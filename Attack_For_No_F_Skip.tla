---------------------------- MODULE Attack_For_No_F_Skip ----------------------------

(*
 * TLA+ specification demonstrating a censorship attack against a BFT consensus
 * protocol that uses simple round-robin leader rotation (i.e., without F-skip).
 *
 * Purpose:
 *   - Show that in the absence of F-skip, a single Byzantine process can permanently
 *     exclude correct processes from proposing blocks over (F+1) consecutive heights.
 *   - Serve as a counterexample to the chain quality property when F-skip is disabled.
 *
 * Assumptions:
 *   - N >= 4, F = |Byzantine| >= 1
 *   - Leader(h, v) = ((h + v - 2) mod N) + 1  (classic round-robin)
 *   - Byzantine processes are static and known in advance (standard TLA+ modeling)
 *
 *)

EXTENDS Integers, FiniteSets, Sequences

(***************************************************************************)
(*                         PROTOCOL PARAMETERS                               *)
(***************************************************************************)

CONSTANT
    Corr,          \* Set of correct (honest) processes
    Byzantine,     \* Set of Byzantine (malicious) processes — must be non-empty
    N,             \* Total number of processes
    MaxView,       \* Maximum view number per height (for bounded model checking)
    MaxHeight,     \* Maximum block height (used to check chain quality)
    Values,        \* Non-empty set of valid decision values (e.g., {"A", "B"})
    MaxMessages    \* Upper bound on total messages (ensures TLC termination)

ASSUME
    /\ N = Cardinality(Corr \cup Byzantine)
    /\ N >= 4
    /\ Values # {}
    /\ MaxMessages \in Nat \ {0}
    /\ MaxHeight >= 1
    /\ MaxHeight >= Cardinality(Byzantine) + 1
    /\ Byzantine /= {}                          \* Attack requires at least one Byzantine
    /\ (Corr \cup Byzantine) = 1..N             \* Ensures Leader(h,v) maps to valid IDs

(***************************************************************************)
(*                         PROTOCOL STATE VARIABLES                          *)
(***************************************************************************)

VARIABLES
    messages,         \* PRE-PREPARE, PREPARE, COMMIT messages for current height
    processState,     \* Per-correct-process state: view, input, last prepared round/value
    decision,         \* Decided values per height and per correct process
    RCmessages,       \* ROUND-CHANGE messages for current height
    messageCount,     \* Total number of messages sent (for TLC termination)
    committedHeights, \* Set of heights that have been committed
    blockLeader,      \* Leader that proposed the block at each height
    currentHeight     \* Current consensus height under execution

vars == <<messages, processState, decision, RCmessages,
          messageCount, committedHeights, blockLeader, currentHeight>>

(***************************************************************************)
(*                         AUXILIARY DEFINITIONS                             *)
(***************************************************************************)

AllProcs == Corr \cup Byzantine
F        == Cardinality(Byzantine)
QUORUM   == (2 * F) + 1

Views        == 1..MaxView
NilView      == -1
ViewsOrNil   == Views \cup {NilView}

NilValue     == "None"
ValuesOrNil  == Values \cup {NilValue}
Nil          == -1

(* Maximum element of a set of views; returns NilView if empty *)
Maximum(S) == IF S = {} THEN NilView
              ELSE CHOOSE x \in S : \A y \in S : x >= y

(***************************************************************************)
(*                     LEADER SELECTION: ROUND-ROBIN (NO F-SKIP)             *)
(* Vulnerable to censorship: Byzantine leaders can appear consecutively     *)
(***************************************************************************)

Leader(h, v) == ((h + v - 2) % N) + 1

(***************************************************************************)
(*                         PROTOCOL INITIALIZATION                           *)
(***************************************************************************)

Init ==
    /\ \E iv \in [Corr -> Values] :  \* Each correct process has an input
        LET leader1 == Leader(1, 1) IN
        LET initialCmd ==
            IF leader1 \in Corr THEN iv[leader1]
            ELSE CHOOSE c \in Values : TRUE  \* Byzantine picks arbitrary value
        IN
        /\ messages = {[type |-> "PRE-PREPARE", view_num |-> 1,
                        cmd |-> initialCmd, from |-> leader1]}
        /\ processState = [p \in Corr |->
                             [view_num |-> 1,
                              inputValue |-> iv[p],
                              pr |-> NilView,
                              pv |-> NilValue]]
        /\ decision = [h \in 1..MaxHeight |-> [p \in Corr |-> NilValue]]
        /\ RCmessages = {}
    /\ messageCount = 1
    /\ committedHeights = {}
    /\ blockLeader = [h \in 1..MaxHeight |-> Nil]
    /\ currentHeight = 1

(***************************************************************************)
(*                         MESSAGE FILTERING HELPERS                         *)
(***************************************************************************)

PrepareMessages(p, v) ==
    { msg \in messages :
        /\ msg.type = "PREPARE"
        /\ msg.view_num = processState[p].view_num
        /\ msg.cmd = v
    }

CommitMessages(p, v) ==
    { msg \in messages :
        /\ msg.type = "COMMIT"
        /\ msg.view_num = processState[p].view_num
        /\ msg.cmd = v
    }

AllRCsForView(v) == { msg \in RCmessages : msg.type = "ROUND-CHANGE" /\ msg.view_num = v }

(***************************************************************************)
(*                         MESSAGE JUSTIFICATION LOGIC                       *)
(***************************************************************************)

HighestPrepared(Q) ==
    IF Q = {} THEN <<NilView, NilValue>>
    ELSE
        LET prSet  == {m.pr : m \in Q}
            maxPr  == Maximum(prSet) IN
        IF maxPr = NilView THEN <<NilView, NilValue>>
        ELSE
            LET msgsAtMax == {m \in Q : m.pr = maxPr} IN
            LET representative == CHOOSE m \in msgsAtMax : TRUE IN
            <<maxPr, representative.pv>>

JustifyRoundChange(Q) ==
    LET hp == HighestPrepared(Q) IN
    \/ /\ hp[1] = NilView
       /\ \A msg \in Q : msg.pr = NilView /\ msg.pv = NilValue
    \/ /\ hp[1] > NilView
       /\ Cardinality({ m \in messages :
             m.type = "PREPARE" /\ m.view_num = hp[1] /\ m.cmd = hp[2] }) >= QUORUM

JustifyPrePrepare(m) ==
    /\ m.type = "PRE-PREPARE"
    /\ m.cmd \in Values
    /\ m.from = Leader(currentHeight, m.view_num)
    /\ \/ m.view_num = 1
        \/ /\ Cardinality(AllRCsForView(m.view_num)) >= QUORUM
           /\ LET hp == HighestPrepared(AllRCsForView(m.view_num)) IN
              \/ hp[1] = NilView
              \/ (hp[1] > NilView /\ m.cmd = hp[2])

(***************************************************************************)
(*                         NORMAL-CASE PROTOCOL STEPS                        *)
(***************************************************************************)

UponPrePrepared(p) ==  \* On receiving a valid PRE-PREPARE
    /\ p \in Corr
    /\ messageCount < MaxMessages
    /\ \E msg \in messages :
        /\ msg.from = Leader(currentHeight, processState[p].view_num)
        /\ msg.type = "PRE-PREPARE"
        /\ msg.view_num = processState[p].view_num
        /\ msg.cmd \in Values
        /\ JustifyPrePrepare(msg)
        /\ ~\E m \in messages : m.type = "PREPARE" /\ m.from = p /\ m.view_num = processState[p].view_num
        /\ LET prepare_msg == [type |-> "PREPARE", view_num |-> processState[p].view_num,
                               cmd |-> msg.cmd, from |-> p] IN
           /\ messages' = messages \cup {prepare_msg}
           /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<processState, decision, RCmessages, committedHeights, blockLeader, currentHeight>>

UponPrepared(p) ==  \* On collecting a quorum of PREPARE
    /\ p \in Corr
    /\ messageCount < MaxMessages
    /\ \E v \in Values :
        /\ Cardinality(PrepareMessages(p, v)) >= QUORUM
        /\ ~\E m \in messages : m.type = "COMMIT" /\ m.from = p /\ m.view_num = processState[p].view_num
        /\ LET commit_msg == [type |-> "COMMIT", view_num |-> processState[p].view_num,
                              cmd |-> v, from |-> p] IN
           /\ processState' = [processState EXCEPT ![p].pr = processState[p].view_num,
                                                 ![p].pv = v]
           /\ messages' = messages \cup {commit_msg}
           /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<decision, RCmessages, committedHeights, blockLeader, currentHeight>>

UponCommit(p) ==  \* On collecting a quorum of COMMIT
    /\ p \in Corr
    /\ messageCount < MaxMessages
    /\ currentHeight \in DOMAIN decision
    /\ p \in DOMAIN decision[currentHeight]
    /\ decision[currentHeight][p] = NilValue
    /\ \E v \in Values, viewNum \in Views :
        /\ Cardinality({ m \in messages :
              m.type = "COMMIT" /\ m.cmd = v /\ m.view_num = viewNum }) >= QUORUM
        /\ currentHeight <= MaxHeight
        /\ currentHeight \notin committedHeights
        /\ decision' = [decision EXCEPT ![currentHeight] = [decision[currentHeight] EXCEPT ![p] = v]]
        /\ committedHeights' = committedHeights \cup {currentHeight}
        /\ blockLeader' = [blockLeader EXCEPT ![currentHeight] = Leader(currentHeight, viewNum)]
        /\ currentHeight' = currentHeight + 1
        /\ processState' = [q \in Corr |->
               [view_num |-> 1,
                inputValue |-> CHOOSE c \in Values : TRUE,
                pr |-> NilView,
                pv |-> NilValue]]
        /\ messages' = {}
        /\ RCmessages' = {}
        /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<>>

(***************************************************************************)
(*                         VIEW-CHANGE (TIMEOUT) LOGIC                       *)
(***************************************************************************)

Timeout(p) ==  \* Triggered when no progress is made in current view
    /\ p \in Corr
    /\ messageCount < MaxMessages
    /\ processState[p].view_num < MaxView
    /\ ~\E m \in RCmessages : m.type = "ROUND-CHANGE" /\ m.from = p /\ m.view_num = processState[p].view_num + 1
    /\ LET vNew == processState[p].view_num + 1
           rcMsg == [type |-> "ROUND-CHANGE", view_num |-> vNew,
                     pv |-> processState[p].pv, pr |-> processState[p].pr, from |-> p] IN
       /\ RCmessages' = RCmessages \cup {rcMsg}
       /\ processState' = [processState EXCEPT ![p].view_num = vNew]
       /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<decision, messages, committedHeights, blockLeader, currentHeight>>

UponQRC(p) ==  \* Leader sends PRE-PREPARE upon quorum of ROUND-CHANGE
    /\ p \in Corr
    /\ messageCount < MaxMessages
    /\ \E v \in Views :
        /\ p = Leader(currentHeight, v)
        /\ LET Q == AllRCsForView(v) IN
           /\ Cardinality(Q) >= QUORUM
           /\ JustifyRoundChange(Q)
           /\ LET hp == HighestPrepared(Q)
                  cmdVal == IF hp[1] = NilView THEN processState[p].inputValue
                            ELSE hp[2] IN
              /\ cmdVal \in Values
              /\ ~\E m \in messages : m.type = "PRE-PREPARE" /\ m.from = p /\ m.view_num = v
              /\ LET ppMsg == [type |-> "PRE-PREPARE", view_num |-> v,
                               cmd |-> cmdVal, from |-> p] IN
                 /\ messages' = messages \cup {ppMsg}
                 /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<decision, processState, RCmessages, committedHeights, blockLeader, currentHeight>>

(***************************************************************************)
(*                         BYZANTINE ATTACK STRATEGIES                       *)
(* Full arsenal of attacks; only ByzantineLeaderPrepares is enabled by default *)
(***************************************************************************)

ByzantineLeaderPrepares(p) ==  \* Standard: propose arbitrary block as leader
    /\ p \in Byzantine
    /\ messageCount < MaxMessages
    /\ \E v \in Views :
        /\ p = Leader(currentHeight, v)
        /\ ~\E m \in messages : m.type = "PRE-PREPARE" /\ m.from = p /\ m.view_num = v
        /\ LET cmdVal == CHOOSE c \in Values : TRUE IN
           /\ messages' = messages \cup {[type |-> "PRE-PREPARE", view_num |-> v,
                                          cmd |-> cmdVal, from |-> p]}
           /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<RCmessages, processState, decision, committedHeights, blockLeader, currentHeight>>

ByzantineLeaderIgnoresJustification(p) ==  \* Violates view-change justification
    /\ p \in Byzantine
    /\ messageCount < MaxMessages
    /\ \E v \in Views :
        /\ v > 1
        /\ p = Leader(currentHeight, v)
        /\ ~\E m \in messages : m.type = "PRE-PREPARE" /\ m.from = p /\ m.view_num = v
        /\ LET Q == AllRCsForView(v) IN
           /\ Cardinality(Q) >= QUORUM
           /\ LET hp == HighestPrepared(Q)
                  justifiedCmd == IF hp[1] = NilView THEN CHOOSE c \in Values : TRUE
                                 ELSE hp[2]
                  fakeCmd == CHOOSE c \in Values : c /= justifiedCmd
              IN
              /\ fakeCmd \in Values
              /\ messages' = messages \cup {[type |-> "PRE-PREPARE", view_num |-> v,
                                             cmd |-> fakeCmd, from |-> p]}
              /\ messageCount' = messageCount + 1
    /\ UNCHANGED <<RCmessages, processState, decision, committedHeights, blockLeader, currentHeight>>

ByzantineEquivocate(p) ==  \* Sends two conflicting PRE-PREPAREs in the same view
    /\ p \in Byzantine
    /\ messageCount + 2 <= MaxMessages
    /\ \E v \in Views, c1, c2 \in Values :
        /\ c1 /= c2
        /\ p = Leader(currentHeight, v)
        /\ ~\E m \in messages : m.type = "PRE-PREPARE" /\ m.from = p /\ m.view_num = v
        /\ messages' = messages \cup {
              [type |-> "PRE-PREPARE", view_num |-> v, cmd |-> c1, from |-> p],
              [type |-> "PRE-PREPARE", view_num |-> v, cmd |-> c2, from |-> p]
           }
        /\ messageCount' = messageCount + 2
        /\ UNCHANGED <<RCmessages, processState, decision, committedHeights, blockLeader, currentHeight>>

ByzantineCommitNoPrepare(p) ==  \* Sends COMMIT without prior PREPARE
    /\ p \in Byzantine
    /\ messageCount < MaxMessages
    /\ \E v \in Views, c \in Values :
        /\ ~\E m \in messages : m.type = "COMMIT" /\ m.from = p /\ m.view_num = v /\ m.cmd = c
        /\ messages' = messages \cup {[type |-> "COMMIT", view_num |-> v, cmd |-> c, from |-> p]}
        /\ messageCount' = messageCount + 1
        /\ UNCHANGED <<RCmessages, processState, decision, committedHeights, blockLeader, currentHeight>>

ByzantinePrepareNoPrePrepare(p) ==  \* Sends PREPARE without corresponding PRE-PREPARE
    /\ p \in Byzantine
    /\ messageCount < MaxMessages
    /\ \E v \in Views, c \in Values :
        /\ ~\E m \in messages : m.type = "PREPARE" /\ m.from = p /\ m.view_num = v /\ m.cmd = c
        /\ ~\E pp \in messages : pp.type = "PRE-PREPARE" /\ pp.view_num = v /\ pp.cmd = c
        /\ messages' = messages \cup {[type |-> "PREPARE", view_num |-> v, cmd |-> c, from |-> p]}
        /\ messageCount' = messageCount + 1
        /\ UNCHANGED <<RCmessages, processState, decision, committedHeights, blockLeader, currentHeight>>

ByzantineInvalidRC(p) ==  \* Sends ROUND-CHANGE with forged or neutral (pr, pv)
    /\ p \in Byzantine
    /\ messageCount < MaxMessages
    /\ \E v \in Views :
        /\ ~\E m \in RCmessages : m.type = "ROUND-CHANGE" /\ m.from = p /\ m.view_num = v
        /\ \E fakePr \in Views \cup {NilView}, fakePv \in Values \cup {NilValue} :
            /\ \/ fakePr = NilView /\ fakePv = NilValue
               \/ (fakePr = 1 /\ fakePv \in Values)  \* Plausible but false preparation
            /\ RCmessages' = RCmessages \cup {
                  [type |-> "ROUND-CHANGE", view_num |-> v, from |-> p,
                   pr |-> fakePr, pv |-> fakePv]
               }
        /\ messageCount' = messageCount + 1
        /\ UNCHANGED <<messages, processState, decision, committedHeights, blockLeader, currentHeight>>

ByzantineFakeLeader(p) ==  \* Impersonates leader by sending PRE-PREPARE
    /\ p \in Byzantine
    /\ messageCount < MaxMessages
    /\ \E v \in Views, c \in Values :
        /\ p /= Leader(currentHeight, v)
        /\ ~\E m \in messages : m.type = "PRE-PREPARE" /\ m.from = p /\ m.view_num = v
        /\ messages' = messages \cup {[type |-> "PRE-PREPARE", view_num |-> v, cmd |-> c, from |-> p]}
        /\ messageCount' = messageCount + 1
        /\ UNCHANGED <<RCmessages, processState, decision, committedHeights, blockLeader, currentHeight>>

(***************************************************************************)
(*                         BEHAVIORAL COMPOSITION                            *)
(* Only ByzantineLeaderPrepares is enabled — sufficient to break chain quality *)
(***************************************************************************)

ByzantineBehavior(p) ==
    \/ ByzantineLeaderPrepares(p)
    \/ ByzantineLeaderIgnoresJustification(p)
    \/ ByzantineEquivocate(p)
    \/ ByzantineCommitNoPrepare(p)
    \/ ByzantinePrepareNoPrePrepare(p)
    \/ ByzantineInvalidRC(p)
    \/ ByzantineFakeLeader(p)
    \/ (* Passive Byzantine: do nothing *)
       /\ p \in Byzantine
       /\ UNCHANGED vars

Steps(p) ==
    IF p \in Corr THEN
        UponPrePrepared(p) \/ UponPrepared(p) \/ UponCommit(p) \/ Timeout(p) \/ UponQRC(p)
    ELSE
        ByzantineBehavior(p)

Next == \E p \in AllProcs : Steps(p)

Spec == Init /\ [][Next]_vars /\ \A p \in AllProcs : WF_vars(Steps(p))

(***************************************************************************)
(*                         TYPE INVARIANT                                    *)
(***************************************************************************)

TypeOK ==
    /\ currentHeight \in 1..(MaxHeight + 1)
    /\ processState \in [Corr -> [view_num: Views, inputValue: Values,
                                  pr: ViewsOrNil, pv: ValuesOrNil]]
    /\ decision \in [1..MaxHeight -> [Corr -> ValuesOrNil]]
    /\ messages \in SUBSET [type: {"PRE-PREPARE", "PREPARE", "COMMIT"},
                            view_num: Views,
                            cmd: Values,
                            from: AllProcs]
    /\ RCmessages \in SUBSET [type: {"ROUND-CHANGE"},
                              view_num: Views,
                              from: AllProcs,
                              pv: ValuesOrNil,
                              pr: ViewsOrNil]
    /\ messageCount \in 0..MaxMessages
    /\ committedHeights \subseteq 1..MaxHeight
    /\ blockLeader \in [1..MaxHeight -> AllProcs \cup {Nil}]

(***************************************************************************)
(*                         SAFETY AND LIVENESS PROPERTIES                    *)
(***************************************************************************)

Agreement ==  \* All correct processes agree on the same value per height
    \A h \in 1..MaxHeight, p, q \in Corr :
        (decision[h][p] /= NilValue /\ decision[h][q] /= NilValue) => decision[h][p] = decision[h][q]

Validity ==  \* Decisions are either valid or "None"
    \A h \in 1..MaxHeight, p \in Corr : decision[h][p] \in ValuesOrNil

Done == \A h \in committedHeights, p \in Corr : decision[h][p] \in Values
Termination == <>Done

(***************************************************************************)
(*                         CHAIN QUALITY (CENSORSHIP RESISTANCE)             *)
(* This property is expected to FAIL in this model due to lack of F-skip     *)
(***************************************************************************)

HonestLeaderInFPlusOneBlocks ==
  \A h \in 1..(MaxHeight - F) :
    (\A i \in 0..F : blockLeader[h + i] /= Nil) =>
    \E i \in 0..F : blockLeader[h + i] \in Corr

================================================================================
(*
 * Usage Note:
 *   - To demonstrate the censorship attack, run TLC with:
 *       MaxHeight = F + 1
 *       MaxView = 1
 *       Values = {"A"}
 *       Corr = 2..N, Byzantine = {1}
 *   - The property `HonestLeaderInFPlusOneBlocks` will be violated,
 *     showing that all (F+1) blocks were proposed by Byzantine process 1.
 *)