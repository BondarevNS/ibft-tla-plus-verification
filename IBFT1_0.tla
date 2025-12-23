------------------------------- MODULE IBFT1_0 -------------------------------

(*
 * TLA+ specification of a simplified IBFT 1.0 consensus protocol
 * demonstrating a safety violation (Agreement failure) due to equivocation.
 *
 * Key features:
 *   - N = 4, F = 1 (Byzantine process = {1})
 *   - QUORUM = 3
 *   - Fixed decision values: {"A", "B"}
 *   - Byzantine process 1 sends two conflicting PRE-PREPAREs in view 1
 *   - Correct leaders in views 2 and 3 propose different values ("B" and "A")
 *   - Result: two correct processes decide "A", two decide "B" → Agreement violated
 *
 * This model serves as a counterexample to safety in the original IBFT 1.0
 * under equivocation without additional validation (e.g., view-change justification).
 *
 * Author: N. S. Bondarev, Lomonosov Moscow State University
 *)

EXTENDS Integers, FiniteSets, TLC

(***************************************************************************)
(*                         PROTOCOL PARAMETERS                               *)
(***************************************************************************)

CONSTANTS
    Corr,          \* Set of correct processes (e.g., {2,3,4})
    Byzantine,     \* Set of Byzantine processes (must be exactly one)
    N,             \* Total number of processes (N = |Corr| + |Byzantine|)
    MaxView,       \* Maximum view number (must be ≥ 3 to enable the attack)
    Values         \* Set of possible decision values (fixed to {"A", "B"})

ASSUME
    /\ N = Cardinality(Corr \cup Byzantine)
    /\ N >= 4
    /\ MaxView >= 3
    /\ Byzantine \subseteq (1..N)
    /\ Corr \subseteq (1..N)
    /\ Corr \cap Byzantine = {}
    /\ Cardinality(Byzantine) = 1      \* F = 1 ⇒ QUORUM = 3
    /\ Values = {"A", "B"}             \* Fixed to enable deterministic attack

(***************************************************************************)
(*                         PROTOCOL STATE VARIABLES                          *)
(***************************************************************************)

VARIABLES
    messages,        \* Set of all sent messages (PRE-PREPARE, PREPARE, COMMIT)
    processState,    \* Per-process state: current view number
    decision         \* Final decision per correct process

vars == <<messages, processState, decision>>

(***************************************************************************)
(*                         AUXILIARY DEFINITIONS                             *)
(***************************************************************************)

AllProcs == Corr \cup Byzantine
F        == Cardinality(Byzantine)
QUORUM   == 2 * F + 1  \* = 3 when F = 1

Views == 1..MaxView

(* Leader selection: round-robin over 1..N *)
Leader == [v \in Views |-> ((v - 1) % N) + 1]

NilValue     == "None"
ValuesOrNil  == Values \cup {NilValue}

(* Message structure *)
Message == [type : {"PRE-PREPARE", "PREPARE", "COMMIT"},
            view_num : Views,
            cmd : Values,
            from : AllProcs]

(* Ensures each process sends at most one message per (type, view) *)
BoundedMessages ==
    /\ messages \subseteq Message
    /\ \A p \in AllProcs :
        \A m1, m2 \in messages :
            (m1.type = m2.type /\ m1.view_num = m2.view_num /\ m1.from = p /\ m2.from = p) => m1 = m2

(* Helper to add messages *)
sendMsg(msgs) == messages' = messages \cup msgs

(***************************************************************************)
(*                         PROTOCOL INITIALIZATION                           *)
(***************************************************************************)

Init ==
    /\ messages = {}
    /\ processState = [p \in AllProcs |-> [view_num |-> 1]]
    /\ decision = [p \in Corr |-> NilValue]

(***************************************************************************)
(*                         PROTOCOL ACTIONS                                  *)
(***************************************************************************)

UponPrePrepared(p) ==  \* On receiving a PRE-PREPARE, send PREPARE
    /\ p \in AllProcs
    /\ \E msg \in messages :
        /\ msg.type = "PRE-PREPARE"
        /\ msg.view_num = processState[p].view_num
        /\ msg.from = Leader[processState[p].view_num]
        /\ ~\E m \in messages : m.type = "PREPARE" /\ m.from = p /\ m.view_num = processState[p].view_num
        /\ LET prepare_msg == [type |-> "PREPARE", view_num |-> processState[p].view_num,
                               cmd |-> msg.cmd, from |-> p]
           IN sendMsg({prepare_msg})
    /\ UNCHANGED <<processState, decision>>

UponPrepared(p) ==  \* On collecting a quorum of PREPARE, send COMMIT
    /\ p \in AllProcs
    /\ \E v_num \in Views, c \in Values :
        /\ Cardinality({ msg \in messages :
                msg.type = "PREPARE" /\ msg.view_num = v_num /\ msg.cmd = c }) >= QUORUM
        /\ ~\E m \in messages : m.type = "COMMIT" /\ m.from = p /\ m.view_num = v_num
        /\ LET commit_msg == [type |-> "COMMIT", view_num |-> v_num, cmd |-> c, from |-> p]
           IN sendMsg({commit_msg})
    /\ UNCHANGED <<processState, decision>>

UponCommit(p) ==  \* On collecting a quorum of COMMIT, decide
    /\ p \in Corr
    /\ decision[p] = NilValue
    /\ \E v \in Views, c \in Values :
        /\ Cardinality({ msg \in messages :
                msg.type = "COMMIT" /\ msg.view_num = v /\ msg.cmd = c }) >= QUORUM
        /\ decision' = [decision EXCEPT ![p] = c]
    /\ UNCHANGED <<processState, messages>>

Timeout(p) ==  \* Move to next view (no progress in current view)
    /\ p \in AllProcs
    /\ processState[p].view_num < MaxView
    /\ processState' = [processState EXCEPT ![p].view_num = processState[p].view_num + 1]
    /\ UNCHANGED <<decision, messages>>

ProposeAsLeader(p) ==  \* Correct leader proposes value depending on view
    /\ p \in Corr
    /\ p = Leader[processState[p].view_num]
    /\ ~\E msg \in messages : msg.type = "PRE-PREPARE" /\ msg.view_num = processState[p].view_num /\ msg.from = p
    /\ LET c ==
          CASE processState[p].view_num = 2 -> "B"
             [] processState[p].view_num = 3 -> "A"
             [] OTHER -> "A"  \* fallback
       IN LET pp_msg == [type |-> "PRE-PREPARE", view_num |-> processState[p].view_num,
                         cmd |-> c, from |-> p]
          IN sendMsg({pp_msg})
    /\ UNCHANGED <<processState, decision>>

ByzantineBehavior(p) ==  \* Process 1 performs equivocation in view 1
    /\ p \in Byzantine
    /\ p = 1  \* Only process 1 is the attacker (as assumed)
    /\ messages = {}  \* Attack occurs at the very beginning
    /\ processState[p].view_num = 1
    /\ LET
        msgA == [type |-> "PRE-PREPARE", view_num |-> 1, cmd |-> "A", from |-> 1]
        msgB == [type |-> "PRE-PREPARE", view_num |-> 1, cmd |-> "B", from |-> 1]
       IN sendMsg({msgA, msgB})
    /\ UNCHANGED <<processState, decision>>

(***************************************************************************)
(*                         BEHAVIORAL COMPOSITION                            *)
(***************************************************************************)

Steps(p) ==
    IF p \in Corr THEN
        IF decision[p] = NilValue THEN
            UponPrePrepared(p) \/ UponPrepared(p) \/ UponCommit(p) \/ Timeout(p) \/ ProposeAsLeader(p)
        ELSE
            UNCHANGED vars  \* Terminated processes do nothing
    ELSE
        ByzantineBehavior(p)

Next == \E p \in AllProcs : Steps(p)

Spec == Init /\ [][Next]_vars /\ \A p \in AllProcs : WF_vars(Steps(p))

(***************************************************************************)
(*                         TYPE INVARIANT                                    *)
(***************************************************************************)

TypeOK ==
    /\ processState \in [AllProcs -> [view_num : Views]]
    /\ decision \in [Corr -> ValuesOrNil]
    /\ BoundedMessages

(***************************************************************************)
(*                         SAFETY PROPERTY: AGREEMENT                        *)
(* This property is expected to be VIOLATED in this model                  *)
(***************************************************************************)

Agreement ==
  \A p, q \in Corr :
    (decision[p] /= NilValue /\ decision[q] /= NilValue) => decision[p] = decision[q]

================================================================================
(*
 * Expected Behavior:
 *   - Byzantine process 1 sends both ("A", view=1) and ("B", view=1).
 *   - Half of correct processes prepare/commit "A", half — "B".
 *   - In views 2 and 3, leaders propose "B" and "A" respectively,
 *     reinforcing divergent decisions.
 *   - Final outcome: Agreement is violated.
 *
 * To reproduce:
 *   - Set MaxView = 3
 *   - Run TLC with this specification
 *   - TLC will report a violation of the "Agreement" property.
 *)