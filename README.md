# IBFT Formal Verification Artifacts

This repository contains the TLA+ specifications and TLC configurations used in the formal verification study of the IBFT consensus protocol and its variants.

## Repository Structure

The repository is organized by protocol variant. Each directory contains:
- TLA+ model of the protocol variant.
- One or more TLC configuration files used for verification of safety, liveness, and censorship resistance properties.
- TLC-generated counterexample trace for properties that are violated (if exists).

## Tooling

All models are written in **TLA+** and were verified using the **TLC model checker** (TLA+ Toolbox or TLA+ VSCode Extension).

Each configuration file corresponds to a specific verification task (e.g., Agreement, Termination, or censorship resistance) with bounded parameters.