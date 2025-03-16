This repository hosts TLA+ specifications for the paper "CRGC: Fault-Recovering
Actor Garbage Collection in Pekko".

# Overview

`FaultModel.tla` formalizes our model of a distributed actor system.
Actors can monitor each other for failure, messages can be dropped,
and nodes can "shun" one another and become "exiled". This model
corresponds to Section 3 of the paper.

Our model for CRGC is composed of several specifications of 
increasing complexity:

1. `Dynamic.tla` is the "core" part of CRGC, ignoring faults and sticky
   actors and monitoring. This model is similar to (Plyukhin and Agha, 
   LMCS 2022) and to (Clebsch and Drossopoulou, OOPSLA 2013).
2. `Monitors.tla` adds support for sticky actors and monitoring.
3. `Exile.tla` adds support for fault recovery. 
4. `Shadows.tla` and `UndoLogs.tla` define shadow graphs and undo logs.

`Exile.tla` corresponds to Section 4.1 of the paper. `Shadows.tla` and
`UndoLogs.tla` correspond to Section 4.2 of the paper.

# Model checking

TLC (the TLA+ model checker) performs a breadth-first exhaustive search 
by default. Unfortunately, the models in this repository are unbounded and 
grow quickly as the search depth increases. Many bugs require ~10 steps to 
manifest---a depth that is already infeasible to search exhaustively. However,
random simulation is sufficient for finding most bugs within a few
minutes.

To search exhaustively up to depth N, pass the option `-dfid N` to TLC.

To simulate executions up to depth N, pass the option `-simulate -depth N`.
The depth defaults to 100.