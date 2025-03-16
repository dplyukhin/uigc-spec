This repository hosts TLA+ specifications for the paper "CRGC: Fault-Recovering
Actor Garbage Collection in Pekko".

# Quick Start

Ensure you have Java (version 11 or higher) already installed and a copy
of `tla2tools.jar` in the root directory of this repository. To quickly 
model check all the specifications up to bounded depth, run the command:

```bash
./check.sh
```

The command should finish running in less than a minute.  Errors and 
other information will be written to the `logs/` directory.

If you also have `pdflatex` installed, you can generate pretty PDF
versions of the specifications. Run the command:

```bash
./format.sh
```

The PDFs will be written to the `tex` directory.

# Overview

TLA+ specifications are in the `spec/` directory. Configuration files
for model checking are in the `config/` directory.

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