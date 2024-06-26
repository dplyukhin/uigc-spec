---- MODULE Monitors ----
(* This model extends the Dynamic model with sticky actors and monitoring.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Operators from the Dynamic model are imported within the `D' namespace. *)
D == INSTANCE Dynamic

ActorState == [
    status      : {"busy", "idle", "halted"}, \* NEW: Actors may become "halted".
    received    : Nat,
    sent        : [ActorName -> Nat],
    active      : [ActorName -> Nat],
    deactivated : [ActorName -> Nat],
    created     : [ActorName \X ActorName -> Nat],
    monitored   : SUBSET ActorName, \* NEW: The set of actors monitored by this one.
    isSticky    : BOOLEAN           \* NEW: Indicates whether this actor is a sticky actor.
]

TypeOK == 
  /\ actors         \in [ActorName -> ActorState \cup {null}]
  /\ snapshots      \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs) \subseteq D!Message

InitialActorState ==
    D!InitialActorState @@ [
        monitored |-> {},
        isSticky |-> FALSE
    ]

InitialConfiguration(actor, actorState) ==   
    D!InitialConfiguration(actor, [actorState EXCEPT !.isSticky = TRUE])

-----------------------------------------------------------------------------
(* DEFINITIONS *)

msgsTo(a)             == D!msgsTo(a)
acqs(a)               == D!acqs(a)
iacqs(b)              == D!iacqs(b)
pacqs(a)              == D!pacqs(a)
piacqs(b)             == D!piacqs(b)
pastAcqs(a)           == D!pastAcqs(a)
pastIAcqs(b)          == D!pastIAcqs(b)
monitoredBy(b)        == actors[b].monitored
appearsMonitoredBy(a) == snapshots[a].monitored

BusyActors    == D!BusyActors
IdleActors    == D!IdleActors
Blocked       == D!Blocked
Unblocked     == D!Unblocked
HaltedActors  == { a \in Actors    : actors[a].status = "halted" }
AppearsHalted == { a \in Snapshots : snapshots[a].status = "halted" }
StickyActors  == { a \in Actors    : actors[a].isSticky }
AppearsSticky == { a \in Snapshots : snapshots[a].isSticky }

-----------------------------------------------------------------------------
(* TRANSITIONS *)

Idle(a)          == D!Idle(a)
Deactivate(a,b)  == D!Deactivate(a,b)
Send(a,b,m)      == D!Send(a,b,m)
Receive(a,m)     == D!Receive(a,m)
Snapshot(a)      == D!Snapshot(a)
Spawn(a,b,state) == D!Spawn(a,b,state)

Halt(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "halted"]      \* Mark the actor as halted.
    /\ UNCHANGED <<msgs,snapshots>>

Monitor(a,b) ==
    /\ actors' = [actors EXCEPT ![a].monitored = @ \union {b}] \* Add b to the monitored set.
    /\ UNCHANGED <<msgs,snapshots>>

Notify(a,b) ==
    /\ actors' = [actors EXCEPT  \* Mark the monitor as busy and remove b from the monitored set.
                    ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<msgs,snapshots>>

Unmonitor(a,b) ==
    /\ actors' = [actors EXCEPT ![a].monitored = @ \ {b}] \* Remove b from the monitored set.
    /\ UNCHANGED <<msgs,snapshots>>

Register(a) ==
    /\ actors' = [actors EXCEPT ![a].isSticky = TRUE]
    /\ UNCHANGED <<msgs,snapshots>>

Wakeup(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ UNCHANGED <<msgs,snapshots>>

Unregister(a) ==
    /\ actors' = [actors EXCEPT ![a].isSticky = FALSE]
    /\ UNCHANGED <<msgs,snapshots>>

Init == 
    InitialConfiguration(CHOOSE a \in ActorName: TRUE, InitialActorState)

Next == 
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: Spawn(a,b,InitialActorState)
    \/ \E a \in BusyActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[target |-> b, refs |-> refs])
    \/ \E a \in IdleActors: \E m \in msgsTo(a): Receive(a,m)
    \/ \E a \in IdleActors \union BusyActors \union HaltedActors : Snapshot(a)
        \* NEW: Halted actors can now take snapshots.
    \/ \E a \in BusyActors: Halt(a)
    \/ \E a \in BusyActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors: \E b \in HaltedActors \intersect monitoredBy(a): Notify(a,b)
    \/ \E a \in BusyActors: \E b \in monitoredBy(a): Unmonitor(a,b)
    \/ \E a \in BusyActors \ StickyActors: Register(a)
    \/ \E a \in IdleActors \intersect StickyActors : Wakeup(a)
    \/ \E a \in BusyActors \intersect StickyActors : Unregister(a)


-----------------------------------------------------------------------------

(*
Non-halted sticky actors and unblocked actors are not garbage.
Non-halted actors that are potentially reachable by non-garbage are not garbage.
Non-halted actors that monitor actors that can halt or have halted are not garbage.
 *)
PotentiallyUnblocked ==
    CHOOSE S \in SUBSET Actors :
    /\ (StickyActors \union Unblocked) \ HaltedActors \subseteq S
    /\ \A a \in Actors, b \in Actors \ HaltedActors :
        /\ (a \in S \intersect piacqs(b) => b \in S)
        /\ (a \in (S \union HaltedActors) \intersect monitoredBy(b) => b \in S)

Quiescent == Actors \ PotentiallyUnblocked

AppearsUnblocked == D!AppearsUnblocked
apparentIAcqs(b) == D!apparentIAcqs(b)
AppearsClosed == D!AppearsClosed \intersect 
                 { b \in Snapshots : appearsMonitoredBy(b) \subseteq Snapshots }

(* 
Each clause in this definition corresponds to one in PotentiallyUnblocked---with one
addition: if an actor A has potential inverse acquaintances or monitored actors that 
have not taken a snapshot, then A should be marked as potentially unblocked for safety.
 *)
AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET Snapshots :
    /\ Snapshots \ (AppearsClosed \union AppearsHalted) \subseteq S
    /\ (AppearsSticky \union AppearsUnblocked) \ AppearsHalted \subseteq S
    /\ \A a \in Snapshots, b \in Snapshots \ AppearsHalted :
        /\ (a \in S \intersect apparentIAcqs(b) => b \in S)
        /\ (a \in (S \union AppearsHalted) \intersect appearsMonitoredBy(b) => b \in S)

AppearsQuiescent == Snapshots \ AppearsPotentiallyUnblocked

-----------------------------------------------------------------------------

SnapshotUpToDate(a) == D!SnapshotUpToDate(a)
RecentEnough(a,b) == D!RecentEnough(a,b)

SnapshotsInsufficient == 
    CHOOSE S \in SUBSET Actors : \A a \in Actors :
    /\ (~SnapshotUpToDate(a) => a \in S)
    /\ \A b \in Actors \ HaltedActors :
        /\ (a \in pastIAcqs(b) /\ ~RecentEnough(a,b) => b \in S)
        /\ (a \in S /\ a \in piacqs(b) => b \in S)
        /\ (a \in S /\ a \in monitoredBy(b) => b \in S) \* NEW

SnapshotsSufficient == Actors \ SnapshotsInsufficient

Spec == (Quiescent \intersect SnapshotsSufficient) = AppearsQuiescent

-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)

(* This invariant fails, showing that the set of quiescent actors is nonempty. *)
GarbageExists == ~(Quiescent = {})

(* This invariant fails, showing that quiescence can be detected and that it
   is possible to obtain a sufficient set of snapshots. *)
GarbageIsDetected == ~(AppearsQuiescent = {})

(* This invariant fails, showing that quiescent actors can have halted inverse
   acquaintances. *)
HaltedGarbageIsDetected ==
  ~(\E a,b \in Actors: a # b /\ a \in HaltedActors /\ b \in AppearsQuiescent /\ 
    a \in iacqs(b))

(* The previous soundness property no longer holds because actors can now become
   busy by receiving signals from halted actors or messages from external actors. *)
OldSoundness == D!AppearsQuiescent \subseteq Quiescent

(* The previous completeness property no longer holds because snapshots from
   monitored actors need to be up to date. *)
OldCompleteness == (Quiescent \intersect D!SnapshotsSufficient) \subseteq AppearsQuiescent

====