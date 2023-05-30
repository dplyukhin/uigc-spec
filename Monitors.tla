---- MODULE Monitors ----
(* This model extends the Dynamic model with receptionists and monitoring.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Operators from the Dynamic model are imported within the `D' namespace. *)
D == INSTANCE Dynamic

ActorState == [
    status      : {"busy", "idle", "crashed"}, \* NEW: Actors may become "crashed".
    recvCount   : Nat,
    sendCount   : [ActorName -> Nat],
    active      : [ActorName -> Nat],
    deactivated : [ActorName -> Nat],
    created     : [ActorName \X ActorName -> Nat],
    monitored   : SUBSET ActorName, \* NEW: The set of actors monitored by this one.
    isReceptionist : BOOLEAN        \* NEW: Indicates whether this actor is a receptionist.
]

TypeOK == 
  /\ actors         \in [ActorName -> ActorState \cup {null}]
  /\ snapshots      \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs) \subseteq D!Message

InitialActorState ==
    D!InitialActorState @@ [
        monitored |-> {},
        isReceptionist |-> FALSE
    ]

monitoredBy(b) == actors[b].monitored
 
InitialConfiguration(actor, actorState) ==   
    D!InitialConfiguration(actor, [actorState EXCEPT !.isReceptionist = TRUE])

Idle(a)          == D!Idle(a)
Deactivate(a,b)  == D!Deactivate(a,b)
Send(a,b,m)      == D!Send(a,b,m)
Receive(a,m)     == D!Receive(a,m)
Snapshot(a)      == D!Snapshot(a)
Spawn(a,b,state) == D!Spawn(a,b,state)

Crash(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "crashed"]      \* Mark the actor as crashed.
    /\ msgs'   = removeWhere(msgs, LAMBDA m: m \in msgsTo(a)) \* Messages to crashed actors are dropped.
    /\ UNCHANGED <<snapshots>>

Monitor(a,b) ==
    /\ actors' = [actors EXCEPT ![a].monitored = @ \union {b}] \* Add b to the monitored set.
    /\ UNCHANGED <<msgs,snapshots>>

Notify(a,b) ==
    /\ actors' = [actors EXCEPT  \* Mark the monitor as busy and remove b from the monitored set.
                    ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<msgs,snapshots>>

Register(a) ==
    /\ actors' = [actors EXCEPT ![a].isReceptionist = TRUE]
    /\ UNCHANGED <<msgs,snapshots>>

Wakeup(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ UNCHANGED <<msgs,snapshots>>

Unregister(a) ==
    /\ actors' = [actors EXCEPT ![a].isReceptionist = FALSE]
    /\ UNCHANGED <<msgs,snapshots>>

Init == 
    InitialConfiguration(CHOOSE a \in ActorName: TRUE, InitialActorState)

Next == 
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: Spawn(a,b,InitialActorState)
    \/ \E a \in BusyActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a) \ CrashedActors: \E refs \in SUBSET acqs(a): 
        Send(a,b,[target |-> b, refs |-> refs])
        \* NEW: Messages sent to crashed actors have no effect, so we disallow them.
    \/ \E a \in IdleActors: \E m \in msgsTo(a): Receive(a,m)
    \/ \E a \in IdleActors \union BusyActors \union CrashedActors : Snapshot(a)
        \* NEW: Crashed actors can now take snapshots.
    \/ \E a \in BusyActors: Crash(a)
    \/ \E a \in BusyActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors: \E b \in CrashedActors \intersect monitoredBy(a): Notify(a,b)
    \/ \E a \in BusyActors \ Receptionists: Register(a)
    \/ \E a \in IdleActors \intersect Receptionists : Wakeup(a)
    \/ \E a \in BusyActors \intersect Receptionists : Unregister(a)


-----------------------------------------------------------------------------

(*
Non-crashed receptionists and unblocked actors are not garbage.
Non-crashed actors that are potentially reachable by non-garbage are not garbage.
Non-crashed actors that monitor actors that can crash or have crashed are not garbage.
 *)
PotentiallyUnblocked ==
    CHOOSE S \in SUBSET pdom(actors) :
    /\ (Receptionists \union Unblocked) \ CrashedActors \subseteq S
    /\ \A a \in pdom(actors), b \in pdom(actors) \ CrashedActors :
        /\ (a \in S \intersect piacqs(b) => b \in S)
        /\ (a \in (S \union CrashedActors) \intersect monitoredBy(b) => b \in S)

Quiescent == pdom(actors) \ PotentiallyUnblocked

(* The previous soundness property no longer holds because actors can now become
   busy by receiving signals from crashed actors or messages from external actors. *)
OldSoundness == D!AppearsQuiescent \subseteq Quiescent

AppearsUnblocked == D!AppearsUnblocked
apparentIAcqs(b) == D!apparentIAcqs(b)
appearsMonitoredBy(a) == snapshots[a].monitored
AppearsReceptionist == { a \in pdom(snapshots) : snapshots[a].isReceptionist }
AppearsCrashed == { a \in pdom(snapshots) : snapshots[a].status = "crashed" }
AppearsClosed == D!AppearsClosed \intersect 
                 { b \in pdom(snapshots) : appearsMonitoredBy(b) \subseteq pdom(snapshots) }

(* 
Each clause in this definition corresponds to one in PotentiallyUnblocked---with one
addition: if an actor A has potential inverse acquaintances or monitored actors that 
have not taken a snapshot, then A should be marked as potentially unblocked for safety.
 *)
AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET pdom(snapshots) :
    /\ pdom(snapshots) \ AppearsClosed \subseteq S
    /\ (AppearsReceptionist \union AppearsUnblocked) \ AppearsCrashed \subseteq S
    /\ \A a \in pdom(snapshots), b \in pdom(snapshots) \ AppearsCrashed :
        /\ (a \in S \intersect apparentIAcqs(b) => b \in S)
        /\ (a \in (S \union AppearsCrashed) \intersect appearsMonitoredBy(b) => b \in S)

AppearsQuiescent == pdom(snapshots) \ AppearsPotentiallyUnblocked

Soundness == AppearsQuiescent \subseteq Quiescent

-----------------------------------------------------------------------------

Relevant(a, b) == D!Relevant(a, b) \/ a \in monitoredBy(b)
SnapshotUpToDate(a) == D!SnapshotUpToDate(a)
RecentEnough(a, b) ==
    \/ D!RecentEnough(a,b) 
    \/ (a \in pdom(snapshots) /\ actors[a].status = "crashed" /\ snapshots[a].status = "crashed")

(* A set of snapshots is sufficient for b if:
   1. b's snapshot is up to date;
   2. The snapshots of all b's historical inverse acquaintances are recent enough for a;
   3. The snapshots are sufficient for all of b's potential inverse acquaintances.
 *)
SnapshotsInsufficient == 
    CHOOSE S \in SUBSET pdom(actors):
    /\ \A a \in pdom(actors): 
        /\ ~SnapshotUpToDate(a) => a \in S
        \* For crashed actors, a most recent snapshot suffices.
    /\ \A a \in pdom(actors): \A b \in pdom(actors) \ CrashedActors:
        /\ (Relevant(a,b) /\ ~RecentEnough(a,b) => b \in S)
        /\ (a \in S /\ a \in piacqs(b) => b \in S)
        /\ (a \in S /\ a \in monitoredBy(b) => b \in S)

SnapshotsSufficient == pdom(actors) \ SnapshotsInsufficient

(* If an actor is garbage and its snapshot is up to date and the snapshots of
   all its historical inverse acquaintances are recent enough and 
 *)
Completeness == (Quiescent \intersect SnapshotsSufficient) \subseteq AppearsQuiescent

-----------------------------------------------------------------------------
(* OTHER PROPERTIES: *)

SufficientIsTight == AppearsQuiescent \subseteq SnapshotsSufficient

-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)

GarbageIsDetected == AppearsQuiescent = {}

====