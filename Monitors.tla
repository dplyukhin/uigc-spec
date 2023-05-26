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
  /\ BagToSet(msgs) \subseteq Message

InitialActorState ==
    D!InitialActorState @@ [
        monitored |-> {},
        isReceptionist |-> FALSE
    ]

monitoredBy(b) == actors[b].monitored
 
Init ==   
    LET actor == CHOOSE a \in ActorName: TRUE 
        state == [ InitialActorState EXCEPT 
                   !.active  = @ ++ (actor :> 1),
                   !.created = @ ++ (<<actor, actor>> :> 1),
                   !.isReceptionist = TRUE
                 ]
    IN
    /\ msgs = EmptyBag
    /\ actors = [a \in ActorName |-> IF a = actor THEN state ELSE null ]
    /\ snapshots = [a \in ActorName |-> null]

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,                                 \* Parent has a reference to the child.
        ![b] = [ 
            InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),                      \* Child has a reference to itself.
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1) \* Child knows about both references.
        ]
        ]
    /\ UNCHANGED <<snapshots,msgs>>

Snapshot == 
    \E a \in IdleActors \union BusyActors \union CrashedActors :
    /\ snapshots[a] = null
    /\ snapshots' = [snapshots EXCEPT ![a] = actors[a]]
    /\ UNCHANGED <<msgs,actors>>

Crash ==
    \E a \in BusyActors :
    /\ actors' = [actors EXCEPT ![a].status = "crashed"]
    /\ UNCHANGED <<msgs,snapshots>>

Monitor ==
    \E a \in BusyActors : \E b \in acqs(a) :
    /\ actors' = [actors EXCEPT ![a].monitored = @ \union {b}]
    /\ UNCHANGED <<msgs,snapshots>>

Notify ==
    \E a \in IdleActors : \E b \in CrashedActors \intersect monitoredBy(a) :
    /\ actors' = [actors EXCEPT ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<msgs,snapshots>>

Register ==
    \E a \in BusyActors \ Receptionists :
    /\ actors' = [actors EXCEPT ![a].isReceptionist = TRUE]
    /\ UNCHANGED <<msgs,snapshots>>

Wakeup ==
    \E a \in IdleActors \intersect Receptionists :
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ UNCHANGED <<msgs,snapshots>>

Unregister ==
    \E a \in BusyActors \intersect Receptionists :
    /\ actors' = [actors EXCEPT ![a].isReceptionist = FALSE]
    /\ UNCHANGED <<msgs,snapshots>>

Next == D!Idle \/ D!Deactivate \/ D!Send \/ D!Receive \/ Snapshot \/ Spawn \/ 
        Crash \/ Monitor \/ Notify \/ Register \/ Wakeup \/ Unregister


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
    /\ (AppearsReceptionist \union D!AppearsUnblocked) \ AppearsCrashed \subseteq S
    /\ \A a \in pdom(snapshots), b \in pdom(snapshots) \ AppearsCrashed :
        /\ (a \in S \intersect D!apparentIAcqs(b) => b \in S)
        /\ (a \in (S \union AppearsCrashed) \intersect appearsMonitoredBy(b) => b \in S)

AppearsQuiescent == pdom(snapshots) \ AppearsPotentiallyUnblocked

Soundness == AppearsQuiescent \subseteq Quiescent

-----------------------------------------------------------------------------

RecentEnough(a, b) ==
    /\ D!RecentEnough(a,b) 
    /\ actors[a].status = "crashed" => snapshots[a].status = "crashed"

(* A set of snapshots is sufficient for b if:
   1. b's snapshot is up to date;
   2. The snapshots of all b's historical inverse acquaintances are recent enough for a;
   3. The snapshots are sufficient for all of b's potential inverse acquaintances.
 *)
SnapshotsInsufficient == 
    CHOOSE S \in SUBSET pdom(actors) : \A a,b \in pdom(actors) :
    /\ (~D!SnapshotUpToDate(a) => a \in S)
    /\ (~RecentEnough(a,b) => b \in S)
    /\ (a \in S /\ a \in piacqs(b) => b \in S)
    /\ (a \in S /\ a \in monitoredBy(b) => b \in S)

SnapshotsSufficient == pdom(actors) \ SnapshotsInsufficient

(* If an actor is garbage and its snapshot is up to date and the snapshots of
   all its historical inverse acquaintances are recent enough and 
 *)
Completeness == (Quiescent \intersect SnapshotsSufficient) \subseteq AppearsQuiescent

====