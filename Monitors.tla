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
        isReceptionist |-> TRUE
    ]
 
Init ==   
    LET actor == CHOOSE a \in ActorName: TRUE 
        state == [ InitialActorState EXCEPT 
                   !.active  = @ ++ (actor :> 1),
                   !.created = @ ++ (<<actor, actor>> :> 1)
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

Crash ==
    \E a \in BusyActors :
    /\ actors' = [actors EXCEPT ![a].status = "crashed"]
    /\ UNCHANGED <<msgs,snapshots>>

Monitor ==
    \E a \in BusyActors : \E b \in acqs(a) :
    /\ actors' = [actors EXCEPT ![a].monitored = @ \union {b}]
    /\ UNCHANGED <<msgs,snapshots>>

Notify ==
    \E a \in IdleActors : \E b \in CrashedActors :
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

Next == D!Idle \/ D!Deactivate \/ D!Send \/ D!Receive \/ D!Snapshot \/ 
        Spawn \/ Crash \/ Monitor \/ Notify \/ Register \/ Wakeup \/ Unregister


-----------------------------------------------------------------------------

(* The previous safety property no longer holds because actors can now become
   busy by receiving signals from crashed actors or messages from external actors. *)
OldSafety == D!AppearsQuiescent \subseteq Quiescent

appearsMonitoredBy(a) == snapshots[a].monitored
AppearsReceptionist == { a \in pdom(snapshots) : ~snapshots[a].isReceptionist }

AppearsPotentiallyUnblocked == CHOOSE S \in SUBSET pdom(snapshots) : 
    /\ \A a \in pdom(snapshots) \ AppearsBlocked : a \in S
    /\ \A a \in S, b \in pdom(snapshots) : a \in apparentIAcqs(b) => b \in S

AppearsQuiescent == pdom(snapshots) \ AppearsPotentiallyUnblocked

AppearsQuiescent == 
    LET RECURSIVE actorAppearsQuiescent(_)
        actorAppearsQuiescent(b) ==
            /\ ~snapshots[b].isReceptionist
            /\ b \in D!AppearsBlocked
            /\ \A a \in (D!apparentIAcqs(b) \union snapshots[b].monitored) \ {b} : 
                /\ a \in pdom(snapshots)
                /\ actorAppearsQuiescent(a)
    IN { a \in pdom(snapshots) : actorAppearsQuiescent(a) }

Safety == AppearsQuiescent \subseteq Quiescent

====