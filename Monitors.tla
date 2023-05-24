---- MODULE Monitors ----
(* This model extends the Dynamic model with receptionists and monitoring.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Operators from the Dynamic model are imported within the `D' namespace. *)
D == INSTANCE Dynamic

ActorState == [
    status      : {"busy", "idle"},
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

Next == D!Idle \/ D!Deactivate \/ D!Send \/ D!Receive \/ D!Snapshot \/ Spawn

-----------------------------------------------------------------------------

Safety == D!AppearsQuiescent \subseteq Quiescent

====