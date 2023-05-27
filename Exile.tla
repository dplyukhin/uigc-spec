---- MODULE Exile ----
(* This model extends the Dropped model with faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID and a status. *)
CONSTANT NodeID
VARIABLE droppedMsgs, nodeStatus

(* Operators from the Dropped model are imported within the `D' namespace. *)
D == INSTANCE Dropped WITH droppedMsgs <- droppedMsgs

ActorState == [
    status         : {"busy", "idle", "crashed"},
    recvCount      : Nat,
    sendCount      : [ActorName -> Nat],
    active         : [ActorName -> Nat],
    deactivated    : [ActorName -> Nat],
    created        : [ActorName \X ActorName -> Nat],
    monitored      : SUBSET ActorName,
    isReceptionist : BOOLEAN,
    location       : NodeID   \* NEW: Actors are located on nodes.
]

TypeOK == 
  /\ actors \in [ActorName -> ActorState \cup {null}]
  /\ snapshots \in [ActorName -> ActorState \cup {null}]
  /\ nodeStatus \in [NodeID -> {"up", "down"}] \* NEW: Each node is either up or down.
  /\ BagToSet(msgs) \subseteq Message
  /\ BagToSet(droppedMsgs) \subseteq Message

Init ==   
    LET actor == CHOOSE a \in ActorName: TRUE 
        state == [ D!InitialActorState EXCEPT 
                   !.active  = @ ++ (actor :> 1),
                   !.created = @ ++ (<<actor, actor>> :> 1),
                   !.isReceptionist = TRUE
                   \* NEW: Choose an arbitrary node for the initial actor's location.
                 ] @@ ("location" :> CHOOSE node \in NodeID: TRUE)
    IN
    /\ msgs = EmptyBag
    /\ actors = [a \in ActorName |-> IF a = actor THEN state ELSE null ]
    /\ snapshots = [a \in ActorName |-> null]
    /\ droppedMsgs = EmptyBag
    /\ nodeStatus = [n \in NodeID |-> "up"]  \* NEW: Every node is initially "up".

-----------------------------------------------------------------------------

NonFaultyNode = { n \in NodeID : nodeStatus[n] = "up" }
FaultyNode    = { n \in NodeID : nodeStatus[n] = "down" }

-----------------------------------------------------------------------------

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName : \E node \in NonFaultyNode :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,
        ![b] = [ 
            D!InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1)
        ] @@ ("location" :> node)  \* NEW: The child may be spawned on any nonfaulty node.
        ]
    /\ UNCHANGED <<snapshots,msgs,droppedMsgs,nodeStatus>>

Next == D!Next /\ UNCHANGED <<nodeStatus>>

-----------------------------------------------------------------------------

Soundness == D!Soundness
Completeness == D!Completeness

====