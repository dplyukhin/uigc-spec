---- MODULE Exile ----
(* This model extends the Dropped model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID and a status. Every actor has a fixed location. *)
CONSTANT NodeID
VARIABLE droppedMsgs, nodeStatus, location

(* Import operators from the Dropped and Monitors models. *)
D == INSTANCE Dropped WITH droppedMsgs <- droppedMsgs
M == INSTANCE Monitors

TypeOK == 
  /\ D!TypeOK
  /\ location \in [ActorName -> NodeID \cup {null}] \* NEW: Each actor has a location.
  /\ \A a \in ActorName : actors[a] # null => location[a] # null
  /\ nodeStatus \in [NodeID -> {"up", "down"}] \* NEW: Each node is either up or down.

Init == D!Init /\
    LET actor == CHOOSE a \in ActorName: actors[a] # null \* The initial actor.
        node  == CHOOSE node \in NodeID: TRUE IN          \* The initial actor's location.
    /\ location = [a \in ActorName |-> IF a = actor THEN node ELSE null]
    /\ nodeStatus = [n \in NodeID |-> "up"]  \* NEW: Every node is initially "up".

-----------------------------------------------------------------------------

ExiledNodes    == { n \in NodeID : nodeStatus[n] = "down" }
ExiledActors   == { a \in ActorName : location[a] \in ExiledNodes }

-----------------------------------------------------------------------------

Idle       == D!Idle       /\ UNCHANGED <<location,nodeStatus>>
Deactivate == D!Deactivate /\ UNCHANGED <<location,nodeStatus>>
Send       == D!Send       /\ UNCHANGED <<location,nodeStatus>>
Receive    == D!Receive    /\ UNCHANGED <<location,nodeStatus>>
Snapshot   == D!Snapshot   /\ UNCHANGED <<location,nodeStatus>>
Crash      == D!Crash      /\ UNCHANGED <<location,nodeStatus>>
Monitor    == D!Monitor    /\ UNCHANGED <<location,nodeStatus>>
Register   == D!Register   /\ UNCHANGED <<location,nodeStatus>>
Wakeup     == D!Wakeup     /\ UNCHANGED <<location,nodeStatus>>
Unregister == D!Unregister /\ UNCHANGED <<location,nodeStatus>>
Drop       == D!Drop       /\ UNCHANGED <<location,nodeStatus>>

Notify ==
    \* NEW: Monitored actors can be notified about actors on exiled nodes
    \E a \in IdleActors : \E b \in (CrashedActors \union ExiledActors) \intersect M!monitoredBy(a) :
    /\ actors' = [actors EXCEPT ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<msgs,snapshots>>

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName : \E node \in ExiledNodes :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,
        ![b] = [ 
            D!InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1)
        ]]
    /\ location' = [location EXCEPT ![a] = node]  \* NEW: The actor is spawned at a nonfaulty node.
    /\ UNCHANGED <<snapshots,msgs,droppedMsgs,nodeStatus>>

Next == Idle \/ Deactivate \/ Send \/ Receive \/ Snapshot \/ Spawn \/ 
        Crash \/ Monitor \/ Notify \/ Register \/ Wakeup \/ Unregister \/ 
        Drop

-----------------------------------------------------------------------------

Soundness == D!Soundness
Completeness == D!Completeness

====