---- MODULE Exile ----
(* This model extends the Dropped model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID, status, and oracle. Every actor has a fixed location.  *)
CONSTANT NodeID
VARIABLE droppedMsgs, nodeStatus, oracle, location

(* Import operators from the Dropped and Monitors models. *)
D == INSTANCE Dropped WITH droppedMsgs <- droppedMsgs
M == INSTANCE Monitors

TypeOK == 
  /\ D!TypeOK
  /\ nodeStatus \in [NodeID -> {"up", "down"}] \* Each node is either up or down.
  /\ oracle     \in [NodeID ->                 \* Each node has an oracle tracking messages.
                        [delivered: Bag(Message), dropped: Bag(Message)]]
  /\ location   \in [ActorName -> NodeID \cup {null}] \* Each actor has a location.
  /\ \A a \in ActorName : actors[a] # null => location[a] # null

Init == D!Init /\
    LET actor == CHOOSE a \in ActorName: actors[a] # null \* The initial actor.
        node  == CHOOSE node \in NodeID: TRUE IN          \* The initial actor's location.
    /\ nodeStatus = [n \in NodeID |-> "up"]               \* Every node is initially "up".
    /\ oracle     = [n \in NodeID |->                     \* No messages have been sent.
                        [delivered: EmptyBag, dropped: EmptyBag]]
    /\ location   = [a \in ActorName |-> IF a = actor THEN node ELSE null]

-----------------------------------------------------------------------------

NonFaultyNodes == { n \in NodeID : nodeStatus[n] = "up" }
ExiledNodes    == { n \in NodeID : nodeStatus[n] = "down" }
ExiledActors   == { a \in ActorName : location[a] \in ExiledNodes }

-----------------------------------------------------------------------------

Idle       == D!Idle       /\ UNCHANGED <<location,nodeStatus,oracle>>
Deactivate == D!Deactivate /\ UNCHANGED <<location,nodeStatus,oracle>>
Send       == D!Send       /\ UNCHANGED <<location,nodeStatus,oracle>>
Snapshot   == D!Snapshot   /\ UNCHANGED <<location,nodeStatus,oracle>>
Crash      == D!Crash      /\ UNCHANGED <<location,nodeStatus,oracle>>
Monitor    == D!Monitor    /\ UNCHANGED <<location,nodeStatus,oracle>>
Register   == D!Register   /\ UNCHANGED <<location,nodeStatus,oracle>>
Wakeup     == D!Wakeup     /\ UNCHANGED <<location,nodeStatus,oracle>>
Unregister == D!Unregister /\ UNCHANGED <<location,nodeStatus,oracle>>


Drop == ???
Receive == ???

Notify ==
    \* NEW: Monitored actors can be notified about actors on exiled nodes
    \E a \in IdleActors : \E b \in (CrashedActors \union ExiledActors) \intersect M!monitoredBy(a) :
    /\ actors' = [actors EXCEPT ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<msgs,snapshots,droppedMsgs,nodeStatus,oracle,location>>

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName : \E node \in NonFaultyNodes :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,
        ![b] = [ 
            D!InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1)
        ]]
    /\ location' = [location EXCEPT ![b] = node]  \* NEW: The actor is spawned at a nonfaulty node.
    /\ UNCHANGED <<snapshots,msgs,droppedMsgs,nodeStatus>>

(* 
When a node is exiled:
1. All actors located on the node are removed from the configuration.
2. All messages sent from the node are removed.
*)
Exile == TRUE

Next == Idle \/ Deactivate \/ Send \/ Receive \/ Snapshot \/ Spawn \/ 
        Crash \/ Monitor \/ Notify \/ Register \/ Wakeup \/ Unregister \/ 
        Drop

-----------------------------------------------------------------------------

Soundness == D!Soundness
Completeness == D!Completeness

====