---- MODULE Exile ----
(* This model extends the Dropped model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID, status, and oracle. Every actor has a fixed location.  *)
CONSTANT NodeID
VARIABLE nodeStatus, oracle, location

(* Import operators from the Monitors model. *)
M == INSTANCE Monitors

TypeOK == 
  /\ M!TypeOK
  /\ nodeStatus \in [NodeID -> {"up", "down"}] \* Each node is either up or down.
  /\ DOMAIN oracle = NodeID                    \* Each node has an oracle tracking messages.
  /\ \A n \in NodeID : 
    BagToSet(oracle[n].delivered) \subseteq Message /\ 
    BagToSet(oracle[n].dropped) \subseteq Message
  /\ location   \in [ActorName -> NodeID \cup {null}] \* Each actor has a location.
  /\ \A a \in ActorName : actors[a] # null => location[a] # null

Init == M!Init /\
    LET actor == CHOOSE a \in ActorName: actors[a] # null \* The initial actor.
        node  == CHOOSE node \in NodeID: TRUE IN          \* The initial actor's location.
    /\ nodeStatus = [n \in NodeID |-> "up"]               \* Every node is initially "up".
    /\ oracle     = [n \in NodeID |->                     \* No messages have been sent.
                        [delivered |-> EmptyBag, dropped |-> EmptyBag]]
    /\ location   = [a \in ActorName |-> IF a = actor THEN node ELSE null]

-----------------------------------------------------------------------------

NonFaultyNodes == { n \in NodeID : nodeStatus[n] = "up" }
ExiledNodes    == { n \in NodeID : nodeStatus[n] = "down" }
ExiledActors   == { a \in ActorName : location[a] \in ExiledNodes }

-----------------------------------------------------------------------------

Idle       == M!Idle       /\ UNCHANGED <<location,nodeStatus,oracle>>
Deactivate == M!Deactivate /\ UNCHANGED <<location,nodeStatus,oracle>>
Send       == M!Send       /\ UNCHANGED <<location,nodeStatus,oracle>>
Snapshot   == M!Snapshot   /\ UNCHANGED <<location,nodeStatus,oracle>>
Crash      == M!Crash      /\ UNCHANGED <<location,nodeStatus,oracle>>
Monitor    == M!Monitor    /\ UNCHANGED <<location,nodeStatus,oracle>>
Register   == M!Register   /\ UNCHANGED <<location,nodeStatus,oracle>>
Wakeup     == M!Wakeup     /\ UNCHANGED <<location,nodeStatus,oracle>>
Unregister == M!Unregister /\ UNCHANGED <<location,nodeStatus,oracle>>

Drop == \E m \in BagToSet(msgs) : \E node \in NodeID : location[m.target] = node
    /\ msgs' = remove(msgs, m)
    /\ oracle' = [oracle EXCEPT ![node].dropped = put(@, m)]
    /\ UNCHANGED <<actors,snapshots,nodeStatus,location>>

Receive == \E a \in IdleActors : \E m \in msgsTo(a) : \E node \in NodeID : location[m.target] = node
    /\ actors' = [actors EXCEPT 
        ![a].active = @ ++ [c \in m.refs |-> 1],
        ![a].recvCount = @ + 1, 
        ![a].status = "busy"]
    (* Remove m from the msgs bag. *)
    /\ msgs' = remove(msgs, m)
    /\ oracle' = [oracle EXCEPT ![node].delivered = put(@, m)]  \* NEW: Update the oracle.
    /\ UNCHANGED <<snapshots,nodeStatus,location>>

Notify ==
    \* NEW: Monitored actors can be notified about actors on exiled nodes
    \E a \in IdleActors : \E b \in (CrashedActors \union ExiledActors) \intersect M!monitoredBy(a) :
    /\ actors' = [actors EXCEPT ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<msgs,snapshots,nodeStatus,oracle,location>>

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName : \E node \in NonFaultyNodes :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,
        ![b] = [ 
            M!InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1)
        ]]
    /\ location' = [location EXCEPT ![b] = node]  \* NEW: The actor is spawned at a nonfaulty node.
    /\ UNCHANGED <<snapshots,msgs,nodeStatus,oracle>>

(* 
When a node is exiled:
1. All actors located on the node are removed from the configuration.
2. All messages *to or from* the node are removed.
*)
Exile == TRUE

Next == Idle \/ Deactivate \/ Send \/ Receive \/ Snapshot \/ Spawn \/ 
        Crash \/ Monitor \/ Notify \/ Register \/ Wakeup \/ Unregister \/ 
        Drop

-----------------------------------------------------------------------------

Soundness == M!Soundness
Completeness == M!Completeness

====