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

Idle(a)         == M!Idle(a)         /\ UNCHANGED <<location,nodeStatus,oracle>>
Deactivate(a,b) == M!Deactivate(a,b) /\ UNCHANGED <<location,nodeStatus,oracle>>
Send(a,b,m)     == M!Send(a,b,m)     /\ UNCHANGED <<location,nodeStatus,oracle>>
Snapshot(a)     == M!Snapshot(a)     /\ UNCHANGED <<location,nodeStatus,oracle>>
Crash(a)        == M!Crash(a)        /\ UNCHANGED <<location,nodeStatus,oracle>>
Monitor(a,b)    == M!Monitor(a,b)    /\ UNCHANGED <<location,nodeStatus,oracle>>
Notify(a,b)     == M!Notify(a,b)     /\ UNCHANGED <<location,nodeStatus,oracle>>
Register(a)     == M!Register(a)     /\ UNCHANGED <<location,nodeStatus,oracle>>
Wakeup(a)       == M!Wakeup(a)       /\ UNCHANGED <<location,nodeStatus,oracle>>
Unregister(a)   == M!Unregister(a)   /\ UNCHANGED <<location,nodeStatus,oracle>>

Drop(m) == 
    LET node == location[m.target] IN
    /\ msgs' = remove(msgs, m)
    /\ oracle' = [oracle EXCEPT ![node].dropped = put(@, m)]
    /\ UNCHANGED <<actors,snapshots,nodeStatus,location>>

Receive(a,m) == M!Receive(a,m) /\
    LET node == location[a] IN
    /\ oracle' = [oracle EXCEPT ![node].delivered = put(@, m)]
    /\ UNCHANGED <<nodeStatus,location>>

Spawn(a,b,node) == M!Spawn(a,b) /\
    /\ location' = [location EXCEPT ![b] = node]
    /\ UNCHANGED <<nodeStatus,oracle>>

(* 
When a node is exiled:
1. All actors located on the node are removed from the configuration.
2. All messages *to or from* the node are removed.
*)
Exile == TRUE

Next ==
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: \E n \in NonFaultyNodes: Spawn(a,b,n)
        \* NEW: Actors are spawned onto a specific node
    \/ \E a \in BusyActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[target |-> b, refs |-> refs])
    \/ \E a \in IdleActors: \E m \in msgsTo(a): Receive(a,m)
    \/ \E a \in IdleActors \union BusyActors \union CrashedActors: Snapshot(a)
    \/ \E a \in BusyActors: Crash(a)
    \/ \E a \in BusyActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors: \E b \in (CrashedActors \union ExiledActors) \intersect M!monitoredBy(a): Notify(a,b)
        \* NEW: Actors are notified when monitored actors are exiled.
    \/ \E a \in BusyActors \ Receptionists: Register(a)
    \/ \E a \in IdleActors \intersect Receptionists: Wakeup(a)
    \/ \E a \in BusyActors \intersect Receptionists: Unregister(a)
    \/ \E m \in BagToSet(msgs): Drop(m)

-----------------------------------------------------------------------------

Soundness == M!Soundness
Completeness == M!Completeness

====