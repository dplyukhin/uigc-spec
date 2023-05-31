---- MODULE Exile ----
(* This model extends the Dropped model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID, status, and oracle. Every actor has a fixed location.  *)
CONSTANT NodeID
VARIABLE nodeStatus, oracle, location

(* Import operators from the Monitors model. *)
M == INSTANCE Monitors

ActorState == [
    status      : {"busy", "idle", "crashed", "exiled"}, \* NEW: Actors may become "exiled".
    recvCount   : Nat,
    sendCount   : [ActorName -> Nat],
    active      : [ActorName -> Nat],
    deactivated : [ActorName -> Nat],
    created     : [ActorName \X ActorName -> Nat],
    monitored   : SUBSET ActorName,
    exiled      : SUBSET NodeID, \* NEW: The set of nodes that this actor has exiled.
    isReceptionist : BOOLEAN
]

InitialActorState ==
    M!InitialActorState @@ [
        exiled |-> {}
    ]

(* In order to model exile, messages are now tagged with the ID of the sender node. *)
Message == [origin: NodeID, target: ActorName, refs : SUBSET ActorName] 

TypeOK == 
  /\ actors         \in [ActorName -> ActorState \cup {null}]
  /\ snapshots      \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs) \subseteq Message
  /\ nodeStatus \in [NodeID -> {"up", "down"}] \* Each node is either up or down.
  /\ DOMAIN oracle = NodeID                    \* Each node has an oracle tracking messages.
  /\ \A n \in NodeID : 
    BagToSet(oracle[n].delivered) \subseteq Message /\ 
    BagToSet(oracle[n].dropped) \subseteq Message
  /\ location   \in [ActorName -> NodeID \cup {null}] \* Each actor has a location.
  /\ \A a \in ActorName : actors[a] # null => location[a] # null

InitialConfiguration(actor, node, actorState) == 
    /\ M!InitialConfiguration(actor, actorState)
    /\ nodeStatus = [n \in NodeID |-> "up"]
    /\ oracle     = [n \in NodeID |-> [delivered |-> EmptyBag, dropped |-> EmptyBag]]
    /\ location   = [a \in ActorName |-> IF a = actor THEN node ELSE null]

-----------------------------------------------------------------------------
(* SET DEFINITIONS *)

ExiledNodes     == { n \in NodeID : nodeStatus[n] = "down" }
ExiledActors    == { a \in pdom(actors) : actors[a].status = "exiled" }
FaultyActors    == ExiledActors \union CrashedActors
NonExiledNodes  == { n \in NodeID : nodeStatus[n] = "up" }
NonExiledActors == pdom(actors) \ ExiledActors
NonFaultyActors == pdom(actors) \ FaultyActors

(* The bag of messages that have been sent to `a' and dropped. *)
droppedMsgsTo(a) == 
    selectWhere(oracle[location[a]].dropped, LAMBDA m: m.target = a)
(* The bag of messages that have been delivered to `a' from `nodes'. *)
deliveredMsgsTo(a, nodes) == 
    selectWhere(oracle[location[a]].delivered, LAMBDA m: m.target = a /\ m.origin \in nodes)
(* The bag of actors on `node' that have received references to `a' from exiledNodes.  
Each instance of an actor in the bag corresponds to one reference to `a'.*)
deliveredRefs(a, node, exiledNodes) == 
    BagOfAll(LAMBDA m: m.target,
        selectWhere(oracle[node].delivered, 
            LAMBDA m: a \in m.refs /\ m.origin \in exiledNodes))

-----------------------------------------------------------------------------
(* TRANSITION RULES *)

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

Receive(a,m) == M!Receive(a,m) /\
    LET node == location[a] IN
    /\ oracle' = [oracle EXCEPT ![node].delivered = put(@, m)]
    /\ UNCHANGED <<nodeStatus,location>>

Spawn(a,b,state,node) == 
    /\ M!Spawn(a, b, state)
    /\ location' = [location EXCEPT ![b] = node]
    /\ UNCHANGED <<nodeStatus,oracle>>

Drop(m) == 
    LET node == location[m.target] IN
    /\ msgs' = remove(msgs, m)
    /\ oracle' = [oracle EXCEPT ![node].dropped = put(@, m)]
    /\ UNCHANGED <<actors,snapshots,nodeStatus,location>>

Exile(nodes) ==
    /\ actors' = [a \in ActorName |-> 
                    IF location[a] \notin nodes THEN actors[a] ELSE 
                    [actors[a] EXCEPT !.status = "exiled"]
                 ]
    /\ msgs' = removeWhere(msgs, LAMBDA msg: 
                msg.origin \in nodes /\ location[msg.target] \in nodes)
    /\ nodeStatus' = [n \in NodeID |-> IF n \in nodes THEN "down" ELSE nodeStatus[n]]
    /\ oracle'     = [n \in NodeID |-> IF n \in nodes
                                       THEN [oracle[n] EXCEPT !.dropped = EmptyBag] 
                                        \* Dropped messages no longer need to be recorded after exile.
                                       ELSE oracle[n]]
    /\ UNCHANGED <<snapshots,location>>

DropOracle(a, droppedMsgs) ==
    LET node == location[a]
        droppedCount == BagCardinality(droppedMsgs)
        droppedRefs  == BagUnionOfSets(BagOfAll(LAMBDA msg: msg.refs, droppedMsgs)) IN
    /\ actors' = [ actors EXCEPT 
                   ![a].recvCount = @ + droppedCount,
                   ![a].deactivated = @ ++ droppedRefs
                 ]
    /\ oracle' = [oracle EXCEPT 
                    ![node].delivered = @ (+) droppedMsgs,
                    ![node].dropped   = @ (-) droppedMsgs]
                 \* The oracle now considers these messages to be "delivered".
    /\ UNCHANGED <<msgs,snapshots,location,nodeStatus>>

ExileOracle(a, exiledNodes) ==
    LET remainingNodes == NodeID \ (exiledNodes \union actors[a].exiled)
            \* The set of nodes that have not been exiled yet.
        delivered == deliveredMsgsTo(a, exiledNodes)
            \* The set of all messages delivered to `a', sent by actors in exiledNodes.
        created == BagUnion({ deliveredRefs(a, node, exiledNodes) : node \in remainingNodes })
            \* The bag of references pointing to `a', created by actors in exiledNodes
            \* for actors on remainingNodes.
    IN 
    /\ actors' = [ actors EXCEPT 
                   ![a].recvCount = @ - BagCardinality(delivered),
                   ![a].created = @ ++ BagOfAll(LAMBDA b: <<b,a>>, created),
                   ![a].exiled = @ \union exiledNodes
                 ]
    /\ UNCHANGED <<msgs,snapshots,location,nodeStatus,oracle>>

Init == 
    InitialConfiguration(CHOOSE a \in ActorName: TRUE, CHOOSE n \in NodeID: TRUE, InitialActorState)

Next ==
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: \E n \in NonExiledNodes: Spawn(a,b,InitialActorState,n)
        \* NEW: Actors are spawned onto a specific (non-exiled) node.
    \/ \E a \in BusyActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a) \ ExiledActors: \E refs \in SUBSET acqs(a): 
        Send(a,b,[origin |-> location[a], target |-> b, refs |-> refs])
        \* NEW: Messages are tagged with node locations and cannot be sent to faulty actors.
    \/ \E a \in IdleActors: \E m \in msgsTo(a): Receive(a,m)
    \/ \E a \in IdleActors \union BusyActors \union CrashedActors: Snapshot(a)
        \* NB: Exiled actors do not take snapshots.
    \/ \E a \in BusyActors: Crash(a)
    \/ \E a \in BusyActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors: \E b \in FaultyActors \intersect M!monitoredBy(a): Notify(a,b)
        \* NEW: Actors are notified when monitored actors are exiled.
    \/ \E a \in BusyActors \ Receptionists: Register(a)
    \/ \E a \in IdleActors \intersect Receptionists: Wakeup(a)
    \/ \E a \in BusyActors \intersect Receptionists: Unregister(a)
    \/ \E m \in BagToSet(msgs): Drop(m)
    \/ \E nodes \in SUBSET NonExiledNodes: Exile(nodes)
    \/ \E a \in NonFaultyActors: 
       \E droppedMsgs \in SubBag(droppedMsgsTo(a)): 
       DropOracle(a,droppedMsgs)
    \/ \E a \in NonFaultyActors: 
       \E exiledNodes \in SUBSET (ExiledNodes \ actors[a].exiled): 
       ExileOracle(a, exiledNodes)

-----------------------------------------------------------------------------
(* ACTUAL GARBAGE *)

monitoredBy(b) == M!monitoredBy(b)

isPotentiallyUnblockedUpToAFault(S) ==
    /\ Receptionists \ FaultyActors \subseteq S
    /\ Unblocked \ FaultyActors \subseteq S
    /\ \A a \in pdom(actors), b \in pdom(actors) \ FaultyActors :
        /\ (a \in S \intersect piacqs(b) => b \in S)
        /\ (a \in (S \union FaultyActors) \intersect monitoredBy(b) => b \in S)
            \* NEW: An actor is not garbage if it monitors an exiled actor

isPotentiallyUnblocked(S) ==
    /\ isPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in pdom(actors), b \in pdom(actors) \ FaultyActors :
        /\ (a \in monitoredBy(b) /\ location[a] # location[b] => b \in S)
            \* NEW: Actors that monitor remote actors are not garbage

PotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET pdom(actors) \ FaultyActors : isPotentiallyUnblockedUpToAFault(S)
QuiescentUpToAFault == 
    (pdom(actors) \ ExiledActors) \ PotentiallyUnblockedUpToAFault

PotentiallyUnblocked == 
    CHOOSE S \in SUBSET pdom(actors) \ FaultyActors : isPotentiallyUnblocked(S)
Quiescent == 
    (pdom(actors) \ ExiledActors) \ PotentiallyUnblocked

-----------------------------------------------------------------------------
(* APPARENT GARBAGE *)

AppearsClosed == M!AppearsClosed
AppearsCrashed == M!AppearsCrashed
AppearsFaulty == M!AppearsCrashed \union ExiledActors \* Nodes have common knowledge about exiled actors.
AppearsReceptionist == M!AppearsReceptionist
AppearsUnblocked == M!AppearsUnblocked
apparentIAcqs(b) == M!apparentIAcqs(b)
appearsMonitoredBy(b) == M!appearsMonitoredBy(b)

appearsPotentiallyUnblockedUpToAFault(S) == 
    /\ pdom(snapshots) \ (AppearsClosed \union AppearsCrashed) \subseteq S
    /\ AppearsReceptionist \ AppearsCrashed \subseteq S \* NEW: Exiled actors still appear potentially unblocked
    /\ AppearsUnblocked \ AppearsCrashed \subseteq S
    /\ \A a \in pdom(snapshots), b \in pdom(snapshots) \ AppearsCrashed :
        /\ (a \in S \intersect apparentIAcqs(b) => b \in S)
        /\ (a \in (S \union AppearsFaulty) \intersect appearsMonitoredBy(b) => b \in S)
            \* NEW: An actor is not garbage if it monitors an exiled actor

appearsPotentiallyUnblocked(S) == 
    /\ appearsPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in pdom(snapshots), b \in pdom(snapshots) \ AppearsCrashed :
        /\ (a \in appearsMonitoredBy(b) /\ location[a] # location[b] => b \in S)
            \* NEW: Actors that monitor remote actors are not garbage

AppearsPotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET pdom(snapshots) \ AppearsCrashed : appearsPotentiallyUnblockedUpToAFault(S)
AppearsQuiescentUpToAFault == 
    (pdom(snapshots) \ ExiledActors) \ AppearsPotentiallyUnblockedUpToAFault

AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET pdom(snapshots) \ AppearsCrashed : appearsPotentiallyUnblocked(S)
AppearsQuiescent == 
    (pdom(snapshots) \ ExiledActors) \ AppearsPotentiallyUnblocked

-----------------------------------------------------------------------------
(* SOUNDNESS AND COMPLETENESS PROPERTIES *)

SoundnessUpToAFault == 
    AppearsQuiescentUpToAFault \subseteq NonExiledActors => 
    AppearsQuiescentUpToAFault \subseteq QuiescentUpToAFault

Soundness == AppearsQuiescent \subseteq Quiescent

Relevant(a,b) == M!Relevant(a,b)
SnapshotUpToDate(a) == M!SnapshotUpToDate(a) 
(* `a' is recent enough for `b' if its snapshot is recent enough or `a' is
exiled and `b' has been updated about it. *)
RecentEnough(a,b) == 
    \/ M!RecentEnough(a,b) 
    \/ a \in ExiledActors => a \in actors[b].exiled

SnapshotsInsufficient == 
    CHOOSE S \in SUBSET pdom(actors): \A a \in pdom(actors): 
    /\ ~SnapshotUpToDate(a) => a \in S
    /\ \A b \in pdom(actors) \ CrashedActors:
        /\ droppedMsgsTo(b) # EmptyBag => b \in S
        /\ (Relevant(a,b) /\ ~RecentEnough(a,b) => b \in S)
        /\ (a \in S /\ a \in piacqs(b) => b \in S)
        /\ (a \in S /\ a \in monitoredBy(b) => b \in S)

SnapshotsSufficient == pdom(actors) \ SnapshotsInsufficient

CompletenessUpToAFault == 
    (QuiescentUpToAFault \intersect SnapshotsSufficient) \subseteq AppearsQuiescentUpToAFault

Completeness == (Quiescent \intersect SnapshotsSufficient) \subseteq AppearsQuiescent

-----------------------------------------------------------------------------
(* OTHER PROPERTIES: *)

SufficientIsTight == AppearsQuiescent \subseteq SnapshotsSufficient
SufficientIsTightUpToAFault == AppearsQuiescentUpToAFault \subseteq SnapshotsSufficient

-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)

GarbageIsDetected1 == ~(AppearsQuiescent # {})

GarbageIsDetected2 == ~(AppearsQuiescentUpToAFault # {})

ExiledGarbage == 
    \A a \in AppearsQuiescent \intersect NonFaultyActors:
    ~\E b \in ExiledActors \ pdom(snapshots): actors[b].active[a] > 0

====