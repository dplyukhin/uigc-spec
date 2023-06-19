---- MODULE Exile ----
(* This model extends the Monitors model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID, status, and oracle. Oracles can take snapshots. 
   Every actor has a fixed location.  *)
CONSTANT NodeID
VARIABLE nodeStatus, oracle, oracleSnapshots, location

(* Import operators from the Monitors model. *)
M == INSTANCE Monitors

ActorState == [
    status      : {"busy", "idle", "crashed", "exiled"}, \* NEW: Actors may become "exiled".
    \* Like crashed actors, exiled actors are "stuck"; they cannot take additional steps.
    \* But unlike crashed actors, exiled actors cannot take snapshots.
    recvCount   : Nat,
    sendCount   : [ActorName -> Nat],
    active      : [ActorName -> Nat],
    deactivated : [ActorName -> Nat],
    created     : [ActorName \X ActorName -> Nat],
    monitored   : SUBSET ActorName,
    isReceptionist : BOOLEAN
]

InitialActorState == M!InitialActorState

(* In order to model exile, messages are now tagged with the ID of the sender node. 
   This ID is not necessary for implementing the garbage collection algorithm itself. *)
Message == [origin: NodeID, target: ActorName, refs : SUBSET ActorName] 

-----------------------------------------------------------------------------
(* SET DEFINITIONS *)

ExiledNodes     == { n \in NodeID : nodeStatus[n] = "out" }
ExiledActors    == { a \in pdom(actors) : actors[a].status = "exiled" }
FaultyActors    == ExiledActors \union CrashedActors
NonExiledNodes  == { n \in NodeID : nodeStatus[n] = "in" }
NonExiledActors == pdom(actors) \ ExiledActors
NonFaultyActors == pdom(actors) \ FaultyActors

MessagesTo(node) == { m \in Message : location[m.target] = node }

(* The bag of messages that have been sent to `a' by non-exiled nodes and dropped. *)
droppedMsgsTo(a) == 
    selectWhere(oracle[location[a]].dropped, LAMBDA m: m.target = a /\ m.origin \notin ExiledNodes)
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
(* INITIALIZATION AND BASIC INVARIANTS *)

OracleTypeOK(map) ==
  (* An oracle tracks the messages that have been dropped or delivered to actors on
     its node. It also tracks the set of nodes that have been exiled so far. *)
  /\ DOMAIN map = NodeID
  /\ \A n \in pdom(map) : 
    BagToSet(map[n].delivered) \subseteq MessagesTo(n) /\ 
    BagToSet(map[n].dropped) \subseteq MessagesTo(n) /\
    map[n].exiled \subseteq ExiledNodes

TypeOK == 
  /\ actors         \in [ActorName -> ActorState \cup {null}]
  /\ snapshots      \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs) \subseteq Message
  /\ nodeStatus \in [NodeID -> {"in", "out"}]       \* Each node is in the cluster or out of it.
  /\ OracleTypeOK(oracle)                           \* Each node has an oracle tracking messages.
  /\ OracleTypeOK(oracleSnapshots)                  \* Oracles can take snapshots.
  /\ location \in [ActorName -> NodeID \cup {null}] \* Each actor has a location.
  /\ \A a \in ActorName : actors[a] # null => location[a] # null

InitialConfiguration(actor, node, actorState) == 
    /\ M!InitialConfiguration(actor, actorState)
    /\ nodeStatus      = [n \in NodeID |-> "in"]
    /\ oracle          = [n \in NodeID |-> [delivered |-> EmptyBag, dropped |-> EmptyBag, exiled |-> {}]]
    /\ oracleSnapshots = [n \in NodeID |-> null]
    /\ location        = [a \in ActorName |-> IF a = actor THEN node ELSE null]

-----------------------------------------------------------------------------
(* TRANSITION RULES *)

Idle(a)         == M!Idle(a)         /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Deactivate(a,b) == M!Deactivate(a,b) /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Send(a,b,m)     == M!Send(a,b,m)     /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Snapshot(a)     == M!Snapshot(a)     /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Crash(a)        == M!Crash(a)        /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Monitor(a,b)    == M!Monitor(a,b)    /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Notify(a,b)     == M!Notify(a,b)     /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Register(a)     == M!Register(a)     /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Wakeup(a)       == M!Wakeup(a)       /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>
Unregister(a)   == M!Unregister(a)   /\ UNCHANGED <<location,nodeStatus,oracle,oracleSnapshots>>

Receive(a,m) == M!Receive(a,m) /\
    LET node == location[a] IN
    /\ oracle' = [oracle EXCEPT ![node].delivered = put(@, m)]
    /\ UNCHANGED <<nodeStatus,oracleSnapshots,location>>

Spawn(a,b,state,node) == 
    /\ M!Spawn(a, b, state)
    /\ location' = [location EXCEPT ![b] = node]
    /\ UNCHANGED <<nodeStatus,oracleSnapshots,oracle>>

Drop(m) == 
    LET node == location[m.target] IN
    /\ msgs' = remove(msgs, m)
    /\ oracle' = [oracle EXCEPT ![node].dropped = put(@, m)]
    /\ UNCHANGED <<actors,snapshots,nodeStatus,oracleSnapshots,location>>

Exile(nodes) ==
    /\ actors' = [a \in ActorName |-> 
                    IF location[a] \notin nodes THEN actors[a] ELSE 
                    [actors[a] EXCEPT !.status = "exiled"]
                 ]
    /\ msgs' = removeWhere(msgs, LAMBDA msg: 
                msg.origin \in nodes /\ location[msg.target] \in nodes)
    /\ nodeStatus' = [n \in NodeID |-> IF n \in nodes THEN "out" ELSE nodeStatus[n]]
    /\ oracle' = [n \in NodeID |-> IF n \notin ExiledNodes \union nodes 
                                   THEN [oracle[n] EXCEPT !.exiled = @ \union nodes]
                                   ELSE oracle[n]]
    /\ UNCHANGED <<snapshots,oracleSnapshots,location>>

(*
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
*)

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
    (*
    \/ \E a \in NonFaultyActors: 
       \E droppedMsgs \in SubBag(droppedMsgsTo(a)): 
       DropOracle(a,droppedMsgs)
    \/ \E a \in NonFaultyActors: 
       \E exiledNodes \in SUBSET (ExiledNodes \ actors[a].exiled): 
       ExileOracle(a, exiledNodes *)

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

(* NEW: A snapshot is up to date if all fields except `exiled' agree the actor's
   current state. *)
SnapshotUpToDate(a) ==
    /\ a \in pdom(snapshots)
    /\ actors[a].status = snapshots[a].status
    /\ actors[a].recvCount = snapshots[a].recvCount
    /\ actors[a].sendCount = snapshots[a].sendCount
    /\ actors[a].active = snapshots[a].active
    /\ actors[a].deactivated = snapshots[a].deactivated
    /\ actors[a].created = snapshots[a].created
    /\ actors[a].monitored = snapshots[a].monitored
    /\ actors[a].isReceptionist = snapshots[a].isReceptionist
RecentEnough(a,b) == M!RecentEnough(a,b)

SnapshotsInsufficient == 
    CHOOSE S \in SUBSET NonExiledActors : 
    /\ \A a \in NonExiledActors : (~SnapshotUpToDate(a) => a \in S)
        \* NEW: Snapshots from exiled actors are always sufficient.
    /\ \A a \in ExiledActors : \A b \in NonFaultyActors :
        (a \in piacqs(b) /\ ~FinishedExile(a,b) => b \in S)
        \* NEW: Exiled potential inverse acquaintances must be processed.
    /\ \A a \in NonExiledActors : \A b \in NonFaultyActors :
        /\ droppedMsgsTo(b) # EmptyBag => b \in S 
        \* NEW: Dropped messages from non-exiled nodes must be detected.
        /\ (a \in pastIAcqs(b) /\ ~RecentEnough(a,b) => b \in S)
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

(* This invariant fails, showing that the set of quiescent actors is nonempty. *)
GarbageExists == ~(Quiescent = {})

(* This invariant fails, showing that quiescence can be detected and that it
   is possible to obtain a sufficient set of snapshots. *)
GarbageIsDetected == ~(AppearsQuiescent = {})

(* This invariant fails, showing that quiescent actors can have crashed inverse
   acquaintances. *)
ExiledGarbageIsDetected == 
  ~(\E a,b \in pdom(actors): a # b /\ a \in ExiledActors /\ b \in AppearsQuiescent /\ 
    a \in iacqs(b))

(* This invariant fails, showing that "quiescence up to a fault" is a strict 
   superset of quiescence. *)
GarbageUpToAFault == AppearsQuiescentUpToAFault \subseteq AppearsQuiescent

====