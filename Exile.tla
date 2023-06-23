---- MODULE Exile ----
(* This model extends the Monitors model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID and every actor is located at some node. 
   Every pair of nodes has an ingress actor that tracks when messages are dropped 
   and when messages arrive at a node. Ingress actors can take snapshots. *)
CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots

(* Import operators from the Monitors model. *)
M == INSTANCE Monitors

(* We add two fields to every message. `origin' indicates the node that produced the
   message and `admitted' indicates whether the message was admitted into the
   destination node by the ingress actor. All messages between actors on distinct nodes 
   must be admitted before they can be received by the destination actor. Messages 
   between actors on the same node are admitted by default. *)
Message == [origin: NodeID, admitted: BOOLEAN, target: ActorName, refs : SUBSET ActorName] 

-----------------------------------------------------------------------------
(* INITIALIZATION AND BASIC INVARIANTS *)

MessagesTo(node) == { m \in Message : location[m.target] = node }

ActorState == M!ActorState

IngressState == [
    shunned      : BOOLEAN,
    sentCount    : [ActorName -> Nat],
    sentRefs     : [ActorName \X ActorName -> Nat],
    droppedCount : [ActorName -> Nat],
    droppedRefs  : [ActorName \X ActorName -> Nat]
]

TypeOK == 
  /\ actors           \in [ActorName -> ActorState \cup {null}]
  /\ snapshots        \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs)   \subseteq Message
  /\ location         \in [ActorName -> NodeID \cup {null}] \* NEW
  /\ ingress          \in [NodeID \X NodeID -> IngressState] \* NEW
  /\ ingressSnapshots \in [NodeID \X NodeID -> IngressState \cup {null}] \* NEW
  /\ \A a \in pdom(actors): location[a] # null \* Every actor has a location upon being spawned

InitialActorState == M!InitialActorState

InitialConfiguration(initialActor, node, actorState) == 
    /\ M!InitialConfiguration(initialActor, actorState)
    /\ ingress = 
        [N_1, N_2 \in NodeID |->
            [shunned      |-> FALSE,
             sentCount    |-> [a \in ActorName |-> 0],
             sentRefs     |-> [a,b \in ActorName |-> 0]
             droppedCount |-> [a \in ActorName |-> 0],
             droppedRefs  |-> [a,b \in ActorName |-> 0]
            ]
        ]
    /\ ingressSnapshots = [N_1, N_2 \in NodeID |-> null]
    /\ location = [a \in ActorName |-> null] ++ (initialActor :> node)

-----------------------------------------------------------------------------
(* SET DEFINITIONS *)

ShunnedBy(N_2) == { N_1 \in NodeID : ingress[N_1,N_2].shunned }
NotShunnedBy(N_1) == NodeID \ ShunnedBy(N_1)
NeitherShuns(N_1) == { N_2 \in NodeID : ~ingress[N_1, N_2].shunned /\ ~ingress[N_2, N_1].shunned }

(* A message must be admitted before being delivered. *)
deliverableMsgsTo(a) == { a \in msgsTo(a) : a.admitted }

(* A message is admissible if it is not already admitted and the origin
   node is not shunned by the destination node. *)
AdmissibleMsgs ==
    { m \in BagToSet(msgs) : ~m.admitted /\ ~ingress[m.origin, location[m.target]].shunned }
        
-----------------------------------------------------------------------------
(* TRANSITION RULES *)

Idle(a)         == M!Idle(a)         /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Deactivate(a,b) == M!Deactivate(a,b) /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Send(a,b,m)     == M!Send(a,b,m)     /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Receive(a,m)    == M!Receive(a,m)    /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Snapshot(a)     == M!Snapshot(a)     /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Crash(a)        == M!Crash(a)        /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Monitor(a,b)    == M!Monitor(a,b)    /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Notify(a,b)     == M!Notify(a,b)     /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Register(a)     == M!Register(a)     /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Wakeup(a)       == M!Wakeup(a)       /\ UNCHANGED <<location,ingress,ingressSnapshots>>
Unregister(a)   == M!Unregister(a)   /\ UNCHANGED <<location,ingress,ingressSnapshots>>

Spawn(a,b,state,N) == 
    /\ M!Spawn(a, b, state)
    /\ location' = [location EXCEPT ![b] = N]
    /\ UNCHANGED <<msgs,ingress,ingressSnapshots>>

Admit(m) ==
    LET N_1 == m.origin
        N_2 == location[m.target] 
        B   == [ b,c \in {m.target} \X m.refs |-> 1 ]
    IN
    /\ ingress' = [ingress EXCEPT ![N_1,N_2].sentCount = @ + 1, ![N_1,N_2].sentRefs = @ ++ B]
    /\ msgs' = replace(msgs, m, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

(* If a message is in flight, then it is added to the ingress's bag of dropped messages. 
   If the message has been admitted, the ingress moves the message from its bag of sent messages 
   to its bag of dropped messages. *)
Drop(m) == 
    LET N_1 == m.origin 
        N_2 == location[m.target]
        B   == [ b,c \in {m.target} \X m.refs |-> 1 ]
    IN
    /\ msgs' = remove(msgs, m)
    /\ IF ~m.admitted THEN 
           ingress' = [ingress EXCEPT ![N_1,N_2].droppedCount = @ + 1, ![N_1,N_2].droppedRefs = @ ++ B]
       ELSE
           ingress' = [ingress EXCEPT ![N_1,N_2].droppedCount = @ + 1, ![N_1,N_2].droppedRefs = @ ++ B,
                              i       ![N_1,N_2].sentCount    = @ - 1, ![N_1,N_2].sentRefs    = @ -- B]
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

Shun(N_1, N_2) ==
    /\ ingress' = [ingress EXCEPT ![N_1,N_2].shunned = TRUE]
    /\ UNCHANGED <<actors,msgs,snapshots,ingressSnapshots,location>>

(* To reduce the model checking state space, the `Shun' rule can be replaced with the following `Exile'
   rule. This is safe because, for any execution in which a faction G_1 all shuns another faction G_2,
   there is an equivalent execution in which all `Shun' events happen successively.  *)
Exile(G_1, G_2) ==
    /\ ingress' = [ingress EXCEPT ![N_1,N_2].shunned = @ \/ (N_1 \in G_1 /\ N_2 \in G_2)]
    /\ UNCHANGED <<actors,msgs,snapshots,ingressSnapshots,location>>

IngressSnapshot(N_1, N_2) ==
    /\ ingressSnapshots' = [ingressSnapshots EXCEPT ![N_1,N_2] = ingress[N_1,N_2]]
    /\ UNCHANGED <<actors,msgs,snapshots,ingress,location>>

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
    \/ \E a \in BusyActors: \E b \in FreshActorName: \E N \in NeitherShuns(location[a]):
       Spawn(a,b,InitialActorState,N)
        \* NEW: Actors are spawned onto a specific (non-exiled) node.
    \/ \E a \in BusyActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[origin |-> location[a], admitted |-> location[b] = location[a], 
                  target |-> b, refs |-> refs])
        \* NEW: Messages are tagged with node locations and cannot be sent to faulty actors.
    \/ \E a \in IdleActors: \E m \in deliverableMsgsTo(a): Receive(a,m)
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
    \/ \E node \in NonExiledNodes: ingress[N_1,N_2] # ingressSnapshots[N_1,N_2] /\ IngressSnapshot(node)
        \* NEW: Ingress actors can take snapshots. No need to take snapshots that have no effect.
    \/ \E m \in AdmissibleMsgs: Admit(m)
    (*
    \/ \E a \in NonFaultyActors: 
       \E droppedMsgs \in SubBag(droppedMsgsTo(a)): 
       DropOracle(a,droppedMsgs)
    \/ \E a \in NonFaultyActors: 
       \E exiledNodes \in SUBSET (ExiledNodes \ actors[a].exiled): 
       ExileOracle(a, exiledNodes *)

-----------------------------------------------------------------------------
(* ACTUAL GARBAGE *)

(* An actor is potentially unblocked if it is busy or can become busy. 
   (Crashed and exiled actors automatically fail this definition.)
   Similarly, an actor is potentially unblocked up-to-a-fault if it is busy
   or it can become busy in a non-faulty extension of this execution. *)

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

(* An actor is quiescent if it has not been exiled and it is not potentially 
   unblocked. Likewise for quiescence up-to-a-fault. *)

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

LargestSubset(D, F) == 
    D \ CHOOSE S \in SUBSET D: ~F(S)

(* A set of nodes S is apparently exiled if every node aside from S has
   taken an ingress snapshot and the ingress snapshots were all taken after
   S was exiled. *)
ApparentlyExiledNodes == 
    LargestSubset(ExiledNodes, LAMBDA S:
        /\ (NodeID \ S) \subseteq pdom(ingressSnapshots)
        /\ \A node \in NodeID \ S : S \subseteq ingressSnapshots[node].exiled
    )
ApparentlyExiledActors == { a \in pdom(actors) : location[a] \in ApparentlyExiledNodes }

(* The bag of messages that have been sent to `a' from `nodes' and were dropped. *)
apparentDroppedMsgsTo ==
    BagUnion({ droppedMessages(n1,n2) : 
        n1 \in ApparentlyExiledNodes, n2 \in NodeID \ ApparentlyExiledNodes })

apparentDeliveredMsgs ==
    BagUnion({ deliveredMessages(n1,n2) : 
        n1 \in ApparentlyExiledNodes, n2 \in NodeID \ ApparentlyExiledNodes })

effectivelyCreatedRefs ==
    {}


(* The bag of messages that have been delivered to `a' from apparently exiled nodes. *)
effectivelyDeliveredMsgsTo(a) == 
    selectWhere(ingressSnapshots[location[a]].delivered, 
                LAMBDA m: m.target = a /\ m.origin \in ApparentlyExiledNodes)

(* The bag of actors on `nodes' that have received references to `a' from 
   nodes that are apparently exiled. Each instance of an actor in the bag 
   corresponds to one reference to `a'. *)
effectivelyDeliveredRefsTo(a) == 
    LET B1(a, n) == selectWhere(ingressSnapshots[n].delivered, 
                                LAMBDA msg: a \in msg.refs /\ msg.origin \in ApparentlyExiledNodes) IN
        \* B1(a, n) is the bag of messages delivered to node n that contain a reference to `a'.
    LET B2(a, n) == BagOfAll(LAMBDA msg: msg.target, B1(a, n)) IN 
        \* B2(a, n) is the bag of actors on node n that have received references to `a'.
    BagUnion({ B2(a,n) : n \in NodeID \ ApparentlyExiledNodes})

AppearsCrashed == M!AppearsCrashed
AppearsFaulty == M!AppearsCrashed \union ExiledActors \* Nodes have common knowledge about exiled actors.
AppearsReceptionist == M!AppearsReceptionist
appearsMonitoredBy(b) == M!appearsMonitoredBy(b)

(* We now use snapshots from both actors and ingresss to compute effective message counts and 
   potential references. *)

effectiveCreatedCount == 
    BagUnion({ snapshots[c].created : c \in pdom(snapshots) \ ApparentlyExiledActors }) (+)
    deliveredRefsFromExiledNodes
effectiveDeactivatedCount == 
    [ <<a,b>> \in ... |-> snapshots[a].deactivated[b] ] (+)
    createdRefsForExiledNodes
    \* Refs from exiled actors are all deactivated
effectiveSendCount == 
    sum([ a \in pdom(snapshots) \ ApparentlyExiledActors |-> snapshots[a].sendCount[b]]) +
    BagCardinality(effectivelyDeliveredMsgsTo(b))

(* `b' is an effective historical inverse acquaintance of `c' if... *)
historicalIAcqs(c) == { b \in ActorName : effectiveCreatedCount[b, c] > 0 }
apparentIAcqs(c)   == { b \in ActorName : effectiveCreatedCount[b, c] > effectiveDeactivatedCount[b, c] }
    \* TODO We can ignore exiled actors if we have sufficient ingress snapshots

(* If an exiled actor `a' is historically potentially acquainted with `b', then
   `b' is only closed if we have sufficient ingress snapshots. *)
AppearsClosed  == { b \in pdom(snapshots) : effectiveHistoricalIAcqs(b) \subseteq pdom(snapshots) }
AppearsBlocked == { b \in AppearsIdle \cap AppearsClosed : countSentTo(b) = countReceived(b) }

AppearsBlocked == ???
AppearsUnblocked == NonExiledActors \ AppearsBlocked 
apparentIAcqs(b) == ???


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

\* TODO: Check that quiescence actually means the actor never becomes busy.

SoundnessUpToAFault == 
    AppearsQuiescentUpToAFault \subseteq NonExiledActors => 
    AppearsQuiescentUpToAFault \subseteq QuiescentUpToAFault

Soundness == AppearsQuiescent \subseteq Quiescent

SnapshotUpToDate(a) == M!SnapshotUpToDate(a)
RecentEnough(a,b) == M!RecentEnough(a,b)

SnapshotsInsufficient == 
    CHOOSE S \in SUBSET NonExiledActors : 
    /\ \A a \in NonExiledActors : (~SnapshotUpToDate(a) => a \in S)
        \* NEW: Snapshots from exiled actors are always sufficient.
    /\ \A a \in ExiledActors : \A b \in NonFaultyActors :
        (a \in piacqs(b) /\ ~FinishedExile(a,b) => b \in S)
        \* NEW: Exiled potential inverse acquaintances must be marked.
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