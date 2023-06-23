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

ActorState == [
    status      : {"busy", "idle", "crashed", "exiled"}, \* NEW: Actors may become "exiled".
        \* Exiled actors are like crashed actors, except they cannot take snapshots.
    recvCount   : Nat,
    sendCount   : [ActorName -> Nat],
    active      : [ActorName -> Nat],
    deactivated : [ActorName -> Nat],
    created     : [ActorName \X ActorName -> Nat],
    monitored   : SUBSET ActorName,
    isRoot      : BOOLEAN
]

IngressState == [
    shunned      : BOOLEAN,
    sendCount    : [ActorName -> Nat],
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
  /\ ingressSnapshots \in [NodeID \X NodeID -> IngressState] \* NEW
  /\ \A a \in Actors: location[a] # null \* Every actor has a location upon being spawned.

InitialActorState == M!InitialActorState

InitialIngressState = [
    shunned      |-> FALSE,
    sendCount    |-> [a \in ActorName |-> 0],
    sentRefs     |-> [a,b \in ActorName |-> 0]
    droppedCount |-> [a \in ActorName |-> 0],
    droppedRefs  |-> [a,b \in ActorName |-> 0]
]

InitialConfiguration(initialActor, node, actorState) == 
    /\ M!InitialConfiguration(initialActor, actorState)
    /\ ingress          = [N_1, N_2 \in NodeID |-> InitialIngressState]
    /\ ingressSnapshots = [N_1, N_2 \in NodeID |-> InitialIngressState]
    /\ location         = [a \in ActorName |-> null] ++ (initialActor :> node)

-----------------------------------------------------------------------------
(* SET DEFINITIONS *)

ShunnedBy(N_2) == { N_1 \in NodeID : ingress[N_1,N_2].shunned }
NotShunnedBy(N_1) == NodeID \ ShunnedBy(N_1)
NeitherShuns(N_1) == { N_2 \in NodeID : ~ingress[N_1, N_2].shunned /\ ~ingress[N_2, N_1].shunned }

(* A faction of nodes G is exiled if every node outside of G has shunned 
   every node in G. *)
ExiledNodes == 
    LargestSubset(NodeID, LAMBDA G:
        \A N_1 \in G, N_2 \in NodeID \ G : ingress[N_1,N_2].shunned
    )
ExiledActors    == { a \in Actors : actors[a].status = "exiled" }
FaultyActors    == CrashedActors \union ExiledActors
NonFaultyActors == Actors \ FaultyActors

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
    /\ ingress' = [ingress EXCEPT ![N_1,N_2].sendCount = @ + 1, ![N_1,N_2].sentRefs = @ ++ B]
    /\ msgs' = replace(msgs, m, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

(* If an admitted message is dropped, then it is added to the ingress's bag of dropped messages. 
   If the ingress actor learns that a non-admitted message has been dropped, then the message is
   added both to the sent bag and the dropped bag. *)
Drop(m) == 
    LET N_1 == m.origin 
        N_2 == location[m.target]
        B   == [ b,c \in {m.target} \X m.refs |-> 1 ]
    IN
    /\ msgs' = remove(msgs, m)
    /\ IF m.admitted THEN 
           ingress' = [ingress EXCEPT ![N_1,N_2].droppedCount = @ + 1, ![N_1,N_2].droppedRefs = @ ++ B]
       ELSE
           ingress' = [ingress EXCEPT ![N_1,N_2].droppedCount = @ + 1, ![N_1,N_2].droppedRefs = @ ++ B,
                                      ![N_1,N_2].sendCount    = @ + 1, ![N_1,N_2].sentRefs    = @ + B]
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

Shun(N_1, N_2) ==
    /\ ingress' = [ingress EXCEPT ![N_1,N_2].shunned = TRUE]
    /\ actors' = [actors EXCEPT ![a].status = IF location[a] \in ExiledNodes THEN "exiled" else @]
        \* If the node has become exiled, then all its actors are marked as such.
    /\ snapshots' = [snapshots EXCEPT ![a] = IF location[a] \in ExiledNodes THEN null ELSE @]
    /\ UNCHANGED <<msgs,snapshots,ingressSnapshots,location>>

(* To reduce the model checking state space, the `Shun' rule can be replaced with the following `Exile'
   rule. This is safe because, for any execution in which a faction G_1 all shuns another faction G_2,
   there is an equivalent execution in which all `Shun' events happen successively.  *)
Exile(G_1, G_2) ==
    /\ ingress' = [ingress EXCEPT ![N_1,N_2].shunned = @ \/ (N_1 \in G_1 /\ N_2 \in G_2)]
    /\ actors' = [actors EXCEPT ![a].status = IF location[a] \in ExiledNodes THEN "exiled" ELSE @]
    /\ snapshots' = [snapshots EXCEPT ![a] = IF location[a] \in ExiledNodes THEN null ELSE @]
    /\ UNCHANGED <<msgs,snapshots,ingressSnapshots,location>>

IngressSnapshot(N_1, N_2) ==
    /\ ingressSnapshots' = [ingressSnapshots EXCEPT ![N_1,N_2] = ingress[N_1,N_2]]
    /\ UNCHANGED <<actors,msgs,snapshots,ingress,location>>

Init == 
    InitialConfiguration(CHOOSE a \in ActorName: TRUE, CHOOSE n \in NodeID: TRUE, InitialActorState)

Next ==
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: \E N \in NeitherShuns(location[a]):
       Spawn(a,b,InitialActorState,N)
        \* NEW: Actors are spawned onto a specific (non-shunned) node.
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
    \/ \E a \in BusyActors \ Roots: Register(a)
    \/ \E a \in IdleActors \intersect Roots: Wakeup(a)
    \/ \E a \in BusyActors \intersect Roots: Unregister(a)
    \/ \E m \in AdmissibleMsgs: Admit(m) \* NEW: Any admissible message can be admitted.
    \/ \E m \in BagToSet(msgs): Drop(m)  \* NEW: Any message can be dropped.
    \/ \E N_2 \in NodeID: \E N_1 \in NotShunnedBy(N_2): Shun(N_1,N_2) \* NEW: Nodes can shun other nodes.
    \* \/ \E G \in SUBSET NonExiledNodes: Exile(G)
    \/ \E N_1 \in NodeID: \E N_2 \in NonExiledNodes: ingress[N_1,N_2] # ingressSnapshots[N_1,N_2] /\ IngressSnapshot(node)
        \* NEW: Ingress actors can take snapshots if they have not been exiled. 
        \* To reduce the TLA+ search space, actors do not take snapshots that have no effect.

-----------------------------------------------------------------------------
(* ACTUAL GARBAGE *)

(* An actor is potentially unblocked if it is busy or can become busy. 
   (Crashed and exiled actors automatically fail this definition.)
   Similarly, an actor is potentially unblocked up-to-a-fault if it is busy
   or it can become busy in a non-faulty extension of this execution. *)

monitoredBy(b) == M!monitoredBy(b)

isPotentiallyUnblockedUpToAFault(S) ==
    /\ Roots \ FaultyActors \subseteq S
    /\ Unblocked \ FaultyActors \subseteq S
    /\ \A a \in Actors, b \in NonFaultyActors :
        /\ (a \in S \intersect piacqs(b) => b \in S)
        /\ (a \in (S \union FaultyActors) \intersect monitoredBy(b) => b \in S)
            \* NEW: An actor is not garbage if it monitors an exiled actor.

(* An actor is potentially unblocked if it is potentially unblocked up-to-a-fault
   or it monitors any remote actor. This is because remote actors can always
   become exiled, causing the monitoring actor to be notified. *)
isPotentiallyUnblocked(S) ==
    /\ isPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in Actors, b \in NonFaultyActors :
        /\ (a \in monitoredBy(b) /\ location[a] # location[b] => b \in S)

(* An actor is quiescent if it is not potentially unblocked. Likewise for 
   quiescence up-to-a-fault. *)
PotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET NonFaultyActors : isPotentiallyUnblockedUpToAFault(S)
QuiescentUpToAFault == Actors \ PotentiallyUnblockedUpToAFault

PotentiallyUnblocked == 
    CHOOSE S \in SUBSET NonFaultyActors : isPotentiallyUnblocked(S)
Quiescent == Actors \ PotentiallyUnblocked

(* Both definitions characterize a subset of the idle actors. The difference between the
   definitions is that quiescence up-to-a-fault is only a stable property in non-faulty
   executions. *)
QuiescentImpliesIdle == Quiescent \subseteq IdleActors
QuiescentUpToAFaultImpliesIdle == QuiescentUpToAFault \subseteq IdleActors

-----------------------------------------------------------------------------
(* APPARENT GARBAGE *)

(* A faction of nodes G is apparently exiled if every node outside of G has
   taken an ingress snapshot in which every node of G is shunned. *)
ApparentlyExiledNodes == 
    LargestSubset(ExiledNodes, LAMBDA G:
        \A N_1 \in G, N_2 \in NodeID \ G : 
            ingressSnapshots[N_1,N_2].shunned
    )
ApparentlyExiledActors == { a \in Actors : location[a] \in ApparentlyExiledNodes }
NonExiledSnapshots == Snapshots \ ApparentlyExiledActors

AppearsCrashed == M!AppearsCrashed
AppearsFaulty == M!AppearsCrashed \union ApparentlyExiledActors
AppearsRoot == M!AppearsRoot
appearsMonitoredBy(b) == M!appearsMonitoredBy(b)

(* The effective created count is the sum of (a) the created counts recorded by non-exiled actors
   and (b) the created counts recorded by ingress actors for exiled nodes. *)
effectiveCreatedCount(a, b) == 
    sum([ c \in NonExiledSnapshots |-> snapshots[c].created[a, b]]) +
    sum([ N_1 \in ApparentlyExiledNodes, N_2 \in NodeID \ ApparentlyExiledNodes |-> ingressSnapshots[N_1, N_2].created[a, b] ])

(* Once an actor `a' is exiled, all its references are effectively deactivated. Thus the effective 
   deactivated count is equal to the effective created count. 
   
   If an actor `a' is not exiled, all the references that were sent to `a' and dropped are effectively
   deactivated. Thus the effective deactivated count is the sum of an actor's actually deactivated references
   the number of dropped references. *)
effectiveDeactivatedCount(a, b) == 
    IF a \in ApparentlyExiledActors THEN 
        effectiveCreatedCount(a, b) 
    ELSE 
        (IF a \in Snapshots THEN snapshots[a].deactivated[b] ELSE 0) +
        sum([ N \in NodeID |-> ingressSnapshots[N, location[a]].droppedRefs[a, b] ])

(* Once an actor `a' is exiled, the number of messages that `a' effectively sent to some `b'
   is equal to the number of messages admitted by the ingress actor at `b''s node. Thus the
   effective total send count for `b' is the sum of the send counts from non-exiled actors
   and the number of messages for `b' that entered the ingress actor from apparently exiled nodes. *)
effectiveSendCount(b) == 
    sum([ a \in NonExiledSnapshots |-> snapshots[a].sendCount[b]]) +
    sum([ N_1 \in ApparentlyExiledNodes |-> ingressSnapshots[N_1, location[b]].sendCount[b] ])

(* All messages to actor `b' that were dropped are effectively received. Thus an actor's
   effective receive count is the sum of its actual receive count and the number of 
   dropped messages sent to it. *)
effectiveReceiveCount(b) == 
    (IF b \in Snapshots THEN snapshots[b].recvCount ELSE 0) +
    sum([ N \in NodeID |-> ingressSnapshots[N, location[b]].droppedCount[b] ])

(* NEW: Historical and apparent acquaintances now incorporate ingress snapshot information. 
   Once an actor appears exiled, it is no longer considered a historical or potential inverse
   acquaintance. *)
historicalIAcqs(c) == { b \in ActorName : effectiveCreatedCount(b, c) > 0 }
apparentIAcqs(c)   == { b \in ActorName : effectiveCreatedCount(b, c) > effectiveDeactivatedCount(b, c) }

AppearsIdle      == { a \in NonExiledSnapshots : snapshots[a].status = "idle" }
AppearsClosed    == { b \in NonExiledSnapshots : historicalIAcqs(b) \subseteq Snapshots }
AppearsBlocked   == { b \in AppearsIdle \cap AppearsClosed : effectiveSendCount(b) = effectiveReceiveCount(b) }
AppearsUnblocked == NonExiledSnapshots \ AppearsBlocked

appearsPotentiallyUnblockedUpToAFault(S) == 
    /\ Snapshots \ (AppearsClosed \union AppearsCrashed) \subseteq S
    /\ AppearsRoot \ AppearsCrashed \subseteq S \* NEW: Exiled actors still appear potentially unblocked.
    /\ AppearsUnblocked \ AppearsCrashed \subseteq S
    /\ \A a \in Snapshots, b \in Snapshots \ AppearsCrashed :
        /\ (a \in S \intersect apparentIAcqs(b) => b \in S)
        /\ (a \in (S \union AppearsFaulty) \intersect appearsMonitoredBy(b) => b \in S)
            \* NEW: An actor is not garbage if it monitors an exiled actor.

appearsPotentiallyUnblocked(S) == 
    /\ appearsPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in Snapshots, b \in Snapshots \ AppearsCrashed :
        /\ (a \in appearsMonitoredBy(b) /\ location[a] # location[b] => b \in S)
            \* NEW: Actors that monitor remote actors are not garbage.

AppearsPotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET Snapshots \ AppearsCrashed : appearsPotentiallyUnblockedUpToAFault(S)
AppearsQuiescentUpToAFault == 
    (Snapshots \ ExiledActors) \ AppearsPotentiallyUnblockedUpToAFault

AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET Snapshots \ AppearsCrashed : appearsPotentiallyUnblocked(S)
AppearsQuiescent == 
    (Snapshots \ ExiledActors) \ AppearsPotentiallyUnblocked


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

SnapshotsSufficient == Actors \ SnapshotsInsufficient

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
  ~(\E a,b \in Actors: a # b /\ a \in ExiledActors /\ b \in AppearsQuiescent /\ 
    a \in iacqs(b))

(* This invariant fails, showing that "quiescence up to a fault" is a strict 
   superset of quiescence. *)
GarbageUpToAFault == AppearsQuiescentUpToAFault \subseteq AppearsQuiescent

====