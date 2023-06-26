---- MODULE Exile ----
(* This model extends the Monitors model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID and every actor is located at some node. 
   Every pair of nodes has an ingress actor that tracks when messages are dropped 
   and when messages arrive at a node. Ingress actors can take snapshots. *)
CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots

M == INSTANCE Monitors

(* We add two fields to every message. `origin' indicates the node that produced the
   message and `admitted' indicates whether the message was admitted into the
   destination node by the ingress actor. All messages between actors on distinct nodes 
   must be admitted before they can be received by the destination actor. Messages 
   between actors on the same node are admitted by default. *)
Message == [
    origin: NodeID, 
    admitted: BOOLEAN, 
    target: ActorName, 
    refs : SUBSET ActorName
] 

-----------------------------------------------------------------------------
(* INITIALIZATION AND BASIC INVARIANTS *)

ActorState == M!ActorState

IngressState == [
    shunned      : BOOLEAN,
    sendCount    : [ActorName -> Nat],
    sentRefs     : [ActorName \X ActorName -> Nat],
    droppedCount : [ActorName -> Nat],
    droppedRefs  : [ActorName \X ActorName -> Nat]
]

(* The following invariant specifies the type of every variable
   in the configuration. It also asserts that every actor, once
   spawned, has a location. *)
TypeOK == 
  /\ actors           \in [ActorName -> ActorState \cup {null}]
  /\ snapshots        \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs)   \subseteq Message
  /\ location         \in [ActorName -> NodeID \cup {null}]  \* NEW
  /\ ingress          \in [NodeID \X NodeID -> IngressState] \* NEW
  /\ ingressSnapshots \in [NodeID \X NodeID -> IngressState] \* NEW
  /\ \A a \in Actors: location[a] # null 

InitialActorState == M!InitialActorState

InitialIngressState == [
    shunned      |-> FALSE,
    sendCount    |-> [a \in ActorName |-> 0],
    sentRefs     |-> [a,b \in ActorName |-> 0],
    droppedCount |-> [a \in ActorName |-> 0],
    droppedRefs  |-> [a,b \in ActorName |-> 0]
]

InitialConfiguration(initialActor, node, actorState) == 
    /\ M!InitialConfiguration(initialActor, actorState)
    /\ ingress          = [N1, N2 \in NodeID |-> InitialIngressState]
    /\ ingressSnapshots = [N1, N2 \in NodeID |-> InitialIngressState]
    /\ location         = (initialActor :> node) @@ [a \in ActorName |-> null]

-----------------------------------------------------------------------------
(* DEFINITIONS *)

(* A message is admissible if it is not already admitted and the origin
   node is not shunned by the destination node. *)
AdmissibleMsgs == { m \in BagToSet(msgs) : 
    ~m.admitted /\ ~ingress[m.origin, location[m.target]].shunned }

(* Because inadmissible messages can never be delivered, we
   update the definition of `msgsTo' to exclude them. This causes several
   other definitions below to change in subtle ways. For example, an actor
   `a' is potentially acquainted with `b' if all there is an inadmissible
   message to `a' containing a reference to `b'. *)
msgsTo(a)      == { m \in M!msgsTo(a) : m.admitted \/ m \in AdmissibleMsgs }
acqs(a)        == M!acqs(a)
iacqs(b)       == M!iacqs(b)
pacqs(a)       == { b \in ActorName : b \in acqs(a) \/ \E m \in msgsTo(a) : b \in m.refs }
piacqs(b)      == { a \in Actors : b \in pacqs(a) }
pastAcqs(a)    == M!pastAcqs(a)
pastIAcqs(b)   == M!pastIAcqs(b)
monitoredBy(b) == M!monitoredBy(b)
appearsMonitoredBy(b) == M!appearsMonitoredBy(b)
admittedMsgsTo(a) == { m \in msgsTo(a) : m.admitted }

(* Below, an actor can be blocked if all messages to it are inadmissible. *)
BusyActors     == M!BusyActors
IdleActors     == M!IdleActors
Blocked        == { a \in IdleActors : msgsTo(a) = {} }
Unblocked      == Actors \ Blocked
CrashedActors  == M!CrashedActors
AppearsCrashed == M!AppearsCrashed
Roots          == M!Roots
AppearsRoot    == M!AppearsRoot

ShunnedBy(N2)    == { N1 \in NodeID : ingress[N1,N2].shunned }
ShunnableBy(N1)  == (NodeID \ {N1}) \ ShunnedBy(N1)
NeitherShuns(N1) == { N2 \in NodeID : ~ingress[N1, N2].shunned /\ 
                                      ~ingress[N2, N1].shunned }

(* The exiled nodes are the largest nontrivial faction where every non-exiled
   node has shunned every exiled node. Likewise, a faction of nodes G is 
   apparently exiled if every node outside of G has taken an ingress snapshot 
   in which every node of G is shunned.  *)
ExiledNodes == 
    LargestSubset(NodeID, LAMBDA G:
        /\ G # NodeID
        /\ \A N1 \in G, N2 \in NodeID \ G: ingress[N1,N2].shunned
    )
ApparentlyExiledNodes == 
    LargestSubset(NodeID, LAMBDA G:
        /\ G # NodeID
        /\ \A N1 \in G, N2 \in NodeID \ G: ingressSnapshots[N1,N2].shunned
    )
NonExiledNodes            == NodeID \ ExiledNodes
ExiledActors              == { a \in Actors : location[a] \in ExiledNodes }
NonExiledActors           == Actors \ ExiledActors
FaultyActors              == CrashedActors \union ExiledActors
NonFaultyActors           == Actors \ FaultyActors

ApparentlyNonExiledNodes  == NodeID \ ApparentlyExiledNodes
ApparentlyExiledActors    == { a \in Actors : location[a] \in ApparentlyExiledNodes }
ApparentlyNonExiledActors == Actors \ ApparentlyExiledActors
AppearsFaulty             == M!AppearsCrashed \union ApparentlyExiledActors
AppearsNonFaulty          == Actors \ AppearsFaulty

NonExiledSnapshots        == Snapshots \ ApparentlyExiledActors

(* The total number of dropped messages to `b' is reflected in the state of its
   local ingress actors. *)
droppedMsgsTo(b) ==
    sum([ N \in NodeID |-> ingress[N, location[b]].droppedCount[b]])
apparentDroppedMsgsTo(b) ==
    sum([ N \in NodeID |-> ingressSnapshots[N, location[b]].droppedCount[b]])

(* The total number of dropped references to `b' is reflected in the state of
   ingress actors throughout the cluster. We are only interested in effective
   dropped references, i.e. references sent to non-exiled actors. *)
droppedRefCount(a,b) == 
    sum([ N \in NodeID |-> ingress[N, location[a]].droppedRefs[a, b] ])
apparentDroppedRefCount(a,b) == 
    sum([ N \in NodeID |-> ingressSnapshots[N, location[a]].droppedRefs[a, b] ])
droppedRefsTo(b) ==
    sum([ a \in NonExiledActors |-> droppedRefCount(a, b) ])
apparentDroppedRefsTo(b) ==
    sum([ a \in ApparentlyNonExiledActors |-> apparentDroppedRefCount(a, b) ])

-----------------------------------------------------------------------------
(* TRANSITIONS *)

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
    LET a  == m.target
        N1 == m.origin
        N2 == location[a] 
        B  == [ <<b,c>> \in {a} \X m.refs |-> 1 ]
    IN
    /\ ingress' = [ingress EXCEPT ![N1,N2].sendCount[a] = @ + 1, 
                                  ![N1,N2].sentRefs     = @ ++ B]
    /\ msgs' = replace(msgs, m, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

(* If an admitted message is dropped, then it is added to the ingress's bag of dropped messages. 
   If the ingress actor learns that a non-admitted message has been dropped, then the message is
   added both to the sent bag and the dropped bag. *)
Drop(m) == 
    LET a  == m.target
        N1 == m.origin 
        N2 == location[a]
        B  == [ <<b,c>> \in {a} \X m.refs |-> 1 ]
    IN
    /\ msgs' = remove(msgs, m)
    /\ IF m.admitted THEN 
           ingress' = [ingress EXCEPT ![N1,N2].droppedCount[a] = @ + 1, 
                                      ![N1,N2].droppedRefs     = @ ++ B]
       ELSE
           ingress' = [ingress EXCEPT ![N1,N2].droppedCount[a] = @ + 1, 
                                      ![N1,N2].droppedRefs     = @ ++ B,
                                      ![N1,N2].sendCount[a]    = @ + 1, 
                                      ![N1,N2].sentRefs        = @ ++ B]
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

(* When N2 shuns N1, the ingress actor at N2 is updated. If N1 is now
   exiled, we mark the actors as "exiled" to prevent them from taking
   snapshots. *)
Shun(N1, N2) ==
    /\ ingress' = [ingress EXCEPT ![N1,N2].shunned = TRUE]
    /\ UNCHANGED <<actors,msgs,snapshots,ingressSnapshots,location>>

(* To reduce the model checking state space, the `Shun' rule can be replaced with the following `Exile'
   rule. This is safe because, for any execution in which a faction G_1 all shuns another faction G_2,
   there is an equivalent execution in which all `Shun' events happen successively.  *)
Exile(G1, G2) ==
    /\ ingress' =
        [N1 \in G1, N2 \in G2 |-> [ingress[N1, N2] EXCEPT !.shunned = TRUE]] @@ ingress
    /\ UNCHANGED <<actors,msgs,snapshots,ingressSnapshots,location>>

(* Ingress actors can record snapshots. *)
IngressSnapshot(N1, N2) ==
    /\ ingressSnapshots' = [ingressSnapshots EXCEPT ![N1,N2] = ingress[N1,N2]]
    /\ UNCHANGED <<actors,msgs,snapshots,ingress,location>>

-----------------------------------------------------------------------------

Init == InitialConfiguration(
    CHOOSE a \in ActorName: TRUE, \* An arbitrary name for the initial actor.
    CHOOSE n \in NodeID: TRUE,    \* An arbitrary location for the actor.
    InitialActorState             \* The initial actor's state.
)

(* Several transition rules have been updated to account for locations.
   In addition, every rule is modified so that exiled actors no longer
   take actions. *)
Next ==
    \/ \E a \in BusyActors \ ExiledActors: Idle(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in FreshActorName: 
       \E N \in NeitherShuns(location[a]): Spawn(a,b,InitialActorState,N)
        \* UPDATE: Actors are spawned onto a specific (non-shunned) node.
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[origin |-> location[a], admitted |-> location[b] = location[a], 
                  target |-> b, refs |-> refs])
        \* UPDATE: Messages are tagged with node locations and cannot be sent to faulty actors.
    \/ \E a \in IdleActors \ ExiledActors: \E m \in admittedMsgsTo(a): Receive(a,m)
    \/ \E a \in Actors \ ExiledActors: Snapshot(a)
    \/ \E a \in BusyActors \ ExiledActors: Crash(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors \ ExiledActors: \E b \in FaultyActors \intersect M!monitoredBy(a): Notify(a,b)
        \* UPDATE: Actors are notified when monitored actors are exiled.
    \/ \E a \in (BusyActors \ Roots) \ ExiledActors: Register(a)
    \/ \E a \in (IdleActors \intersect Roots) \ ExiledActors: Wakeup(a)
    \/ \E a \in (BusyActors \intersect Roots) \ ExiledActors: Unregister(a)
    \/ \E m \in AdmissibleMsgs: Admit(m) \* NEW
    \/ \E m \in BagToSet(msgs): Drop(m)  \* NEW
    \/ \E N2 \in NonExiledNodes: \E N1 \in ShunnableBy(N2): Shun(N1,N2) \* NEW
    \/ \E N1 \in NodeID: \E N2 \in NonExiledNodes: 
        ingress[N1,N2] # ingressSnapshots[N1,N2] /\ IngressSnapshot(N1,N2) \* NEW
        \* To reduce the TLA+ search space, ingress actors do not take snapshots if
        \* their state has not changed.

\* The Shun rule above can be replaced with the following Exile rule without
\* loss of generality for faster model checking:
\* \/ \E G \in SUBSET NonExiledNodes: G # {} /\ G # NonExiledNodes /\ Exile(G, NonExiledNodes \ G)

-----------------------------------------------------------------------------
(* ACTUAL GARBAGE *)

(* An actor is potentially unblocked if it is busy or can become busy. 
   (Crashed and exiled actors automatically fail this definition.)
   Similarly, an actor is potentially unblocked up-to-a-fault if it is busy
   or it can become busy in a non-faulty extension of this execution. *)

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
QuiescentImpliesIdle == Quiescent \subseteq (IdleActors \union FaultyActors)
QuiescentUpToAFaultImpliesIdle == QuiescentUpToAFault \subseteq (IdleActors \union FaultyActors)

-----------------------------------------------------------------------------
(* APPARENT GARBAGE *)

(* The effective created count is the sum of (a) the created counts recorded by non-exiled actors
   and (b) the created counts recorded by ingress actors for exiled nodes. *)
effectiveCreatedCount(a, b) == 
    sum([ c \in NonExiledSnapshots |-> snapshots[c].created[a, b]]) +
    sum([ N1 \in ApparentlyExiledNodes, N2 \in NodeID \ ApparentlyExiledNodes |-> 
          ingressSnapshots[N1, N2].sentRefs[a, b] ])

(* Once an actor `a' is exiled, all its references are effectively deactivated. Thus the effective 
   deactivated count is equal to the effective created count. Note that any references sent to `a'
   that were dropped are implicitly included in this count.
   
   If an actor `a' is not exiled, all the references that were sent to `a' and dropped are effectively
   deactivated. Thus the effective deactivated count is the sum of an actor's actually deactivated references
   the number of dropped references. *)
effectiveDeactivatedCount(a, b) == 
    IF a \in ApparentlyExiledActors THEN 
        effectiveCreatedCount(a, b) 
    ELSE 
        (IF a \in Snapshots THEN snapshots[a].deactivated[b] ELSE 0) +
        apparentDroppedRefCount(a,b)

(* Once an actor `a' is exiled, the number of messages that `a' effectively sent to some `b'
   is equal to the number of messages admitted by the ingress actor at `b''s node. Thus the
   effective total send count for `b' is the sum of the send counts from non-exiled actors
   and the number of messages for `b' that entered the ingress actor from apparently exiled nodes. 
   Note that dropped messages to `b' are implicitly included in the sum. *)
effectiveSendCount(b) == 
    sum([ a \in NonExiledSnapshots |-> snapshots[a].sendCount[b]]) +
    sum([ N1 \in ApparentlyExiledNodes |-> ingressSnapshots[N1, location[b]].sendCount[b] ])

(* All messages to `b' that were dropped are effectively received. Thus an actor's
   effective receive count is the sum of its actual receive count and the number of 
   dropped messages sent to it. Note that dropped messages from exiled actors are
   also included in this count. *)
effectiveReceiveCount(b) == 
    (IF b \in Snapshots THEN snapshots[b].recvCount ELSE 0) +
    apparentDroppedMsgsTo(b)

(* Historical and apparent acquaintances now incorporate ingress snapshot information. 
   Once an actor appears exiled, it is no longer considered a historical or potential inverse
   acquaintance. In addition, if all references to `b' sent to `a' were dropped, then `a'
   is not considered a historical inverse acquaintance of `b'; this is because snapshots from
   `a' are not needed to determine whether `b' is quiescent.  *)
historicalIAcqs(c) == { b \in Actors : 
    effectiveCreatedCount(b, c) > apparentDroppedRefCount(b,c) }
apparentIAcqs(c)   == { b \in Actors : 
    effectiveCreatedCount(b, c) > effectiveDeactivatedCount(b, c) }

AppearsIdle      == { a \in NonExiledSnapshots : snapshots[a].status = "idle" }
AppearsClosed    == { b \in NonExiledSnapshots : 
    /\ historicalIAcqs(b)    \subseteq Snapshots \union ApparentlyExiledActors
    /\ appearsMonitoredBy(b) \subseteq Snapshots \union ApparentlyExiledActors }
AppearsBlocked   == { b \in NonExiledSnapshots \intersect AppearsIdle : 
    effectiveSendCount(b) = effectiveReceiveCount(b) }
AppearsUnblocked == NonExiledSnapshots \ AppearsBlocked

appearsPotentiallyUnblockedUpToAFault(S) == 
    /\ Snapshots \ (AppearsClosed \union AppearsFaulty) \subseteq S
    /\ AppearsRoot \ AppearsFaulty \subseteq S 
        \* NEW: Exiled actors still appear potentially unblocked.
    /\ AppearsUnblocked \ AppearsFaulty \subseteq S
    /\ \A a \in Snapshots, b \in Snapshots \ AppearsFaulty :
        /\ (a \in S \intersect apparentIAcqs(b) => b \in S)
        /\ (a \in (S \union AppearsFaulty) \intersect appearsMonitoredBy(b) => b \in S)
            \* NEW: An actor is not garbage if it monitors an exiled actor.

appearsPotentiallyUnblocked(S) == 
    /\ appearsPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in Snapshots, b \in Snapshots \ AppearsCrashed :
        /\ (a \in appearsMonitoredBy(b) /\ location[a] # location[b] => b \in S)
            \* NEW: Actors that monitor remote actors are not garbage.

AppearsPotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET Snapshots \ AppearsCrashed : 
    appearsPotentiallyUnblockedUpToAFault(S)
AppearsQuiescentUpToAFault == 
    Snapshots \ AppearsPotentiallyUnblockedUpToAFault

AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET Snapshots \ AppearsCrashed :
    appearsPotentiallyUnblocked(S)
AppearsQuiescent == 
    Snapshots \ AppearsPotentiallyUnblocked


-----------------------------------------------------------------------------
(* SOUNDNESS AND COMPLETENESS PROPERTIES *)
SoundnessUpToAFault == AppearsQuiescentUpToAFault \subseteq QuiescentUpToAFault
Soundness == AppearsQuiescent \subseteq Quiescent

SnapshotUpToDate(a) == M!SnapshotUpToDate(a)
RecentEnough(a,b) == M!RecentEnough(a,b)

SnapshotsInsufficient == 
    CHOOSE S \in SUBSET Actors : 
    /\ \A a \in NonExiledActors: ~SnapshotUpToDate(a) => a \in S
    /\ \A a \in NonFaultyActors:
        /\ droppedMsgsTo(a) # apparentDroppedMsgsTo(a) => a \in S
        /\ droppedRefsTo(a) # apparentDroppedRefsTo(a) => a \in S
        \* NEW: Dropped messages to nonfaulty actors must be accounted for.
    /\ \A a \in ExiledActors: 
        \* NEW: If an exiled actor does not already appear quiescent, then ingress
        \* actor snapshots are needed.
        a \notin AppearsQuiescent /\ a \notin ApparentlyExiledActors => a \in S
    /\ \A a \in ApparentlyNonExiledActors, b \in NonFaultyActors :
        \* NEW: We do not need up-to-date snapshots from inverse acquaintances that appear exiled.
        /\ (a \in pastIAcqs(b) /\ ~RecentEnough(a,b) => b \in S)
        /\ (a \in S /\ a \in piacqs(b) => b \in S)
        /\ (a \in S /\ a \in monitoredBy(b) => b \in S)
SnapshotsSufficient == Actors \ SnapshotsInsufficient

(* The next definition is identical to the one above, except it uses AppearsQuiescentUpToAFault
   instead of AppearsQuiescent. *)
SnapshotsInsufficientUpToAFault == 
    CHOOSE S \in SUBSET Actors : 
    /\ \A a \in NonExiledActors: ~SnapshotUpToDate(a) => a \in S
    /\ \A a \in NonFaultyActors:
        /\ droppedMsgsTo(a) # apparentDroppedMsgsTo(a) => a \in S
        /\ droppedRefsTo(a) # apparentDroppedRefsTo(a) => a \in S
    /\ \A a \in ExiledActors:
        a \notin AppearsQuiescentUpToAFault /\ a \notin ApparentlyExiledActors => a \in S
    /\ \A a \in ApparentlyNonExiledActors, b \in NonFaultyActors :
        /\ (a \in pastIAcqs(b) /\ ~RecentEnough(a,b) => b \in S)
        /\ (a \in S /\ a \in piacqs(b) => b \in S)
        /\ (a \in S /\ a \in monitoredBy(b) => b \in S)
SnapshotsSufficientUpToAFault == Actors \ SnapshotsInsufficientUpToAFault

(* The specificationstates that a non-exiled actor appears quiescent if and only
   if it is actually quiescent and there are sufficient snapshots to diagnose 
   quiescence. *)
Spec == 
    Quiescent \intersect SnapshotsSufficient \intersect NonExiledActors = 
    AppearsQuiescent \intersect NonExiledActors

(* For quiescence up-to-a-fault, the simple specification above is not sufficient.
   This is because an actor that is quiescent up-to-a-fault can become busy if
   it monitors a remote actor that became exiled. *)
SpecUpToAFault == 
    (\A a \in AppearsQuiescentUpToAFault: \A b \in appearsMonitoredBy(a): b \notin ExiledActors) =>
    QuiescentUpToAFault \intersect SnapshotsSufficientUpToAFault \intersect NonExiledActors = 
    AppearsQuiescentUpToAFault \intersect NonExiledActors

-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)

ActorsCanBeSpawned == Cardinality(Actors) < 4
MessagesCanBeReceived == \A a \in Actors: actors[a].recvCount = 0
SelfMessagesCanBeReceived == \A a \in Actors: actors[a].recvCount = 0 \/ Cardinality(Actors) > 1
ActorsCanBeExiled == \A a \in Actors: a \notin ExiledActors

(* This invariant fails, showing that the set of quiescent actors is nonempty. *)
GarbageExists == Quiescent = {}
NonFaultyGarbageExists == Quiescent \intersect NonFaultyActors = {}

GarbageUpToAFaultExists == QuiescentUpToAFault = {}
NonFaultyGarbageUpToAFaultExists == QuiescentUpToAFault \intersect NonFaultyActors = {}

(* This invariant fails, showing that quiescence can be detected and that it
   is possible to obtain a sufficient set of snapshots. *)
GarbageIsDetected == AppearsQuiescent = {}
NonFaultyGarbageIsDetected == AppearsQuiescent \ AppearsCrashed = {}
GarbageIsDetectedUpToAFault == AppearsQuiescentUpToAFault = {}
NonFaultyGarbageIsDetectedUpToAFault == AppearsQuiescentUpToAFault \ AppearsCrashed = {}

DistinctGarbageUpToAFault == AppearsQuiescentUpToAFault = AppearsQuiescent

(* This invariant fails, showing that quiescent actors can have crashed inverse
   acquaintances. *)
ExiledGarbageIsDetected == 
  ~(\E a,b \in Actors: a # b /\ a \in ExiledActors /\ b \in AppearsQuiescent /\ 
    a \in iacqs(b))

(* This invariant fails, showing that "quiescence up to a fault" is a strict 
   superset of quiescence. *)
GarbageUpToAFault == AppearsQuiescentUpToAFault \subseteq AppearsQuiescent

====