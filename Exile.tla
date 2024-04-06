---- MODULE Exile ----
(* This model extends the Monitors model with dropped messages and faulty nodes.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Every node has a unique ID and every actor is located at some node. 
   Every pair of nodes has an ingress actor that tracks when messages are dropped 
   and when messages arrive at a node. Ingress actors can take snapshots. 
   There is also a temporary holding area for messages that have been dropped
   but whose recipient has not yet learned of the drop. *)
CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots, droppedMsgs

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
    admittedMsgs : [ActorName -> Nat],
    admittedRefs : [ActorName \X ActorName -> Nat]
]

(* The following invariant specifies the type of every variable
   in the configuration. It also asserts that every actor, once
   spawned, has a location; and every message in droppedMsgs must have
   first been admitted. *)
TypeOK == 
  /\ actors                \in [ActorName -> ActorState \cup {null}]
  /\ snapshots             \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs)        \subseteq Message
  /\ BagToSet(droppedMsgs) \subseteq Message
  /\ location              \in [ActorName -> NodeID \cup {null}]  \* NEW
  /\ ingress               \in [NodeID \X NodeID -> IngressState] \* NEW
  /\ ingressSnapshots      \in [NodeID \X NodeID -> IngressState] \* NEW
  /\ \A a \in Actors: location[a] # null 
  /\ \A m \in BagToSet(droppedMsgs): m.admitted

InitialActorState == M!InitialActorState

InitialIngressState == [
    shunned      |-> FALSE,
    admittedMsgs |-> [a \in ActorName |-> 0],
    admittedRefs |-> [a,b \in ActorName |-> 0]
]

InitialConfiguration(initialActor, node, actorState) == 
    /\ M!InitialConfiguration(initialActor, actorState)
    /\ ingress          = [N1, N2 \in NodeID |-> InitialIngressState]
    /\ ingressSnapshots = [N1, N2 \in NodeID |-> InitialIngressState]
    /\ location         = (initialActor :> node) @@ [a \in ActorName |-> null]
    /\ droppedMsgs      = EmptyBag

-----------------------------------------------------------------------------
(* DEFINITIONS *)

(* A message is admissible if it is not already admitted and the origin
   node is not shunned by the destination node. *)
AdmissibleMsgs   == { m \in BagToSet(msgs) : 
    ~m.admitted /\ ~ingress[m.origin, location[m.target]].shunned }
AdmittedMsgs     == { m \in BagToSet(msgs) : m.admitted }

(* Because inadmissible messages can never be delivered, we
   update the definition of `msgsTo' to exclude them. This causes several
   other definitions below to change in subtle ways. For example, an actor
   `a' is potentially acquainted with `b' if all there is an inadmissible
   message to `a' containing a reference to `b'. *)
msgsTo(a)        == { m \in M!msgsTo(a) : m.admitted \/ m \in AdmissibleMsgs }
acqs(a)          == M!acqs(a)
iacqs(b)         == M!iacqs(b)
pacqs(a)         == { b \in ActorName : b \in acqs(a) \/ \E m \in msgsTo(a) : b \in m.refs }
piacqs(b)        == { a \in Actors : b \in pacqs(a) }
pastAcqs(a)      == M!pastAcqs(a)
pastIAcqs(b)     == M!pastIAcqs(b)
monitoredBy(b)   == M!monitoredBy(b)
appearsMonitoredBy(b) == M!appearsMonitoredBy(b)
admittedMsgsTo(a)     == { m \in msgsTo(a) : m.admitted }

(* Below, an actor can be blocked if all messages to it are inadmissible. *)
BusyActors    == M!BusyActors
IdleActors    == M!IdleActors
Blocked       == { a \in IdleActors : msgsTo(a) = {} }
Unblocked     == Actors \ Blocked
HaltedActors  == M!HaltedActors
AppearsHalted == M!AppearsHalted
StickyActors  == M!StickyActors
AppearsSticky == M!AppearsSticky

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
FailedActors              == HaltedActors \union ExiledActors
HealthyActors             == Actors \ FailedActors

ApparentlyNonExiledNodes  == NodeID \ ApparentlyExiledNodes
ApparentlyExiledActors    == { a \in Actors : location[a] \in ApparentlyExiledNodes }
ApparentlyNonExiledActors == Actors \ ApparentlyExiledActors
AppearsFailed             == M!AppearsHalted \union ApparentlyExiledActors
AppearsHealthy            == Actors \ AppearsFailed

NonExiledSnapshots        == Snapshots \ ApparentlyExiledActors

droppedMsgsTo(a) == { m \in BagToSet(droppedMsgs) : m.target = a }
droppedPIAcqs(b) == { a \in Actors : \E m \in droppedMsgsTo(a) : b \in m.refs }

-----------------------------------------------------------------------------
(* TRANSITIONS *)

Idle(a)         == M!Idle(a)         /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Deactivate(a,b) == M!Deactivate(a,b) /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Send(a,b,m)     == M!Send(a,b,m)     /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Receive(a,m)    == M!Receive(a,m)    /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Snapshot(a)     == M!Snapshot(a)     /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Halt(a)         == M!Halt(a)         /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Monitor(a,b)    == M!Monitor(a,b)    /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Unmonitor(a,b)  == M!Unmonitor(a,b)  /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Notify(a,b)     == M!Notify(a,b)     /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Register(a)     == M!Register(a)     /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Wakeup(a)       == M!Wakeup(a)       /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>
Unregister(a)   == M!Unregister(a)   /\ UNCHANGED <<location,ingress,ingressSnapshots,droppedMsgs>>

Spawn(a,b,state,N) == 
    /\ M!Spawn(a, b, state)
    /\ location' = [location EXCEPT ![b] = N]
    /\ UNCHANGED <<msgs,ingress,ingressSnapshots,droppedMsgs>>

Admit(m) ==
    LET a  == m.target
        N1 == m.origin
        N2 == location[a] 
        B  == [ <<b,c>> \in {a} \X m.refs |-> 1 ]
    IN
    /\ ingress' = [ingress EXCEPT ![N1,N2].admittedMsgs[a] = @ + 1, 
                                  ![N1,N2].admittedRefs    = @ ++ B]
    /\ msgs' = replace(msgs, m, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location,droppedMsgs>>

(* Dropped messages are admitted (if necessary) by the recipient ingress
   actor and then added to the droppedMsgs bag. *)
Drop(m) == 
    /\ IF ~m.admitted THEN 
        LET a  == m.target
            N1 == m.origin 
            N2 == location[a]
            B  == [ <<b,c>> \in {a} \X m.refs |-> 1 ]
        IN
        ingress' = [ingress EXCEPT ![N1,N2].admittedMsgs[a] = @ + 1, 
                                   ![N1,N2].admittedRefs    = @ ++ B]
       ELSE UNCHANGED <<ingress>>
    /\ msgs' = remove(msgs, m)
    /\ droppedMsgs' = put(droppedMsgs, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,snapshots,ingressSnapshots,location>>

(* Some time after a message has been dropped, the recipient actor's local
   state is updated. *)
DetectDropped(a, m) ==
    /\ droppedMsgs' = remove(droppedMsgs, m)
    /\ actors' = [actors EXCEPT ![a].received = @ + 1, 
                                ![a].deactivated = @ ++ [c \in m.refs |-> 1]]
    /\ UNCHANGED <<msgs,snapshots,ingress,ingressSnapshots,location>>

(* When N2 shuns N1, the ingress actor at N2 is updated. If N1 is now
   exiled, we mark the actors as "exiled" to prevent them from taking
   snapshots. *)
Shun(N1, N2) ==
    /\ ingress' = [ingress EXCEPT ![N1,N2].shunned = TRUE]
    /\ UNCHANGED <<actors,msgs,snapshots,ingressSnapshots,location,droppedMsgs>>

(* To reduce the model checking state space, the `Shun' rule can be replaced with the following `Exile'
   rule. This is safe because, for any execution in which a faction G_1 all shuns another faction G_2,
   there is an equivalent execution in which all `Shun' events happen successively.  *)
Exile(G1, G2) ==
    /\ ingress' =
        [N1 \in G1, N2 \in G2 |-> [ingress[N1, N2] EXCEPT !.shunned = TRUE]] @@ ingress
    /\ UNCHANGED <<actors,msgs,snapshots,ingressSnapshots,location,droppedMsgs>>

(* Ingress actors can record snapshots. *)
IngressSnapshot(N1, N2) ==
    /\ ingressSnapshots' = [ingressSnapshots EXCEPT ![N1,N2] = ingress[N1,N2]]
    /\ UNCHANGED <<actors,msgs,snapshots,ingress,location,droppedMsgs>>

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
        \* UPDATE: Messages are tagged with node locations.
    \/ \E a \in IdleActors \ ExiledActors: \E m \in admittedMsgsTo(a): Receive(a,m)
    \/ \E a \in Actors \ ExiledActors: Snapshot(a)
    \/ \E a \in BusyActors \ ExiledActors: Halt(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors \ ExiledActors: \E b \in FailedActors \intersect monitoredBy(a): 
        Notify(a,b)
        \* UPDATE: Actors are notified when monitored actors are exiled.
    \/ \E a \in BusyActors \ ExiledActors: \E b \in monitoredBy(a): Unmonitor(a,b)
    \/ \E a \in (BusyActors \ StickyActors) \ ExiledActors: Register(a)
    \/ \E a \in (IdleActors \intersect StickyActors) \ ExiledActors: Wakeup(a)
    \/ \E a \in (BusyActors \intersect StickyActors) \ ExiledActors: Unregister(a)
    \/ \E m \in AdmissibleMsgs: location[m.target] \notin ExiledNodes /\ Admit(m) \* NEW
    \/ \E m \in AdmissibleMsgs \union AdmittedMsgs: location[m.target] \notin ExiledNodes /\ Drop(m)  \* NEW
    \/ \E a \in IdleActors \ ExiledActors: \E m \in droppedMsgsTo(a): 
        DetectDropped(m.target, m)  \* NEW
    \/ \E N1 \in NodeID: \E N2 \in NonExiledNodes: 
        ingress[N1,N2] # ingressSnapshots[N1,N2] /\ IngressSnapshot(N1,N2) \* NEW
        \* To reduce the TLA+ search space, ingress actors do not take snapshots if
        \* their state has not changed.
    \/ \E N2 \in NonExiledNodes: \E N1 \in ShunnableBy(N2): Shun(N1,N2) \* NEW
    \* The Shun rule above can be replaced with the following Exile rule without
    \* loss of generality for faster model checking:
    \* \/ \E G \in SUBSET NonExiledNodes: G # {} /\ G # NonExiledNodes /\ Exile(G, NonExiledNodes \ G)

-----------------------------------------------------------------------------
(* ACTUAL GARBAGE *)

(* An actor is potentially unblocked if it is busy or can become busy. 
   (Halted and exiled actors automatically fail this definition.)
   Similarly, an actor is potentially unblocked up-to-a-fault if it is busy
   or it can become busy in a non-faulty extension of this execution. *)

isPotentiallyUnblockedUpToAFault(S) ==
    /\ StickyActors \ FailedActors \subseteq S
    /\ Unblocked \ FailedActors \subseteq S 
    /\ \A a \in S, b \in HealthyActors : 
        a \in piacqs(b) => b \in S
    /\ \A a \in S \union FailedActors, b \in HealthyActors :
        a \in monitoredBy(b) => b \in S
            \* NEW: An actor is not garbage if it monitors an exiled actor.
            
(* An actor is potentially unblocked if it is potentially unblocked up-to-a-fault
   or it monitors any remote actor. This is because remote actors can always
   become exiled, causing the monitoring actor to be notified. *)
isPotentiallyUnblocked(S) ==
    /\ isPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in Actors, b \in HealthyActors :
        /\ (a \in monitoredBy(b) /\ location[a] # location[b] => b \in S)

(* An actor is quiescent if it is not potentially unblocked. Likewise for 
   quiescence up-to-a-fault. *)
PotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET HealthyActors : isPotentiallyUnblockedUpToAFault(S)
QuiescentUpToAFault == Actors \ PotentiallyUnblockedUpToAFault

PotentiallyUnblocked == 
    CHOOSE S \in SUBSET HealthyActors : isPotentiallyUnblocked(S)
Quiescent == Actors \ PotentiallyUnblocked

(* Both definitions characterize a subset of the idle actors. The difference between the
   definitions is that quiescence up-to-a-fault is only a stable property in non-faulty
   executions. *)
QuiescentImpliesIdle == Quiescent \subseteq (IdleActors \union FailedActors)
QuiescentUpToAFaultImpliesIdle == QuiescentUpToAFault \subseteq (IdleActors \union FailedActors)

-----------------------------------------------------------------------------
(* APPARENT GARBAGE *)

(* The effective created count is the sum of (a) the created counts recorded by non-exiled actors
   and (b) the created counts recorded by ingress actors for exiled nodes. *)
created(a, b) == 
    sum([ c \in NonExiledSnapshots |-> snapshots[c].created[a, b]]) +
    sum([ N1 \in ApparentlyExiledNodes, N2 \in NodeID \ ApparentlyExiledNodes |-> 
          ingressSnapshots[N1, N2].admittedRefs[a, b] ])

(* Once an actor `a' is exiled, all its references are effectively deactivated. Thus the effective 
   deactivated count is equal to the effective created count. Note that any references sent to `a'
   that were dropped are implicitly included in this count. *)
deactivated(a, b) == 
    IF a \in ApparentlyExiledActors THEN 
        created(a, b) 
    ELSE 
        IF a \in Snapshots THEN snapshots[a].deactivated[b] ELSE 0

(* Once an actor `a' is exiled, the number of messages that `a' sent effectively to some `b'
   is equal to the number of messages admitted by the ingress actor at `b''s node. Thus the
   effective total send count for `b' is the sum of the send counts from non-exiled actors
   and the number of messages for `b' that entered the ingress actor from apparently exiled nodes. 
   Note that dropped messages to `b' are implicitly included in the sum. *)
sent(b) == 
    sum([ a \in NonExiledSnapshots |-> snapshots[a].sent[b]]) +
    sum([ N1 \in ApparentlyExiledNodes |-> ingressSnapshots[N1, location[b]].admittedMsgs[b] ])

(* All messages to `b' that were dropped are effectively received. Thus an actor's
   effective receive count is the sum of its actual receive count and the number of 
   dropped messages sent to it. Note that dropped messages from exiled actors are
   also included in this count. *)
received(b) == IF b \in Snapshots THEN snapshots[b].received ELSE 0

(* Hereto inverse acquaintances now incorporate ingress snapshot information. 
   Once an actor appears exiled, it is no longer considered a hereto inverse
   acquaintance.  *)
heretoIAcqs(c)   == { b \in Actors : created(b, c) > 0 }
apparentIAcqs(c) == { b \in Actors : created(b, c) > deactivated(b, c) }

AppearsIdle      == { a \in NonExiledSnapshots : snapshots[a].status = "idle" }
AppearsClosed    == { b \in NonExiledSnapshots : 
    /\ heretoIAcqs(b)        \subseteq Snapshots \union ApparentlyExiledActors
    /\ appearsMonitoredBy(b) \subseteq Snapshots \union ApparentlyExiledActors }
AppearsBlocked   == { b \in NonExiledSnapshots \intersect AppearsIdle : sent(b) = received(b) }
AppearsUnblocked == NonExiledSnapshots \ AppearsBlocked

appearsPotentiallyUnblockedUpToAFault(S) == 
    /\ Snapshots \ (AppearsClosed \union AppearsFailed) \subseteq S
    /\ AppearsSticky \ AppearsFailed \subseteq S 
        \* NEW: Exiled actors still appear potentially unblocked.
    /\ AppearsUnblocked \ AppearsFailed \subseteq S
    /\ \A a \in S, b \in Snapshots \ AppearsFailed :
        a \in apparentIAcqs(b) => b \in S
    /\ \A a \in S \union AppearsFailed, b \in Snapshots \ AppearsFailed :
        a \in appearsMonitoredBy(b) => b \in S
            \* NEW: An actor is not garbage if it monitors an exiled actor.

appearsPotentiallyUnblocked(S) == 
    /\ appearsPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in Actors, b \in Snapshots \ AppearsFailed :
        /\ (a \in appearsMonitoredBy(b) /\ location[a] # location[b] => b \in S)
            \* NEW: Actors that monitor remote actors are not garbage.

AppearsPotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET Snapshots \ AppearsFailed : 
    appearsPotentiallyUnblockedUpToAFault(S)
AppearsQuiescentUpToAFault == 
    Snapshots \ AppearsPotentiallyUnblockedUpToAFault

AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET Snapshots \ AppearsFailed :
    appearsPotentiallyUnblocked(S)
AppearsQuiescent == 
    Snapshots \ AppearsPotentiallyUnblocked

-----------------------------------------------------------------------------
(* SOUNDNESS AND COMPLETENESS PROPERTIES *)

(* Exiled actors may need to appear exiled in order for all quiescent garbage to be
   detected. *)
SnapshotUpToDate(a) == 
    IF a \in ExiledActors THEN a \in ApparentlyExiledActors ELSE 
    IF a \in HaltedActors THEN a \in AppearsHalted ELSE M!SnapshotUpToDate(a)
RecentEnough(a,b) == 
    IF a \in ExiledActors THEN a \in ApparentlyExiledActors ELSE 
    IF a \in HaltedActors THEN a \in AppearsHalted ELSE M!RecentEnough(a,b)
BeingExiled(a) == 
    \E N \in NonExiledNodes: 
    location[a] \in ShunnedBy(N) /\ location[a] \notin ExiledNodes
    
    
SnapshotsInsufficient == 
    CHOOSE S \in SUBSET Actors: 
    /\ \A N1, N2 \in ApparentlyNonExiledNodes: N1 \in ShunnedBy(N2) => 
        Actors \subseteq S
        \* NEW: Shunning creates garbage actors that might not be detected
        \* until those nodes are apparently exiled.
    /\ \A b \in Actors:
        /\ ~SnapshotUpToDate(b) => b \in S
        /\ b \in HealthyActors /\ droppedMsgsTo(b) # {} => b \in S
        \* NEW: Actors may need to be notified about dropped references.
        /\ \A a \in Actors:
            /\ a \in pastIAcqs(b) /\ ~RecentEnough(a,b) => b \in S
            /\ a \in S /\ a \in piacqs(b) => b \in S
            /\ a \in S /\ a \in monitoredBy(b) => b \in S
            /\ a \in S /\ a \in droppedPIAcqs(b) => b \in S
            \* NEW: Recipients of dropped messages containing references to b
            \* may need to have sufficient snapshots.
SnapshotsSufficient == Actors \ SnapshotsInsufficient

(* The specification states that a non-exiled actor appears quiescent if and only
   if it is actually quiescent and there are sufficient snapshots to diagnose 
   quiescence. *)
Spec == 
    /\ AppearsQuiescent \subseteq Quiescent
    /\ Quiescent \subseteq AppearsQuiescent \union SnapshotsInsufficient \union ExiledActors

(* For quiescence up-to-a-fault, the simple specification above is not sufficient.
   This is because an actor that is quiescent up-to-a-fault can become busy if
   it monitors a remote actor that became exiled. *)
SpecUpToAFault == 
    (\A a \in AppearsQuiescentUpToAFault: \A b \in appearsMonitoredBy(a): b \notin ExiledActors) =>
    /\ AppearsQuiescentUpToAFault \subseteq QuiescentUpToAFault
    /\ QuiescentUpToAFault \subseteq AppearsQuiescentUpToAFault \union SnapshotsInsufficient \union ExiledActors

-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)

ActorsCanBeSpawned == Cardinality(Actors) < 4
MessagesCanBeReceived == \A a \in Actors: actors[a].received = 0
SelfMessagesCanBeReceived == \A a \in Actors: actors[a].received = 0 \/ Cardinality(Actors) > 1
ActorsCanBeExiled == \A a \in Actors: a \notin ExiledActors

(* This invariant fails, showing that the set of quiescent actors is nonempty. *)
GarbageExists == Quiescent = {}
HealthyGarbageExists == Quiescent \intersect HealthyActors = {}

GarbageUpToAFaultExists == QuiescentUpToAFault = {}
HealthyGarbageUpToAFaultExists == QuiescentUpToAFault \intersect HealthyActors = {}

(* This invariant fails, showing that quiescence can be detected and that it
   is possible to obtain a sufficient set of snapshots. *)
GarbageIsDetected == AppearsQuiescent = {}
HealthyGarbageIsDetected == AppearsQuiescent \ AppearsHalted = {}
GarbageIsDetectedUpToAFault == AppearsQuiescentUpToAFault = {}
HealthyGarbageIsDetectedUpToAFault == AppearsQuiescentUpToAFault \ AppearsHalted = {}

DistinctGarbageUpToAFault == AppearsQuiescentUpToAFault = AppearsQuiescent

(* This invariant fails, showing that quiescent actors can have halted inverse
   acquaintances. *)
ExiledGarbageIsDetected == 
  ~(\E a,b \in Actors: a # b /\ a \in ExiledActors /\ b \in AppearsQuiescent /\ 
    a \in iacqs(b))

(* This invariant fails, showing that "quiescence up to a fault" is a strict 
   superset of quiescence. *)
GarbageUpToAFault == AppearsQuiescentUpToAFault \subseteq AppearsQuiescent

====