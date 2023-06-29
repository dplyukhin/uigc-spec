---- MODULE Exile ----
EXTENDS Integers, FiniteSets, Bags, TLC

(* The model is parameterized by sets ranging over actor names and node identifiers: *)
CONSTANT 
    ActorName,   \* Every actor has a unique name; this set ranges over all names.
    NodeID,      \* Every node has a unique identifier; this set ranges over all IDs.
    null         \* A TLA+-specific constant, used to indicate values where a partial map
                 \* is undefined.

(* A configuration is a 4-tuple (actors, location, msgs, shunned): *)
VARIABLE 
    actors,      \* A partial map from actor names to actor states (i.e. behaviors).
    location,    \* A partial map from actor names to actor locations (i.e. nodes).
    msgs,        \* A bag (i.e. multiset) of messages to be delivered.
    shunned      \* A relation on nodes, such that `shunned[N1,N2]' if `N2' shuns `N1'.

(* A message is modeled as a record. The `origin' field indicates the node that 
   produced the message; `admitted' indicates whether the message was admitted into the
   destination node; `target' indicates the name of the destination actor; and `refs'
   indicates the set of actor names contained inside the message.
   
   We do not explicitly model the payload of the message (aside from the `refs') because
   it is not relevant to garbage collection. *)
Message == [
    origin: NodeID, 
    admitted: BOOLEAN, 
    target: ActorName, 
    refs : SUBSET ActorName
] 

-----------------------------------------------------------------------------
(* INITIALIZATION AND BASIC INVARIANTS *)

(* ActorState is a record that models the state of an actor.
- status indicates whether the actor is busy, idle, or crashed.
- isRoot indicates whether the actor is a root, i.e. able to spontaneously
  change state from "idle" to "busy".
- active is a map representing the number of references this actor
  has to every other actor.
- monitored is the set of actors monitored by this actor.
*)
ActorState == [ 
    status    : {"busy", "idle", "crashed"},
    isRoot    : BOOLEAN,
    active    : [ActorName -> Nat],
    monitored : SUBSET ActorName
]

(* TypeOK is an invariant that holds in all reachable configurations. It
   specifies the type of each component of the configuration, and asserts
   that every actor has a location. *)
TypeOK == 
  /\ actors \in [ActorName -> ActorState \cup {null}]
  /\ location \in [ActorName -> NodeID \cup {null}]
  /\ BagToSet(msgs) \subseteq Message
  /\ \A a \in Actors: location[a] # null 

(* The initial configuration consists of an actor `a' located on node
   `N'. The actor a busy root with one reference to itself. *)
InitialConfiguration(a, N) == 
    LET state == [
        status: "busy", 
        isRoot: TRUE,
        active: (a :> 1) @@ [b \in ActorName |-> 0]
        \* The notation above states that `active[b]' is 0 for every
        \* `b' where `b # a', and `active[a]' is 1.
    ] 
    IN
    \* Similarly, `actors[b]' and `location[b]' are `null' (i.e. undefined) 
    \* for every actor except `a'; we set `actors[a]' equal to `state'
    \* (defined above) and `location[a]' equal to node `N'.
    /\ actors = (a :> state) @@ [b \in ActorName |-> null]
    /\ location = (a :> N) @@ [b \in ActorName |-> null]
    /\ msgs = EmptyBag

-----------------------------------------------------------------------------
(* DEFINITIONS *)

(* A message is admissible if it is not already admitted and the origin
   node is not shunned by the destination node. *)
AdmissibleMsgs   == { m \in BagToSet(msgs) : 
    ~m.admitted /\ ~shunned[m.origin, location[m.target]] }
AdmittedMsgs     == { m \in BagToSet(msgs) : m.admitted }

(* The exiled nodes are the largest nontrivial faction where every non-exiled
   node has shunned every exiled node. Likewise, a faction of nodes G is 
   apparently exiled if every node outside of G has taken an ingress snapshot 
   in which every node of G is shunned.  *)
ExiledNodes == 
    LargestSubset(NodeID, LAMBDA G:
        /\ G # NodeID
        /\ \A N1 \in G, N2 \in NodeID \ G: shunned[N1,N2]
    )
ExiledActors              == { a \in Actors : location[a] \in ExiledNodes }

-----------------------------------------------------------------------------
(* TRANSITIONS *)

(* This section of the model declares the events that may occur in an execution
   and how each event updates the configuration. 

   The events of an execution are defined as "actions" in TLA+:

   "An action represents a relation between old states 
   and new states, where the unprimed variables refer to the old state and the 
   primed variables refer to the new state. Thus, y = x' + 1 is the relation asserting 
   that the value of y in the old state is one greater than the value of x in the new state. 
   An atomic operation of a concurrent program will be represented in TLA by an action."
   [Lamport 1994]

   We will define events as a conjunction of expressions. In TLA+ syntax,
   one can write
    
     /\ e1
     /\ e2
     /\ e3

   instead of e1 /\ e2 /\ e3. Likewise for logical disjunction (`\/').

   We first define each event (Idle, Spawn, Send, ...) individually, and then define
   the Next relation which specifies all the possible transitions a configuration can
   take.
*)

(* A busy actor `a' can become idle by changing its status. *)
Idle(a) ==
    \* The notation below states that, as a result of the Idle event, the
    \* `actors' component of the configuration will change and the remaining
    \* components do not change.
    \*
    \* Specifically, the new value `actors' is identical to the old value, 
    \* except that the status of actor `a' is set to "idle".
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,locations,shunned>>

(* A busy actor `a' can spawn a fresh actor `b' onto a non-shunned node. *)
Spawn(a,b,N) == 
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1, \* The parent obtains a reference to the child.
        ![b] = [ 
            status: "busy",                                   \* The child is busy,
            root: FALSE,                                      \* not a root,
            active  = (b :> 1) @@ [c \in ActorName |-> null], \* and has a reference to itself.
        ]]
    /\ location' = [location EXCEPT ![b] = N]
    /\ UNCHANGED <<msgs,shunned>>

(* A busy actor can remove references from its state. *)
Deactivate(a,b) ==
    /\ actors' = [actors EXCEPT ![a].active[b] = 0]
    /\ UNCHANGED <<location,msgs,shunned>>

(* A busy actor can send messages to its acquaintances. *)
Send(a,b,m) ==
    /\ msgs' = put(msgs, m) \* Add message `m' to the msgs bag.
    /\ UNCHANGED <<actors,location,shunned>>

(* An idle actor can receive a message, becoming busy. *)
Receive(a,m) ==
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ msgs' = remove(msgs, m) \* Remove `m' from the msgs bag.
    /\ UNCHANGED <<location,shunned>>

(* Busy actors can crash. *)
Crash(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "crashed"]
    /\ UNCHANGED <<location,msgs,shunned>>

(* Busy actors can monitor their acquaintances. *)
Monitor(a,b) ==
    /\ actors' = [actors EXCEPT ![a].monitored = @ \union {b}] \* Add b to the monitored set.
    /\ UNCHANGED <<location,msgs,shunned>>

(* Monitoring actors can become "busy" after the actors they monitor fail. *)
Notify(a,b) ==
    \* Mark the monitoring actor as busy and remove `b' from the monitored set.
    /\ actors' = [actors EXCEPT ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<location,msgs,shunned>>

(* Busy actors can stop monitoring actors. *)
Unmonitor(a,b) ==
    /\ actors' = [actors EXCEPT ![a].monitored = @ \ {b}] \* Remove b from the monitored set.
    /\ UNCHANGED <<location,msgs,shunned>>

(* Actors can register as roots to spontaneously be awoken from "idle" state. *)
Register(a) ==
    /\ actors' = [actors EXCEPT ![a].isRoot = TRUE]
    /\ UNCHANGED <<location,msgs,shunned>>

(* A root actor can be awoken. *)
Wakeup(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ UNCHANGED <<location,msgs,shunned>>

(* Actors can unregister as roots. *)
Unregister(a) ==
    /\ actors' = [actors EXCEPT ![a].isRoot = FALSE]
    /\ UNCHANGED <<location,msgs,shunned>>

(* In-flight messages can be admitted. If node N1 shuns node N2, then messages
   from N1 can no longer be delivered to N2 unless they are already admitted. *)
Admit(m) ==
    /\ msgs' = replace(msgs, m, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,location,shunned>>

(* Any message can spontaneously be dropped. *)
Drop(m) == 
    /\ msgs' = remove(msgs, m)
    /\ UNCHANGED <<actors,location,shunned>>

(* A non-exiled node can shun another node. *)
Shun(N1, N2) ==
    /\ shunned' = [shunned EXCEPT ![N1,N2] = TRUE]
    /\ UNCHANGED <<actors,msgs,location>>

(* The following Exile event can safely be used in place of the Shun event to
   simplify reasoning and reduce the model checking state space. This is safe because, 
   for any execution in which a group of nodes G1 all shuns another group G2,
   there is an equivalent execution in which all `Shun' events happen successively.  *)
Exile(G1, G2) ==
    /\ shunned' = [N1 \in G1, N2 \in G2 |-> TRUE] @@ shunned
    /\ UNCHANGED <<actors,msgs,location>>

-----------------------------------------------------------------------------

(* Init defines the initial configuration, choosing an arbitrary name and 
   location for the initial actor. *)
Init == InitialConfiguration(
    CHOOSE a \in ActorName: TRUE, \* Choose an arbitrary name for the initial actor.
    CHOOSE N \in NodeID: TRUE,    \* Choose an arbitrary location for the actor.
)

(* Next defines the transition relation on configurations, defined as a TLA action,
   such that configuration K1 can atomically transition to configuration K2 if the 
   relation (K1)Next(K2) holds.

   For example, let K1 be a configuration with two busy actors `a,b' and an idle actor
   `c'. Then K1 can transition to a configuration K2 in which `a' is busy and `b,c'
   are idle, because of the Idle transition below.
*)
Next ==
    \/ \E a \in BusyActors \ ExiledActors: Idle(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in FreshActorName: 
       \E N \in NeitherShuns(location[a]): Spawn(a,b,InitialActorState,N)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[origin |-> location[a], 
                  admitted |-> location[b] = location[a], 
                  target |-> b, 
                  refs |-> refs])
    \/ \E a \in IdleActors \ ExiledActors: \E m \in admittedMsgsTo(a): Receive(a,m)
    \/ \E a \in BusyActors \ ExiledActors: Crash(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors \ ExiledActors: \E b \in FaultyActors \intersect M!monitoredBy(a): 
        Notify(a,b)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in monitoredBy(a): Unmonitor(a,b)
    \/ \E a \in (BusyActors \ Roots) \ ExiledActors: Register(a)
    \/ \E a \in (IdleActors \intersect Roots) \ ExiledActors: Wakeup(a)
    \/ \E a \in (BusyActors \intersect Roots) \ ExiledActors: Unregister(a)
    \/ \E m \in AdmissibleMsgs: location[m.target] \notin ExiledNodes /\ Admit(m)
    \/ \E m \in AdmissibleMsgs \union AdmittedMsgs: location[m.target] \notin ExiledNodes /\ Drop(m)
    \/ \E N2 \in NonExiledNodes: \E N1 \in ShunnableBy(N2): Shun(N1,N2)
    \* The Shun rule above can be replaced with the following Exile rule without
    \* loss of generality for faster model checking:
    \* \/ \E G \in SUBSET NonExiledNodes: G # {} /\ G # NonExiledNodes /\ Exile(G, NonExiledNodes \ G)

-----------------------------------------------------------------------------
(* GARBAGE *)

(* An actor is potentially unblocked if it is busy or can become busy. 
   (Crashed and exiled actors automatically fail this definition.)
   Similarly, an actor is potentially unblocked up-to-a-fault if it is busy
   or it can become busy in a non-faulty extension of this execution. *)

isPotentiallyUnblockedUpToAFault(S) ==
    /\ Roots \ FaultyActors \subseteq S
    /\ Unblocked \ FaultyActors \subseteq S 
    /\ \A a \in S, b \in NonFaultyActors : 
        a \in piacqs(b) => b \in S
    /\ \A a \in S \union FaultyActors, b \in NonFaultyActors :
        a \in monitoredBy(b) => b \in S
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

====