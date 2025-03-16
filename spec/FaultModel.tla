---- MODULE FaultModel ----
EXTENDS Integers, FiniteSets, Bags, TLC

(* 
The model is parameterized by sets ranging over actor names and node identifiers: *)
CONSTANT 
    ActorName,   \* Every actor has a unique name; this set ranges over all names.
    NodeID,      \* Every node has a unique identifier; this set ranges over all IDs.
    null         \* A TLA+-specific constant, used to indicate values where a partial map
                 \* is undefined.

(* 
A configuration is a 4-tuple (`actors', `location', `msgs', `shunned'): *)
VARIABLE 
    actors,      \* A partial map from actor names to actor states (i.e. behaviors).
    location,    \* A partial map from actor names to actor locations (i.e. nodes).
    msgs,        \* A bag (i.e. multiset) of messages to be delivered.
    shunned      \* A relation on nodes, such that `shunned[N1,N2]' if N2 shuns N1.

(* 
A message is modeled as a record. The `origin' field indicates the node that 
produced the message; `admitted' indicates whether the message was admitted into the
destination node; `target' indicates the name of the destination actor; and `refs'
indicates the set of actor names contained inside the message.

We do not explicitly model the payload of the message (aside from the refs) because
it is not relevant to garbage collection. *)
Message == [
    origin: NodeID, 
    admitted: BOOLEAN, 
    target: ActorName, 
    refs : SUBSET ActorName
] 

-----------------------------------------------------------------------------
(* 
INITIALIZATION AND BASIC INVARIANTS 
*)

(* 
ActorState is a record that models the state of an actor:
   - status indicates whether the actor is busy, idle, or halted.
   - isSticky indicates whether the actor is sticky, i.e. able to spontaneously
     change state from "idle" to "busy".
   - active is a map representing the number of references this actor
     has to every other actor.
   - monitored is the set of actors monitored by this actor.
*)
ActorState == [ 
    status    : {"busy", "idle", "halted"},
    isSticky  : BOOLEAN,
    active    : [ActorName -> Nat],
    monitored : SUBSET ActorName
]

(* 
TypeOK is an invariant that specifies the type of each component
in the configuration. 

In TLA+ syntax, a conjunction `e1 /\ e2 /\ e3' can be written as follows:
 
  /\ e1
  /\ e2
  /\ e3

We will use this special syntax for better readability.
*)
TypeOK == 
  /\ actors \in [ActorName -> ActorState \cup {null}]
  /\ location \in [ActorName -> NodeID \cup {null}]
  /\ BagToSet(msgs) \subseteq Message
  /\ shunned \in [NodeID \X NodeID -> BOOLEAN]
  (* The above invariant states that `actors' and `location' are partial 
     maps and that `msgs' is a bag of messages. *)

(* 
The initial configuration consists of an actor `a' located on node
N. The actor is a busy sticky actor with one reference to itself. 

The expression `(a :> 1) @@ [b \in ActorName |-> 0]' defines a function
which maps each `b' to 0 except for `a', which is mapped to 1.
*)
InitialConfiguration(a, N) == 
    LET state == [
        status    |-> "busy", 
        isSticky  |-> TRUE,
        active    |-> (a :> 1) @@ [b \in ActorName |-> 0],
        monitored |-> {}
    ] 
    IN
    /\ actors = (a :> state) @@ [b \in ActorName |-> null]
    /\ location = (a :> N) @@ [b \in ActorName |-> null]
    /\ msgs = EmptyBag
    /\ shunned = [N1,N2 \in NodeID |-> FALSE]
    (* 
    `actors[b]' and `location[b]' are `null' (i.e. undefined) 
    for every actor except `a'; we set `actors[a]' equal to `state'
    (defined above) and `location[a]' equal to node `N'. *)

-----------------------------------------------------------------------------
(* DEFINITIONS *)

(* 
Below are TLA+ mechanisms for computing the largest subset of D that satisfies F,
and for selecting fresh actor names.
*)
LargestSubset(D, F(_)) == D \ CHOOSE S \in SUBSET D: F(D \ S)
FreshActorName == IF \E a \in ActorName : actors[a] = null 
                  THEN {CHOOSE a \in ActorName : actors[a] = null}
                  ELSE {}

(* 
pdom(S) is the domain over which the partial function S is defined. 
*)
pdom(S) == { a \in DOMAIN S : S[a] # null }

(* 
The following functions are shorthand for manipulating bags of messages: *)
put(bag, x)        == bag (+) SetToBag({x})  \* Adds x to the bag.
remove(bag, x)     == bag (-) SetToBag({x})  \* Removes x from the bag.
replace(bag, x, y) == put(remove(bag, x), y) \* Replaces x with y in the bag.

(* 
We define the following sets to range over created, busy, idle, halted,
and sticky actors. *)
Actors       == pdom(actors)
BusyActors   == { a \in Actors : actors[a].status = "busy" }
IdleActors   == { a \in Actors : actors[a].status = "idle" }
HaltedActors == { a \in Actors : actors[a].status = "halted" }
StickyActors == { a \in Actors : actors[a].isSticky }

(* 
A message is admissible if it is not already admitted and the origin
node is not shunned by the destination node. *)
AdmissibleMsgs == { m \in BagToSet(msgs) : 
                        /\ ~m.admitted 
                        /\ ~shunned[m.origin, location[m.target]] }
AdmittedMsgs   == { m \in BagToSet(msgs) : m.admitted }

(* 
deliverableTo(a) is the set of messages to an actor `a' is the set of messages `m' for which `a' is 
the target, and `m' has either been admitted or can be admitted. In-flight messages
from shunned nodes are excluded from this set. 

An actor's acquaintances acqs(a) are the set of actors for which it has references.

An actor's inverse acquaintances iacqs(b) are the actors for which it is an acquaintance.

An actor's potential acquaintances pacqs(a) are the actors for which it has a reference or
can possibly receive a reference due to an undelivered message.

An actor's potential inverse acquaintances piacqs(a) are the actors for which it is a 
potential acquaintance.
*)
deliverableTo(a) == { m \in BagToSet(msgs) : /\ m.target = a 
                                             /\ (m.admitted \/ m \in AdmissibleMsgs) }
acqs(a)   == { b \in ActorName : actors[a].active[b] > 0 }
iacqs(b)  == { a \in Actors : b \in acqs(a) }
pacqs(a)  == { b \in ActorName : b \in acqs(a) \/ \E m \in deliverableTo(a) : b \in m.refs }
piacqs(b) == { a \in Actors : b \in pacqs(a) }

admittedMsgsTo(a) == { m \in deliverableTo(a) : m.admitted }
monitoredBy(b)    == actors[b].monitored

(* 
An actor is blocked if it is idle and has no deliverable messages. Otherwise, the
actor is unblocked. *)
Blocked   == { a \in IdleActors : deliverableTo(a) = {} }
Unblocked == Actors \ Blocked

(* 
The exiled nodes are the largest nontrivial faction where every non-exiled
node has shunned every exiled node. Likewise, a faction of nodes G is 
apparently exiled if every node outside of G has taken an ingress snapshot 
in which every node of G is shunned.  *)
ExiledNodes == 
    LargestSubset(NodeID, LAMBDA G:
        /\ G # NodeID
        /\ \A N1 \in G, N2 \in NodeID \ G: shunned[N1,N2]
    )
NonExiledNodes  == NodeID \ ExiledNodes
ExiledActors    == { a \in Actors : location[a] \in ExiledNodes }
FailedActors    == HaltedActors \union ExiledActors
HealthyActors   == Actors \ FailedActors

ShunnedBy(N2)    == { N1 \in NodeID : shunned[N1,N2] }
ShunnableBy(N1)  == (NodeID \ {N1}) \ ShunnedBy(N1)
NeitherShuns(N1) == { N2 \in NodeID : ~shunned[N1, N2] /\ ~shunned[N2, N1] }

-----------------------------------------------------------------------------
(* TRANSITIONS *)

(* 
This section of the model declares the events that may occur in an execution
and how each event updates the configuration. 

The events of an execution are defined as "actions" in TLA+:

"An action represents a relation between old states 
and new states, where the unprimed variables refer to the old state and the 
primed variables refer to the new state. Thus, y = x' + 1 is the relation asserting 
that the value of y in the old state is one greater than the value of x in the new state. 
An atomic operation of a concurrent program will be represented in TLA by an action."
[Lamport 1994]

We first define each event (`Idle', Spawn, Send, ...) individually, and then define
the Next relation which specifies all the possible transitions a configuration can
take.
*)

Idle(a) ==
    (* A busy actor `a' can become idle by changing its status.

       The notation below states that, as a result of the Idle event, the
       `actors' component of the configuration will change and the remaining
       components do not change.
      
       Specifically, the new value `actors' is identical to the old value, 
       except that the status of actor `a' is set to "idle". *)
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,location,shunned>>

Spawn(a,b,N) == 
    (* A busy actor `a' can spawn a fresh actor `b' onto a non-shunned node. *)
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1, \* The parent obtains a reference to the child.
        ![b] = [ 
            status    |-> "busy",                               \* The child is busy,
            isSticky  |-> FALSE,                                \* not sticky,
            active    |-> (b :> 1) @@ [c \in ActorName |-> 0],  \* has a reference to itself,
            monitored |-> {}                                    \* and monitors nobody.
        ]]
    /\ location' = [location EXCEPT ![b] = N]
    /\ UNCHANGED <<msgs,shunned>>

Deactivate(a,b) ==
    (* A busy actor can remove references from its state. *)
    /\ actors' = [actors EXCEPT ![a].active[b] = 0]
    /\ UNCHANGED <<location,msgs,shunned>>

Send(a,b,m) ==
    (* A busy actor can send messages to its acquaintances. *)
    /\ msgs' = put(msgs, m) \* Add message `m' to the msgs bag.
    /\ UNCHANGED <<actors,location,shunned>>

Receive(a,m) ==
    (* An idle actor can receive a message, becoming busy. *)
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ msgs' = remove(msgs, m) \* Remove `m' from the msgs bag.
    /\ UNCHANGED <<location,shunned>>

Halt(a) ==
    (* Busy actors can halt. *)
    /\ actors' = [actors EXCEPT ![a].status = "halted"]
    /\ UNCHANGED <<location,msgs,shunned>>

Monitor(a,b) ==
    (* Busy actors can monitor their acquaintances. *)
    /\ actors' = [actors EXCEPT ![a].monitored = @ \union {b}] \* Add b to the monitored set.
    /\ UNCHANGED <<location,msgs,shunned>>

Notify(a,b) ==
    (* Monitoring actors can become "busy" after the actors they monitor fail. *)
    /\ actors' = [actors EXCEPT ![a].status = "busy", ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<location,msgs,shunned>>

Unmonitor(a,b) ==
    (* Busy actors can stop monitoring actors. *)
    /\ actors' = [actors EXCEPT ![a].monitored = @ \ {b}]
    /\ UNCHANGED <<location,msgs,shunned>>

Register(a) ==
    (* Actors can register as sticky to spontaneously be awoken from "idle" state. *)
    /\ actors' = [actors EXCEPT ![a].isSticky = TRUE]
    /\ UNCHANGED <<location,msgs,shunned>>

Wakeup(a) ==
    (* A sticky actor can be awoken. *)
    /\ actors' = [actors EXCEPT ![a].status = "busy"]
    /\ UNCHANGED <<location,msgs,shunned>>

Unregister(a) ==
    (* Actors can unregister as sticky. *)
    /\ actors' = [actors EXCEPT ![a].isSticky = FALSE]
    /\ UNCHANGED <<location,msgs,shunned>>

Admit(m) ==
    (* In-flight messages can be admitted. If node N1 shuns node N2, then messages
    from N1 can no longer be delivered to N2 unless they are already admitted. *)
    /\ msgs' = replace(msgs, m, [m EXCEPT !.admitted = TRUE])
    /\ UNCHANGED <<actors,location,shunned>>

Drop(m) == 
    (* Any message can spontaneously be dropped. *)
    /\ msgs' = remove(msgs, m)
    /\ UNCHANGED <<actors,location,shunned>>

Shun(N1, N2) ==
    (* A non-exiled node can shun another node. *)
    /\ shunned' = [shunned EXCEPT ![N1,N2] = TRUE]
    /\ UNCHANGED <<actors,msgs,location>>

(* 
The following Exile event can safely be used in place of the Shun event to
simplify reasoning and reduce the model checking state space. This is safe because, 
for any execution in which a group of nodes G1 all shuns another group G2,
there is an equivalent execution in which all `Shun' events happen successively.  *)
Exile(G1, G2) ==
    /\ shunned' = [N1 \in G1, N2 \in G2 |-> TRUE] @@ shunned
    /\ UNCHANGED <<actors,msgs,location>>

-----------------------------------------------------------------------------

(* 
Init defines the initial configuration, choosing an arbitrary name and 
location for the initial actor. *)
Init == InitialConfiguration(
    CHOOSE a \in ActorName: TRUE, \* Choose an arbitrary name for the initial actor.
    CHOOSE N \in NodeID: TRUE     \* Choose an arbitrary location for the actor.
)

(* 
Next defines the transition relation on configurations, defined as a TLA action,
such that configuration K1 can atomically transition to configuration K2 if the 
relation (K1)Next(K2) holds.

For example, let K1 be a configuration with two busy actors `a,b' and an idle actor
`c'. Then K1 can transition to a configuration K2 in which `a' is busy and `b,c'
are idle, because of the Idle transition below.
*)
Next ==
    \/ \E a \in BusyActors \ ExiledActors: Idle(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in FreshActorName: 
       \E N \in NeitherShuns(location[a]): Spawn(a,b,N)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[origin |-> location[a], 
                  admitted |-> location[b] = location[a], 
                  target |-> b, 
                  refs |-> refs])
    \/ \E a \in IdleActors \ ExiledActors: \E m \in admittedMsgsTo(a): Receive(a,m)
    \/ \E a \in BusyActors \ ExiledActors: Halt(a)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in acqs(a): Monitor(a,b)
    \/ \E a \in IdleActors \ ExiledActors: \E b \in FailedActors \intersect monitoredBy(a): 
        Notify(a,b)
    \/ \E a \in BusyActors \ ExiledActors: \E b \in monitoredBy(a): Unmonitor(a,b)
    \/ \E a \in (BusyActors \ StickyActors) \ ExiledActors: Register(a)
    \/ \E a \in (IdleActors \intersect StickyActors) \ ExiledActors: Wakeup(a)
    \/ \E a \in (BusyActors \intersect StickyActors) \ ExiledActors: Unregister(a)
    \/ \E m \in AdmissibleMsgs: location[m.target] \notin ExiledNodes /\ Admit(m)
    \/ \E m \in AdmissibleMsgs \union AdmittedMsgs: location[m.target] \notin ExiledNodes /\ Drop(m)
    \/ \E N2 \in NonExiledNodes: \E N1 \in ShunnableBy(N2): Shun(N1,N2)
    \* The Shun rule above can be replaced with the following Exile rule without
    \* loss of generality for faster model checking:
    \* \/ \E G \in SUBSET NonExiledNodes: G # {} /\ G # NonExiledNodes /\ Exile(G, NonExiledNodes \ G)

-----------------------------------------------------------------------------
(* GARBAGE *)

(* 
An actor is potentially unblocked if it is busy or can become busy. 
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
            
(* 
An actor is potentially unblocked if it is potentially unblocked up-to-a-fault
or it monitors any remote actor. This is because remote actors can always
become exiled, causing the monitoring actor to be notified. *)
isPotentiallyUnblocked(S) ==
    /\ isPotentiallyUnblockedUpToAFault(S)
    /\ \A a \in Actors, b \in HealthyActors :
        /\ (a \in monitoredBy(b) /\ location[a] # location[b] => b \in S)

(* 
An actor is quiescent if it is not potentially unblocked. Likewise for 
quiescence up-to-a-fault. *)
PotentiallyUnblockedUpToAFault == 
    CHOOSE S \in SUBSET HealthyActors : isPotentiallyUnblockedUpToAFault(S)
QuiescentUpToAFault == Actors \ PotentiallyUnblockedUpToAFault

PotentiallyUnblocked == 
    CHOOSE S \in SUBSET HealthyActors : isPotentiallyUnblocked(S)
Quiescent == Actors \ PotentiallyUnblocked

(* 
Both definitions characterize a subset of the idle actors. The difference between the
definitions is that quiescence up-to-a-fault is only a stable property in non-faulty
executions. *)
QuiescentImpliesIdle == Quiescent \subseteq (IdleActors \union FailedActors)
QuiescentUpToAFaultImpliesIdle == QuiescentUpToAFault \subseteq (IdleActors \union FailedActors)

====