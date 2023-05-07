---- MODULE Mattern ----
EXTENDS Integers, FiniteSets, Bags, TLC

CONSTANT Actor,       \* The names of participating actors
  BOUND \* maximum number of steps to take

VARIABLE 
    actorState,  \* actorState[a] is the state of actor `a'.
    msgs,         \* msgs is the set of all undelivered messages.
    numSteps

Perms == Permutations(Actor)
-----------------------------------------------------------------------------
Messages ==
  [sender: Actor, target: Actor, id: Nat] 
  (* A message is uniquely identified by the name of the sender, the name of the
  target, and the count of how many messages the sender sent to the target so 
  far. *)

TypeOK == 
  /\ actorState \in [Actor -> [ status   : {"busy", "idle"},
                                sent     : [Actor -> Nat],
                                received : Nat
                              ]
                    ]
  /\ msgs \subseteq Messages
  /\ numSteps \in Nat
        
Init ==   
    /\ actorState = 
        [a \in Actor |-> 
            [status   |-> "busy", 
             sent     |-> [b \in Actor |-> 0],
             received |-> 0
            ]]
    /\ msgs = {}
    /\ numSteps = 0

-----------------------------------------------------------------------------
\*allQuiescent == \A a \in Actor : actorState[a]
-----------------------------------------------------------------------------
Idle(a) ==
    /\ actorState[a].status = "busy"
    /\ actorState' = [actorState EXCEPT ![a].status = "idle"]
    /\ UNCHANGED msgs

Send(a) == 
    /\ actorState[a].status = "busy"
    /\ \E b \in Actor :
        LET n == actorState[a].sent[b] IN
        /\ actorState' = [actorState EXCEPT ![a].sent[b] = (n + 1)]
        /\ msgs' = msgs \cup {[sender |-> a, target |-> b, id |-> (n + 1)]}

Receive(a) ==
    /\ actorState[a].status = "idle"
    /\ \E m \in msgs :
        LET n == actorState[a].received IN
        /\ m.target = a 
        /\ actorState' = [actorState EXCEPT 
            ![a].received = (n+1), 
            ![a].status = "busy"]
        /\ msgs' = msgs \ {m}

Next == \E a \in Actor : 
    numSteps < BOUND /\ numSteps' = numSteps + 1 /\
    (Idle(a) \/ Send(a) \/ Receive(a))

-----------------------------------------------------------------------------
RECURSIVE _MapSum(_, _)
_MapSum(dom, map) == IF dom = {} THEN 0 ELSE 
    LET x == CHOOSE x \in dom: TRUE IN
    map[x] + _MapSum(dom \ {x}, map)
MapSum(map) == _MapSum(DOMAIN map, map)

MessagesConsistent(a) == 
    LET 
        received == actorState[a].received
        sent == MapSum([ b \in Actor |-> actorState[b].sent[a] ])
        undelivered == Cardinality({ m \in msgs : m.target = a })
    IN received + undelivered = sent

AllMessagesConsistent == 
    \A a \in Actor : MessagesConsistent(a)

\* QuiescentConsistent == If quiescent then no messages
-----------------------------------------------------------------------------

====