---- MODULE Mattern ----
EXTENDS Integers, FiniteSets, Bags, TLC

(*
NOTES ON THIS MODULE

- The search space is unbounded. To perform bounded search,
  run TLC with the argument `-dfid N` where `N` is the 
  search bound.
*)

CONSTANT Actor   \* The names of participating actors

VARIABLE 
    actorState,  \* actorState[a] is the state of actor `a'.
    msgs,        \* msgs is the set of all undelivered messages.
    snapshots    \* snapshots[a] is a snapshot of some actor's state

Perms == Permutations(Actor)
-----------------------------------------------------------------------------
Messages ==
  [sender: Actor, target: Actor, id: Nat] 
  (* A message is uniquely identified by the name of the sender, the name of the
  target, and the count of how many messages the sender sent to the target so 
  far. *)

ActorState ==
    [ status   : {"busy", "idle"},
      sent     : [Actor -> Nat],
      received : Nat
    ]

Null == [ type: {"null"} ]
null == [type |-> "null"]

TypeOK == 
  /\ actorState \in [Actor -> ActorState]
  /\ snapshots \in [Actor -> ActorState \cup Null]
  /\ msgs \subseteq Messages
        
Init ==   
    /\ actorState = 
        [a \in Actor |-> 
            [status   |-> "busy", 
             sent     |-> [b \in Actor |-> 0],
             received |-> 0
            ]]
    /\ snapshots = [a \in Actor |-> null]
    /\ msgs = {}

-----------------------------------------------------------------------------

blocked(a) == 
    /\ actorState[a].status = "idle"
    /\ { m \in msgs : m.target = a } = {}
    
allQuiescent == \A a \in Actor : blocked(a)

-----------------------------------------------------------------------------
Idle(a) ==
    /\ actorState[a].status = "busy"
    /\ actorState' = [actorState EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Send(a) == 
    /\ actorState[a].status = "busy"
    /\ \E b \in Actor :
        LET n == actorState[a].sent[b] IN
        /\ actorState' = [actorState EXCEPT ![a].sent[b] = (n + 1)]
        /\ msgs' = msgs \cup {[sender |-> a, target |-> b, id |-> (n + 1)]}
        /\ UNCHANGED <<snapshots>>

Receive(a) ==
    /\ actorState[a].status = "idle"
    /\ \E m \in msgs :
        LET n == actorState[a].received IN
        /\ m.target = a 
        /\ actorState' = [actorState EXCEPT 
            ![a].received = (n+1), 
            ![a].status = "busy"]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED <<snapshots>>

Snapshot(a) ==
    /\ snapshots[a] = null
    /\ snapshots' = [snapshots EXCEPT ![a] = actorState[a]]
    /\ UNCHANGED <<msgs,actorState>>

Next == \E a \in Actor : 
    (Idle(a) \/ Send(a) \/ Receive(a) \/ Snapshot(a))

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

AppearsBlocked(a) ==
    (\A b \in Actor : snapshots[b] # null) /\
    snapshots[a].status = "idle" /\
    LET 
        received == snapshots[a].received
        sent == MapSum([ b \in Actor |-> snapshots[b].sent[a] ])
    IN received = sent

Safety ==
    (\A a \in Actor : AppearsBlocked(a)) =>
    allQuiescent

-----------------------------------------------------------------------------

====