---- MODULE Dynamic ----
EXTENDS Integers, FiniteSets, Bags, TLC

(*
NOTES ON THIS MODULE

- Exhaustive search is intractable for any execution long
  enough to manifest a bug. So use `-simulate` to generate
  random executions.
- If you find a bug, you want to try and find a small witness.
  Best bet is to use `-simulate -depth N` to only search executions
  of length up to `N`.
*)

CONSTANT 
    Actor,  \* The names of participating actors
    MAX_REFS    \* maximum number of refs in a message

VARIABLE 
    actorState,  \* actorState[a] is the state of actor `a'.
    msgs,        \* msgs is the set of all undelivered messages.
    snapshots    \* snapshots[a] is a snapshot of some actor's state

Perms == Permutations(Actor)
-----------------------------------------------------------------------------
Messages ==
  [sender: Actor, target: Actor, id: Nat, refs : SUBSET Actor] 
  (* A message is uniquely identified by the name of the sender, the name of the
  target, and the count of how many messages the sender sent to the target so 
  far. *)

ActorState ==
    [ status   : {"busy", "idle"},
      sent     : [Actor -> Nat],
      received : Nat,
      active      : [Actor -> Nat],
      deactivated : [Actor -> Nat],
      created     : [Actor \X Actor -> Nat]
    ]

Null == [ type: {"null"} ]
null == [type |-> "null"]

TypeOK == 
  /\ actorState \in [Actor -> ActorState \cup Null]
  /\ snapshots \in [Actor -> ActorState \cup Null]
  /\ msgs \subseteq Messages

initialState(self, parent) ==
    [
        status   |-> "busy", 
        sent     |-> [b \in Actor |-> 0],
        received |-> 0,
        active   |-> [b \in Actor |-> IF b = self THEN 1 ELSE 0],
        deactivated |-> [b \in Actor |-> 0],
        created  |-> [<<a,b>> \in Actor \X Actor |-> 
            IF (a = self \/ a = parent) /\ b = self THEN 1 ELSE 0]
    ]
        
(* Initially, some actor exists and the rest do not. *)
Init ==   
    LET initialActor == CHOOSE a \in Actor: TRUE IN
    /\ actorState = [a \in Actor |-> 
            IF a = initialActor THEN initialState(a, null)
            ELSE null
        ]
    /\ snapshots = [a \in Actor |-> null]
    /\ msgs = {}

-----------------------------------------------------------------------------

CreatedActors == { a \in Actor : actorState[a] # null }

-----------------------------------------------------------------------------
Idle(a) ==
    /\ actorState[a].status = "busy"
    /\ actorState' = [actorState EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Spawn(a) == 
    /\ actorState[a].status = "busy"
    /\ \E b \in Actor :
        /\ actorState[b] = null
        /\ actorState' = [actorState EXCEPT 
            ![a].active[b] = 1,      \* Add child ref to parent state
            ![b] = initialState(a,b) 
            ]
        /\ UNCHANGED <<snapshots,msgs>>

Deactivate(a) ==
    /\ actorState[a].status = "busy"
    /\ \E b \in Actor :
        LET active == actorState[a].active[b] 
            deactivated == actorState[a].deactivated[b] 
        IN 
        /\ active > 0
        /\ actorState' = [actorState EXCEPT 
            ![a].deactivated[b] = deactivated + active,
            ![a].active[b] = 0
            ]
        /\ UNCHANGED <<msgs,snapshots>>

Send(a) == 
    /\ actorState[a].status = "busy"
    /\ \E b \in Actor : 
       actorState[a].active[b] > 0 /\
       \E refs \in SUBSET { c \in Actor : actorState[a].active[c] > 0 } :
        Cardinality(refs) <= MAX_REFS /\
        LET n == actorState[a].sent[b] 
            created == [ <<x,y>> \in Actor \X Actor |-> 
                IF x = b /\ y \in refs 
                THEN actorState[a].created[<<x,y>>] + 1
                ELSE actorState[a].created[<<x,y>>]
                ]
        IN
        /\ actorState' = [actorState EXCEPT 
            ![a].sent[b] = (n + 1),
            ![a].created = created
            ]
        /\ msgs' = msgs \cup {[sender |-> a, target |-> b, id |-> (n + 1), refs |-> refs]}
        /\ UNCHANGED <<snapshots>>

Receive(a) ==
    /\ actorState[a].status = "idle"
    /\ \E m \in msgs :
        /\ m.target = a 
        /\ LET n == actorState[a].received 
               active == [c \in Actor |-> 
                    IF c \in m.refs 
                    THEN actorState[a].active[c] + 1
                    ELSE actorState[a].active[c] + 1]
           IN
            /\ actorState' = [actorState EXCEPT 
                ![a].active = active,
                ![a].received = (n+1), 
                ![a].status = "busy"]
            /\ msgs' = msgs \ {m}
            /\ UNCHANGED <<snapshots>>

Snapshot(a) ==
    /\ snapshots[a] = null
    /\ snapshots' = [snapshots EXCEPT ![a] = actorState[a]]
    /\ UNCHANGED <<msgs,actorState>>

Next == \E a \in CreatedActors : 
    (Idle(a) \/ Spawn(a) \/ Deactivate(a) \/ Send(a) \/ Receive(a) \/ 
     Snapshot(a))

-----------------------------------------------------------------------------

RECURSIVE _MapSum(_, _)
_MapSum(dom, map) == IF dom = {} THEN 0 ELSE 
    LET x == CHOOSE x \in dom: TRUE IN
    map[x] + _MapSum(dom \ {x}, map)
MapSum(map) == _MapSum(DOMAIN map, map)

MessagesConsistent(a) == 
    LET 
        received == actorState[a].received
        sent == MapSum([ b \in CreatedActors |-> actorState[b].sent[a]])
        undelivered == Cardinality({ m \in msgs : m.target = a })
    IN received + undelivered = sent

AllMessagesConsistent == 
    \A a \in CreatedActors : MessagesConsistent(a)

Blocked(a) == 
    /\ actorState[a].status = "idle"
    /\ { m \in msgs : m.target = a } = {}

PotentialAcquaintance(a,b) ==
    \/ actorState[a].active[b] > 0
    \/ \E m \in msgs : 
        /\ m.target = a
        /\ b \in m.refs

RECURSIVE Quiescent(_)
Quiescent(b) ==
    /\ Blocked(b)
    /\ \A a \in Actor : 
        PotentialAcquaintance(a,b) =>
        Quiescent(a)

ActorsOf(Q) == { a \in Actor : Q[a] # null }

AppearsAcquainted(b,c,Q) ==
    LET created == MapSum([ a \in ActorsOf(Q) |-> 
            Q[a].created[<<b,c>>]])
        deactivated == Q[b].active[c]
    IN created > deactivated

AppearsBlocked(b,Q) ==
    Q[b].status = "idle" /\
    LET piacqs == { a \in ActorsOf(Q) : AppearsAcquainted(a,b,Q) }
        sent == MapSum([ a \in piacqs |-> Q[a].sent[b] ])
        received == Q[b].received
    IN sent = received

RECURSIVE AppearsQuiescent(_,_)
AppearsQuiescent(b, Q) ==
    /\ AppearsBlocked(b,Q)
    /\ \A a \in ActorsOf(Q) :
        AppearsAcquainted(a,b,Q) =>
        AppearsQuiescent(b,Q)

UpwardClosed(Q) ==
    \A a, b, c \in Actor : 
    /\ Q[a] # null 
    /\ Q[c] # null
    /\ Q[a].created[<<b,c>>] > 0
    => Q[b] # null

Safety ==
    UpwardClosed(snapshots)
    => \A a \in ActorsOf(snapshots) :
        AppearsQuiescent(a, snapshots) => Quiescent(a)

-----------------------------------------------------------------------------

====