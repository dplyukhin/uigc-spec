---- MODULE Dynamic ----
EXTENDS Integers, FiniteSets, Bags, TLC

(*
NOTES ON THIS MODULE

- Exhaustive search is intractable for any execution long
  enough to manifest a bug. So use '-simulate' to generate
  random executions.
- If you find a bug, you want to try and find a small witness.
  Best bet is to use '-simulate -depth N' to only search executions
  of length up to N.
*)

CONSTANT
    ActorName    \* The names of participating actors.

VARIABLE 
    actors,      \* actors[a] is the state of actor `a'.
    msgs,        \* msgs is a bag of all `^undelivered^' messages.
    snapshots    \* snapshots[a] is a snapshot of some actor's state.

-----------------------------------------------------------------------------
(* A message consists of (a) the name of the destination actor, and (b) a set
   of references to other actors. Any other data a message could contain is 
   irrelevant for our purposes. *)
Message == [target: ActorName, refs : SUBSET ActorName] 

ActorState ==
    [ status      : {"busy", "idle"},
      sendCount   : [ActorName -> Nat],
      recvCount   : Nat,
      active      : [ActorName -> Nat],
      deactivated : [ActorName -> Nat],
      created     : [ActorName \X ActorName -> Nat]
    ]

Null == [ type: {"null"} ]
null == [type |-> "null"]

TypeOK == 
  /\ actors \in [ActorName -> ActorState \cup Null]
  /\ snapshots \in [ActorName -> ActorState \cup Null]
  /\ BagToSet(msgs) \subseteq Message

initialState(self, parent) ==
    [
        status   |-> "busy", 
        sendCount     |-> [b \in ActorName |-> 0],
        recvCount |-> 0,
        active   |-> [b \in ActorName |-> IF b = self THEN 1 ELSE 0],
        deactivated |-> [b \in ActorName |-> 0],
        created  |-> [<<a,b>> \in ActorName \X ActorName |-> 
            IF (a = self \/ a = parent) /\ b = self THEN 1 ELSE 0]
    ]
        
(* Initially, some actor exists and the rest do not. *)
Init ==   
    LET initialActor == CHOOSE a \in ActorName: TRUE IN
    /\ actors = [a \in ActorName |-> 
            IF a = initialActor THEN initialState(a, null)
            ELSE null
        ]
    /\ snapshots = [a \in ActorName |-> null]
    /\ msgs = EmptyBag

-----------------------------------------------------------------------------

CreatedActors == { a \in ActorName : actors[a] # null }

-----------------------------------------------------------------------------
Idle(a) ==
    /\ actors[a] # null
    /\ actors[a].status = "busy"
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Spawn(a) == 
    /\ actors[a] # null
    /\ actors[a].status = "busy" 
    /\ \E b \in ActorName : actors[b] = null
    /\ LET b == CHOOSE b \in ActorName : actors[b] = null IN
        /\ actors' = [actors EXCEPT 
            ![a].active[b] = 1,      \* Add child ref to parent state
            ![b] = initialState(b,a) 
            ]
        /\ UNCHANGED <<snapshots,msgs>>

Deactivate(a) ==
    /\ actors[a] # null
    /\ actors[a].status = "busy"
    /\ \E b \in ActorName :
        LET active == actors[a].active[b] 
            deactivated == actors[a].deactivated[b] 
        IN 
        /\ active > 0
        /\ actors' = [actors EXCEPT 
            ![a].deactivated[b] = deactivated + active,
            ![a].active[b] = 0
            ]
        /\ UNCHANGED <<msgs,snapshots>>

Send(a) == 
    /\ actors[a] # null
    /\ actors[a].status = "busy"
    /\ \E b \in ActorName : 
       actors[a].active[b] > 0 /\
       \E refs \in SUBSET { c \in ActorName : actors[a].active[c] > 0 } :
        LET n == actors[a].sendCount[b] 
            created == [ <<x,y>> \in ActorName \X ActorName |-> 
                IF x = b /\ y \in refs 
                THEN actors[a].created[<<x,y>>] + 1
                ELSE actors[a].created[<<x,y>>]
                ]
        IN
        /\ actors' = [actors EXCEPT 
            ![a].sendCount[b] = (n + 1),
            ![a].created = created
            ]
        (* Add this message to the msgs bag. *)
        /\ msgs' = msgs (+) SetToBag({[target |-> b, refs |-> refs]})
        /\ UNCHANGED <<snapshots>>

Receive(a) ==
    /\ actors[a] # null
    /\ actors[a].status = "idle"
    /\ \E m \in BagToSet(msgs) :
        /\ m.target = a 
        /\ LET n == actors[a].recvCount 
               active == [c \in ActorName |-> 
                    IF c \in m.refs 
                    THEN actors[a].active[c] + 1
                    ELSE actors[a].active[c]]
           IN
            /\ actors' = [actors EXCEPT 
                ![a].active = active,
                ![a].recvCount = (n+1), 
                ![a].status = "busy"]
            (* Remove m from the msgs bag. *)
            /\ msgs' = msgs (-) SetToBag({m})
            /\ UNCHANGED <<snapshots>>

Snapshot(a) ==
    /\ actors[a] # null
    /\ snapshots[a] = null
    /\ snapshots' = [snapshots EXCEPT ![a] = actors[a]]
    /\ UNCHANGED <<msgs,actors>>

Next == \E a \in ActorName : 
    Idle(a) \/ Spawn(a) \/ Deactivate(a) \/ Send(a) \/ Receive(a) \/ 
    Snapshot(a)

-----------------------------------------------------------------------------

RECURSIVE _MapSum(_, _)
_MapSum(dom, map) == IF dom = {} THEN 0 ELSE 
    LET x == CHOOSE x \in dom: TRUE IN
    map[x] + _MapSum(dom \ {x}, map)
MapSum(map) == _MapSum(DOMAIN map, map)

LOCAL BagSum(B, F(_)) ==
    CopiesIn(1, BagOfAll(F, B))

MessagesConsistent(a) == 
    LET 
        recvCount == actors[a].recvCount
        sendCount == MapSum([ b \in CreatedActors |-> actors[b].sendCount[a]])
        undelivered == BagSum(msgs, LAMBDA m : IF m.target = a THEN 1 ELSE 0)
    IN recvCount + undelivered = sendCount

AllMessagesConsistent == 
    \A a \in CreatedActors : MessagesConsistent(a)

Blocked(a) == 
    /\ actors[a].status = "idle"
    /\ BagSum(msgs, LAMBDA m : IF m.target = a THEN 1 ELSE 0) = 0

PotentialAcquaintance(a,b) ==
    \/ actors[a].active[b] > 0
    \/ \E m \in BagToSet(msgs) : 
        /\ m.target = a
        /\ b \in m.refs

RECURSIVE Quiescent(_)
Quiescent(b) ==
    /\ Blocked(b)
    /\ \A a \in CreatedActors \ {b} : 
        PotentialAcquaintance(a,b) =>
        Quiescent(a)

ActorsOf(Q) == { a \in ActorName : Q[a] # null }

EverAcquainted(b,c,Q) ==
    \E a \in ActorsOf(Q) : Q[a].created[<<b,c>>] > 0

AppearsAcquainted(b,c,Q) ==
    LET created == MapSum([ a \in ActorsOf(Q) |-> 
            Q[a].created[<<b,c>>]])
        deactivated == Q[b].deactivated[c]
    IN created > deactivated

AppearsBlocked(b,Q) ==
    Q[b].status = "idle" /\
    LET iacqs == { a \in ActorsOf(Q) : EverAcquainted(a,b,Q) }
        sendCount == MapSum([ a \in iacqs |-> Q[a].sendCount[b] ])
        recvCount == Q[b].recvCount
    IN sendCount = recvCount

RECURSIVE AppearsQuiescent(_,_)
AppearsQuiescent(b, Q) ==
    /\ AppearsBlocked(b,Q)
    /\ \A a \in ActorsOf(Q) \ {b} :
        AppearsAcquainted(a,b,Q) =>
        AppearsQuiescent(a,Q)

UpwardClosed(Q) ==
    \A a, b, c \in ActorName : 
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