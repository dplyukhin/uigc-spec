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

(* `null' is an arbitrary value used to signal that an expression was undefined. *)
CONSTANT null

-----------------------------------------------------------------------------
(* A message consists of (a) the name of the destination actor, and (b) a set
   of references to other actors. Any other data a message could contain is 
   irrelevant for our purposes. *)
Message == [target: ActorName, refs : SUBSET ActorName] 

(*
ActorState represents the GC-relevant state of an actor.
- status indicates whether the actor is currently processing a message.
- recvCount is the number of messages that this actor has received.
- sendCount[b] is the number of messages this actor has sent to b.
- active[b] is the number of active references to b in the state.
- deactivated[b] is the number of references to b that have been deactivated.
- created[b,c] is the number of references to c that have been sent to b.
*)
ActorState == [ 
    status      : {"busy", "idle"},
    recvCount   : Nat,
    sendCount   : [ActorName -> Nat],
    active      : [ActorName -> Nat],
    deactivated : [ActorName -> Nat],
    created     : [ActorName \X ActorName -> Nat]
]

(*
- actors is a partial mapping from actor names to actor states.
- snapshots is also a partial mapping from actor names to actor states.
- msgs is a bag of messages.
*)
TypeOK == 
  /\ actors         \in [ActorName -> ActorState \cup {null}]
  /\ snapshots      \in [ActorName -> ActorState \cup {null}]
  /\ BagToSet(msgs) \subseteq Message

initialState(self, parent) == [
    status      |-> "busy", 
    sendCount   |-> [b \in ActorName |-> 0],
    recvCount   |-> 0,
    active      |-> [b \in ActorName |-> IF b = self THEN 1 ELSE 0],
    deactivated |-> [b \in ActorName |-> 0],
    created     |-> [<<a,b>> \in ActorName \X ActorName |-> 
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

CreatedActors  == { a \in ActorName : actors[a] # null }
BusyActors     == { a \in CreatedActors : actors[a].status = "busy" }
IdleActors     == { a \in CreatedActors : actors[a].status = "idle" }

FreshActorName == IF \E a \in ActorName : actors[a] = null 
                  THEN {CHOOSE a \in ActorName : actors[a] = null}
                  ELSE {}

acqs(a) == { b \in ActorName : actors[a].active[b] > 0 }

-----------------------------------------------------------------------------
Idle ==
    \E a \in BusyActors :
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,      \* Add child ref to parent state
        ![b] = initialState(b,a) 
        ]
    /\ UNCHANGED <<snapshots,msgs>>

Deactivate ==
    \E a \in BusyActors : \E b \in acqs(a) :
    /\ actors' = [actors EXCEPT 
        ![a].deactivated[b] = @ + actors[a].active[b],
        ![a].active[b] = 0
        ]
    /\ UNCHANGED <<msgs,snapshots>>

Send == 
    \E a \in BusyActors : \E b \in acqs(a) : \E refs \in SUBSET acqs(a) :
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

Receive ==
    \E a \in IdleActors : \E m \in BagToSet(msgs) :
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

Snapshot == 
    \E a \in CreatedActors :
    /\ snapshots[a] = null
    /\ snapshots' = [snapshots EXCEPT ![a] = actors[a]]
    /\ UNCHANGED <<msgs,actors>>

Next == Idle \/ Spawn \/ Deactivate \/ Send \/ Receive \/ Snapshot

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
    \/ b \in acqs(a)
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