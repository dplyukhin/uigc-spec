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

(* Assuming map1 has type [D1 -> Nat] and map2 has type [D2 -> Nat] where D2
   is a subset of D1, this operator increments every map1[a] by the value of map2[a]. *)
map1 ++ map2 == [ a \in DOMAIN map1 |-> IF a \in DOMAIN map2 
                                        THEN map1[a] + map2[a] 
                                        ELSE map1[a] ]

(* Convenient notation for adding and removing from bags of undelivered messages. *)
put(bag, x)    == bag (+) SetToBag({x})
remove(bag, x) == bag (-) SetToBag({x})


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

InitialActorState == [
    status      |-> "busy", 
    sendCount   |-> [b \in ActorName |-> 0],
    recvCount   |-> 0,
    active      |-> [b \in ActorName |-> 0],
    deactivated |-> [b \in ActorName |-> 0],
    created     |-> [b, c \in ActorName |-> 0]
]
        
(* In the initial configuration, there is one busy actor with a reference
   to itself. *)
Init ==   
    LET actor == CHOOSE a \in ActorName: TRUE 
        state == [ InitialActorState EXCEPT 
                   !.active  = @ ++ (actor :> 1),
                   !.created = @ ++ (<<actor, actor>> :> 1)
                 ]
    IN
    /\ msgs = EmptyBag
    /\ actors = [a \in ActorName |-> IF a = actor THEN state ELSE null ]
    /\ snapshots = [a \in ActorName |-> null]

-----------------------------------------------------------------------------

CreatedActors  == { a \in ActorName     : actors[a] # null }
BusyActors     == { a \in CreatedActors : actors[a].status = "busy" }
IdleActors     == { a \in CreatedActors : actors[a].status = "idle" }

(* TLA-specific mechanism for deterministically picking a fresh actor name.
   If ActorName is a finite set and all names have been exhausted, this operator
   produces the empty set. *)
FreshActorName == IF \E a \in ActorName : actors[a] = null 
                  THEN {CHOOSE a \in ActorName : actors[a] = null}
                  ELSE {}

msgsTo(a)  == { m \in BagToSet(msgs) : m.target = a }
acqs(a)    == { b \in ActorName : actors[a].active[b] > 0 }
pacqs(a)   == { b \in ActorName : b \in acqs(a) \/ \E m \in msgsTo(a) : b \in m.refs }
piacqs(b)  == { a \in CreatedActors : b \in pacqs(a) }

-----------------------------------------------------------------------------
Idle ==
    \E a \in BusyActors :
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Spawn == 
    \E a \in BusyActors : \E b \in FreshActorName :
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,                                 \* Parent has a reference to the child.
        ![b] = [ 
            InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),                      \* Child has a reference to itself.
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1) \* Child knows about both references.
        ]
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
    /\ actors' = [actors EXCEPT 
        ![a].sendCount[b] = @ + 1,
        ![a].created = @ ++ [ <<x,y>> \in {b} \X refs |-> 1 ]
        ]
    (* Add this message to the msgs bag. *)
    /\ msgs' = put(msgs, [target |-> b, refs |-> refs])
    /\ UNCHANGED <<snapshots>>

Receive ==
    \E a \in IdleActors : \E m \in msgsTo(a) :
    /\ actors' = [actors EXCEPT 
        ![a].active = @ ++ [c \in m.refs |-> 1],
        ![a].recvCount = @ + 1, 
        ![a].status = "busy"]
    (* Remove m from the msgs bag. *)
    /\ msgs' = remove(msgs, m)
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

Blocked(a) == actors[a].status = "idle" /\ msgsTo(a) = {}

RECURSIVE Quiescent(_)
Quiescent(b) == Blocked(b) /\ \A a \in piacqs(b) \ {b} : Quiescent(a)

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