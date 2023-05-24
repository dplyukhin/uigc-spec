---- MODULE Common ----
EXTENDS Integers, FiniteSets, Bags, TLC

(* This module defines variables and functions used in all following models. *)

CONSTANT
    ActorName    \* The names of participating actors.

VARIABLE 
    actors,      \* actors[a] is the state of actor `a'.
    msgs,        \* msgs is a bag of all `^undelivered^' messages.
    snapshots    \* snapshots[a] is a snapshot of some actor's state.

(* `null' is an arbitrary value used to signal that an expression was undefined. *)
CONSTANT null

(* A message consists of (a) the name of the destination actor, and (b) a set
   of references to other actors. Any other data a message could contain is 
   irrelevant for our purposes. *)
Message == [target: ActorName, refs : SUBSET ActorName] 

-----------------------------------------------------------------------------

(* Assuming map1 has type [D1 -> Nat] and map2 has type [D2 -> Nat] where D2
   is a subset of D1, this operator increments every map1[a] by the value of map2[a]. *)
map1 ++ map2 == [ a \in DOMAIN map1 |-> IF a \in DOMAIN map2 
                                        THEN map1[a] + map2[a] 
                                        ELSE map1[a] ]

(* Convenient notation for adding and removing from bags of undelivered messages. *)
put(bag, x)    == bag (+) SetToBag({x})
remove(bag, x) == bag (-) SetToBag({x})

(* Computes the sum `^$\sum_{x \in dom(f)} f(x)$^'. *)
RECURSIVE sumOver(_, _)
sumOver(dom, map) == IF dom = {} THEN 0 ELSE 
    LET x == CHOOSE x \in dom: TRUE IN
    map[x] + sumOver(dom \ {x}, map)
sum(map) == sumOver(DOMAIN map, map)

(* The domain over which the partial function S is defined. *)
pdom(S) == { a \in DOMAIN S : S[a] # null }

-----------------------------------------------------------------------------

(* TLA+ mechanism for deterministically picking a fresh actor name.
   If ActorName is a finite set and all names have been exhausted, this operator
   produces the empty set. *)
FreshActorName == IF \E a \in ActorName : actors[a] = null 
                  THEN {CHOOSE a \in ActorName : actors[a] = null}
                  ELSE {}

msgsTo(a)  == { m \in BagToSet(msgs) : m.target = a }
acqs(a)    == { b \in pdom(actors) : actors[a].active[b] > 0 }
pacqs(a)   == { b \in pdom(actors) : b \in acqs(a) \/ \E m \in msgsTo(a) : b \in m.refs }
piacqs(b)  == { a \in pdom(actors) : b \in pacqs(a) }

BusyActors    == { a \in pdom(actors) : actors[a].status = "busy" }
IdleActors    == { a \in pdom(actors) : actors[a].status = "idle" }
CrashedActors == { a \in pdom(actors) : actors[a].status = "crashed" }
Blocked       == { a \in IdleActors   : msgsTo(a) = {} }
Quiescent     == 
    LET RECURSIVE isQuiescent(_)
        isQuiescent(b) == b \in Blocked /\ \A a \in piacqs(b) \ {b} : isQuiescent(a)
    IN { a \in pdom(actors) : isQuiescent(a) }

====