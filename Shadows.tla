---- MODULE Shadows ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

D == INSTANCE Dynamic
M == INSTANCE Monitors

-----------------------------------------------------------------------------
(* SHADOW GRAPHS *)

(* A Shadow is a node in the shadow graph. Each Shadow in the graph
   corresponds to an actor that has taken a snapshot or is referenced 
   in another actor's snapshot. 
   
   - `interned' indicates whether this actor has taken a snapshot. If
     `interned' is FALSE, the values of `sticky` and `status` are 
     meaningless.
   - `sticky' indicates whether the actor was sticky in its latest
     snapshot.
   - `status' indicates the status of the actor in its latest snapshot.
   - `undelivered' is the number of messages that appear sent but not
     received.
   - `references' is the number of references that appear created but
     not deactivated.
   - `watchers' is the set of actors that appear to monitor this actor.
*)
Shadow == [
    interned      : BOOLEAN,
    sticky        : BOOLEAN,
    status        : {"idle", "busy", "halted"},
    undelivered   : Int,
    references    : [ActorName -> Int],
    watchers      : SUBSET ActorName
]

(* Shadow graphs are represented here as an indexed collection of shadows. *)
ShadowGraph == [ActorName -> Shadow \union {null}]

undelivered(b) == D!sent(b) - D!received(b)

references(a,b) == D!created(a,b) - D!deactivated(a,b)

watches(a,b) == a \in Snapshots /\ b \in snapshots[a].monitored

(* This is the domain of the shadow graph. An actor is in the shadow graph if it occurs
   in a snapshot. *)
Shadows == 
    { c \in ActorName : 
        \/ c \in Snapshots
        \/ \E a \in Snapshots : \E b \in ActorName : snapshots[a].created[b,c] > 0
        \/ \E a \in Snapshots : \E b \in ActorName : snapshots[a].created[c,b] > 0
        \/ \E a \in Snapshots : snapshots[a].deactivated[c] > 0
        \/ \E a \in Snapshots : snapshots[a].sent[c] > 0
        \/ \E a \in Snapshots : c \in snapshots[a].monitored
    }

(* This is the shadow graph representation of the collage stored in `snapshots'. *)
shadows == 
    [ b \in Shadows |->
        [
            interned      |-> b \in Snapshots,
            sticky        |-> IF b \in Snapshots THEN snapshots[b].isSticky ELSE FALSE,
            status        |-> IF b \in Snapshots THEN snapshots[b].status ELSE "idle",
            undelivered   |-> undelivered(b),
            references    |-> [c \in ActorName |-> references(b, c)],
            watchers      |-> { a \in ActorName : watches(a,b) }
        ]
    ]
        
AppearsFaulty == 
    { a \in Shadows : shadows[a].status = "halted" }

PseudoRoots ==
    { a \in Shadows \ AppearsFaulty : LET s == shadows[a] IN
        ~s.interned \/ s.sticky \/ s.status = "busy" \/ s.undelivered # 0 }

acquaintances(a) ==
    { b \in Shadows : shadows[a].references[b] > 0 }
        
watchers(a) == { b \in Shadows : b \in shadows[a].watchers }
        
(* In the shadow graph G, an actor appears potentially unblocked iff 
   0. It is a pseudo-root;
   1. A potentially unblocked actor appears acquainted with it; or
   2. A potentially unblocked actor is monitored by it.  *)
AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET Shadows \ AppearsFaulty :
    /\ PseudoRoots \subseteq S
    /\ \A a \in S: 
        acquaintances(a) \ AppearsFaulty \subseteq S
    /\ \A a \in S \union AppearsFaulty: 
        watchers(a) \ AppearsFaulty \subseteq S

AppearsQuiescent == Shadows \ AppearsPotentiallyUnblocked

-----------------------------------------------------------------------------
(* MODEL *)

(* Alone, shadow graphs characterize the garbage in the Monitors model.
   To find garbage in the Exile model, we need undo logs.
 *)

Init == M!Init
Next == M!Next

-----------------------------------------------------------------------------
(* PROPERTIES *)

TypeOK == \A a \in Shadows: shadows[a] \in Shadow

Spec == AppearsQuiescent = M!AppearsQuiescent

====