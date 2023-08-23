---- MODULE Shadows ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots, droppedMsgs

E == INSTANCE Exile

(* A Shadow is a node in the shadow graph. Each Shadow in the graph
   corresponds to an actor that has taken a snapshot or is referenced 
   in another actor's snapshot. 
   
   - `interned' indicates whether this actor has taken a snapshot. If
     `interned' is FALSE, the other fields are meaningless.
   - `sticky' indicates whether the actor was sticky in its latest
     snapshot.
   - `status' indicates the status of the actor in its latest snapshot.
   - `undelivered' is the number of messages that appear sent but not
     received in the collage.
   - `references' is the number of references that appear created but
     not deactivated in the collage.
   - `monitored' is the set of actors monitored by this actor in its
     latest snapshot.
*)
Shadow == [
    interned      : BOOLEAN,
    sticky        : BOOLEAN,
    status        : {"idle", "busy", "halted"},
    undelivered   : Int,
    references    : [ActorName -> Nat],
    monitored     : SUBSET ActorName,
]

(* Shadow graphs are represented here as an indexed collection of shadows. *)
ShadowGraph == [ActorName -> Shadow \union {null}]

apparentUndeliveredCount(S,b) ==
    sum([b \in pdom(S) |-> S[b].sendCount[a]]) - 
    IF a \in pdom(S) THEN S[a].recvCount ELSE 0

apparentReferenceCount(S,a,b) ==
    sum([c \in pdom(S) |-> S[b].created[a,b]]) -
    IF a \in pdom(S) THEN S[a].deactivated[b] ELSE 0

apparentWatchers(S,a) ==
    { b \in pdom(S) : a \in S[b].monitored }

(* This is the shadow graph representation of the collage stored in `snapshots'. *)
shadowGraph == 
    [ a \in ActorName |-> 
        [
            interned      |-> a \in Snapshots,
            sticky        |-> IF a \in Snapshots THEN S[a].sticky ELSE FALSE,
            status        |-> IF a \in Snapshots THEN S[a].status ELSE "idle",
            undelivered   |-> apparentUndeliveredCount(S, a),
            references    |-> [b \in ActorName |-> apparentReferenceCount(S, a, b)],
            watchers      |-> apparentWatchers(S, a)
        ]
    ]

PseudoRoots(G) ==
    { a \in pdom(G) : 
        ~S[a].interned \/ S[a].sticky \/ S[a].busy \/ S[a].undelivered # 0 }

apparentAcquaintances(G,a) ==
    { b \in pdom(G) : S[a].references > 0 }
        
appearsFaulty(G) == 
    { a \in pdom(G) : G[a].status = "halted" }
        
(* In the shadow graph G, an actor appears potentially unblocked iff 
   1. A potentially unblocked actor appears acquainted with it;
   2. A potentially unblocked actor is monitored by it; or
   3. An apparently faulty actor is monitored by it.  *)
appearsLive(G) == 
    CHOOSE S \in SUBSET pdom(G) \ appearsFaulty(G) :
    /\ PseudoRoots(G) \subseteq S
    /\ \A a \in S, b \in apparentAcquaintances(G,a) => b \in S
    /\ \A a \in S \union appearsFaulty(G), b \in G[a].watchers => b \in S


-----------------------------------------------------------------------------
(* SOUNDNESS AND COMPLETENESS PROPERTIES *)



-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)


====