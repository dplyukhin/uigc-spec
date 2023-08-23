---- MODULE Shadows ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots, droppedMsgs

D == INSTANCE Dynamic
M == INSTANCE Monitors
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
    monitored     : SUBSET ActorName
]

(* Shadow graphs are represented here as an indexed collection of shadows. *)
ShadowGraph == [ActorName -> Shadow \union {null}]

apparentUndeliveredCount(b) == D!countSentTo(b) - D!countReceived(b)

apparentReferenceCount(a,b) == D!countCreated(a,b) - D!countDeactivated(a,b)

(* This is the shadow graph representation of the collage stored in `snapshots'. *)
shadows == 
    [ a \in ActorName |-> 
        (* TODO Some actors are not in the graph... *)
        [
            interned      |-> a \in Snapshots,
            sticky        |-> IF a \in Snapshots THEN snapshots[a].sticky ELSE FALSE,
            status        |-> IF a \in Snapshots THEN snapshots[a].status ELSE "idle",
            undelivered   |-> apparentUndeliveredCount(a),
            references    |-> [b \in ActorName |-> apparentReferenceCount(a, b)],
            monitored     |-> M!appearsMonitoredBy(a)
        ]
    ]

PseudoRoots ==
    { a \in pdom(shadows) : LET s == shadows[a] IN
        ~s.interned \/ s.sticky \/ s.busy \/ s.undelivered # 0 }
        
AppearsFaulty == 
    { a \in pdom(shadows) : shadows[a].status = "halted" }

apparentAcquaintances(a) ==
    { b \in pdom(shadows) : shadows[a].references > 0 }
        
(* In the shadow graph G, an actor appears potentially unblocked iff 
   1. A potentially unblocked actor appears acquainted with it;
   2. A potentially unblocked actor is monitored by it; or
   3. An apparently faulty actor is monitored by it.  *)
AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET pdom(shadows) \ AppearsFaulty :
    /\ PseudoRoots \subseteq S
    /\ \A a \in S: apparentAcquaintances(a) \subseteq S
    /\ \A a \in S \union AppearsFaulty: shadows[a].monitored \subseteq S

AppearsQuiescent == 
    pdom(shadows) \ AppearsPotentiallyUnblocked


-----------------------------------------------------------------------------
(* MODEL *)

Init == E!Init
Next == E!Next
TypeOK == shadows \in ShadowGraph


-----------------------------------------------------------------------------
(* SOUNDNESS AND COMPLETENESS PROPERTIES *)



-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)


====