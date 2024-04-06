---- MODULE Shadows ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots, droppedMsgs

D == INSTANCE Dynamic
M == INSTANCE Monitors
E == INSTANCE Exile

-----------------------------------------------------------------------------
(* SHADOW GRAPHS *)

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
(* UNDO LOGS *)

(* An undo log for node N indicates how to recover from the exile of node N.  
   - `undeliveredMsgs[a]' indicates the number of messages that h
*)
UndoLog == [
    node : NodeID,
    undeliveredMsgs : [ActorName -> Nat],
    undeliveredRefs : [ActorName \X ActorName -> Nat]
]

snapshotsFrom(N) == { a \in Snapshots : location[a] = N }

(* The number of messages sent to actor `b' by actors on node N, according to
   the collage. *)
appearsSentBy(N,b) == sum([ a \in snapshotsFrom(N) |-> snapshots[a].sent[b]])

(* The number of references owned by `a' pointing to `b' created by node N,
   according to the collage. *)
appearsCreatedBy(N,a,b) == sum([ c \in snapshotsFrom(N) |-> snapshots[c].created[a, b]])

(* The number of messages sent to `b' originating from N1 that have been 
   admitted to their destination, according to the ingress actors' snapshots. *)
appearsAdmittedFrom(N1,b) == 
    sum([ N2 \in NodeID |-> ingressSnapshots[N1,N2].admittedMsgs[b] ])

(* The number of references owned by `a' pointing to `b' created by N1 that 
   have been admitted to their destination, according to the ingress actors' 
   snapshots. *)
appearsAdmittedRefsFrom(N1,b,c) == 
    sum([ N2 \in NodeID |-> ingressSnapshots[N1,N2].admittedRefs[b,c] ])

(* The undo log for node N. It is only defined when N appears exiled. *)
undo(N) == [
    node |-> N,
    undeliveredMsgs |-> 
        [b \in ActorName |-> 
            appearsSentBy(N,b) - appearsAdmittedFrom(N,b)],
    undeliveredRefs |-> 
        [<<b,c>> \in ActorName \X ActorName |-> 
            appearsCreatedBy(N,b,c) - appearsAdmittedRefsFrom(N,b,c)]
]


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