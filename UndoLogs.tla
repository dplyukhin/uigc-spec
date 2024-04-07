---- MODULE UndoLogs ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

CONSTANT NodeID
VARIABLE location, ingress, ingressSnapshots, droppedMsgs

D == INSTANCE Dynamic
M == INSTANCE Monitors
E == INSTANCE Exile
S == INSTANCE Shadows

-----------------------------------------------------------------------------
(* UNDO LOGS *)

(* An undo log for node N indicates how to recover from the exile of node N. *)
UndoLog == [
    node : NodeID,
    undeliverableMsgs : [ActorName -> Int],
    undeliverableRefs : [ActorName \X ActorName -> Int]
]

snapshotsFrom(N) == { a \in Snapshots : location[a] = N }

(* The number of messages sent to actor `b' by actors on node N, according to
   the collage. *)
sent(N,b) == sum([ a \in snapshotsFrom(N) |-> snapshots[a].sent[b]])

(* The number of references owned by `a' pointing to `b' created by node N,
   according to the collage. *)
created(N,a,b) == sum([ c \in snapshotsFrom(N) |-> snapshots[c].created[a, b]])

(* The number of messages sent to `b' originating from N1 that have been 
   admitted to their destination, according to the ingress actors' snapshots. *)
admittedMsgs(N1,b) == 
    LET N2 == location[b] IN 
    IF <<N1,N2>> \in DOMAIN ingressSnapshots THEN
        ingressSnapshots[N1,N2].admittedMsgs[b]
    ELSE 0

(* The number of references owned by `a' pointing to `b' created by N1 that 
   have been admitted to their destination, according to the ingress actors' 
   snapshots. *)
admittedRefs(N1,b,c) == 
    LET N2 == location[b] IN 
    IF <<N1,N2>> \in DOMAIN ingressSnapshots THEN
        ingressSnapshots[N1,N2].admittedRefs[b,c]
    ELSE 0

(* The undo logs for each node N. *)
undo == 
    [ N \in NodeID |->
        [
            node |-> N,
            undeliverableMsgs |-> 
                [b \in ActorName |-> 
                    sent(N, b) - admittedMsgs(N, b)],
            undeliverableRefs |-> 
                [<<b,c>> \in ActorName \X ActorName |-> 
                    created(N,b,c) - admittedRefs(N,b,c)]
        ]
    ]

undeliverableMsgs ==
    [ b \in ActorName |->
        sum([ N \in E!ApparentlyExiledNodes |-> undo[N].undeliverableMsgs[b] ])
    ]

undeliverableRefs ==
    [ <<b,c>> \in ActorName \X ActorName |->
        sum([ N \in E!ApparentlyExiledNodes |-> undo[N].undeliverableRefs[b,c] ])
    ]

AmendedShadows ==
    { a \in ActorName : 
        /\ a \in S!Shadows
        /\ (a \notin E!ApparentlyExiledActors \/ S!shadows[a].watchers # {}) 
    }

(* The shadow graph, amended using finalized undo logs. *)
amendedShadows ==
    [ b \in AmendedShadows |->
        [
            interned    |-> S!shadows[b].interned,
            sticky      |-> S!shadows[b].sticky,
            watchers    |-> S!shadows[b].watchers \ E!ApparentlyExiledActors,
            status      |-> IF b \in E!ApparentlyExiledActors THEN "halted" ELSE S!shadows[b].status,
            undelivered |-> S!shadows[b].undelivered - undeliverableMsgs[b],
            references  |-> [c \in ActorName |-> S!shadows[b].references[c] - undeliverableRefs[b,c]]
        ]
    ]

-----------------------------------------------------------------------------
(* MODEL *)

Init == E!Init
Next == E!Next

-----------------------------------------------------------------------------
(* PROPERTIES *)

TypeOK == 
    /\ undo \in [NodeID -> UndoLog]
    /\ \A a \in AmendedShadows : amendedShadows[a] \in S!Shadow

Spec == 
  S!unmarked(amendedShadows) \ E!ApparentlyExiledActors = 
  E!AppearsQuiescent \ E!ApparentlyExiledActors

====