---- MODULE Dynamic ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

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

Idle(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Spawn(a,b) == 
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,                                 \* Parent has a reference to the child.
        ![b] = [ 
            InitialActorState EXCEPT 
            !.active  = @ ++ (b :> 1),                      \* Child has a reference to itself.
            !.created = @ ++ (<<b,b>> :> 1 @@ <<a,b>> :> 1) \* Child knows about both references.
        ]
        ]
    /\ UNCHANGED <<snapshots,msgs>>

Deactivate(a,b) ==
    /\ actors' = [actors EXCEPT 
        ![a].deactivated[b] = @ + actors[a].active[b],
        ![a].active[b] = 0
        ]
    /\ UNCHANGED <<msgs,snapshots>>

Send(a,b,m) ==
    /\ actors' = [actors EXCEPT 
        ![a].sendCount[b] = @ + 1,
        ![a].created = @ ++ [ <<x, y>> \in {b} \X m.refs |-> 1 ]
        ]
    (* Add this message to the msgs bag. *)
    /\ msgs' = put(msgs, m)
    /\ UNCHANGED <<snapshots>>

Receive(a,m) ==
    /\ actors' = [actors EXCEPT 
        ![a].active = @ ++ [c \in m.refs |-> 1],
        ![a].recvCount = @ + 1, 
        ![a].status = "busy"]
    (* Remove m from the msgs bag. *)
    /\ msgs' = remove(msgs, m)
    /\ UNCHANGED <<snapshots>>

Snapshot(a) == 
    /\ snapshots[a] = null
    /\ snapshots' = [snapshots EXCEPT ![a] = actors[a]]
    /\ UNCHANGED <<msgs,actors>>

Next == 
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: Spawn(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a): Deactivate(a,b)
    \/ \E a \in BusyActors: \E b \in acqs(a): \E refs \in SUBSET acqs(a): 
        Send(a,b,[target |-> b, refs |-> refs])
    \/ \E a \in IdleActors: \E m \in msgsTo(a): Receive(a,m)
    \/ \E a \in IdleActors \union BusyActors: Snapshot(a)

-----------------------------------------------------------------------------

PotentiallyUnblocked ==
    CHOOSE S \in SUBSET pdom(actors) : \A a, b \in pdom(actors) :
    /\ (a \notin Blocked => a \in S)
    /\ (a \in S /\ a \in piacqs(b) => b \in S)

Quiescent == pdom(actors) \ PotentiallyUnblocked

countCreated(a, b)     == sum([ c \in pdom(snapshots) |-> snapshots[c].created[a, b]])
countDeactivated(a, b) == IF a \in pdom(snapshots) THEN snapshots[a].deactivated[b] ELSE 0
countSentTo(b)         == sum([ a \in pdom(snapshots) |-> snapshots[a].sendCount[b]])
countReceived(b)       == IF b \in pdom(snapshots) THEN snapshots[b].recvCount ELSE 0

historicalIAcqs(c) == { b \in ActorName : countCreated(b, c) > 0 }
apparentIAcqs(c)   == { b \in ActorName : countCreated(b, c) > countDeactivated(b, c) }

AppearsIdle    == { a \in pdom(snapshots) : snapshots[a].status = "idle" }
AppearsClosed  == { b \in pdom(snapshots) : historicalIAcqs(b) \subseteq pdom(snapshots) }
AppearsBlocked == { b \in AppearsIdle \cap AppearsClosed : countSentTo(b) = countReceived(b) }
AppearsUnblocked == pdom(snapshots) \ AppearsBlocked

AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET pdom(snapshots) : \A a, b \in pdom(snapshots) :
    /\ (a \notin AppearsBlocked => a \in S)
    /\ (a \in S /\ a \in apparentIAcqs(b) => b \in S)

AppearsQuiescent == pdom(snapshots) \ AppearsPotentiallyUnblocked

Soundness == AppearsQuiescent \subseteq Quiescent

-----------------------------------------------------------------------------

(* A snapshot from actor `a' is recent enough for actor `b' if its send count,
   deactivated count, and created count regarding `b' are all up to date.
 *)
RecentEnough(a, b) ==
    /\ a \in pdom(snapshots)
    /\ actors[a].active[b] = snapshots[a].active[b]
    /\ actors[a].deactivated[b] = snapshots[a].deactivated[b]
    /\ \A c \in ActorName : actors[a].created[b,c] = snapshots[a].created[b,c]
    /\ \A c \in ActorName : actors[a].created[c,b] = snapshots[a].created[c,b]

(* An actor's snapshot is up to date if its state has not changed since the last snapshot. *)
SnapshotUpToDate(a) == actors[a] = snapshots[a]

(* A set of snapshots is sufficient for b if:
   1. b's snapshot is up to date;
   2. The snapshots of all b's historical inverse acquaintances are recent enough for a;
   3. The snapshots are sufficient for all of b's potential inverse acquaintances.
 *)
SnapshotsInsufficient == 
    CHOOSE S \in SUBSET pdom(actors) : \A a,b \in pdom(actors) :
    /\ (~SnapshotUpToDate(a) => a \in S)
    /\ (~RecentEnough(a,b) => b \in S)
    /\ (a \in S /\ a \in piacqs(b) => b \in S)

SnapshotsSufficient == pdom(actors) \ SnapshotsInsufficient

(* If an actor is garbage and its snapshot is up to date and the snapshots of
   all its historical inverse acquaintances are recent enough and 
 *)
Completeness == (Quiescent \intersect SnapshotsSufficient) \subseteq AppearsQuiescent

====