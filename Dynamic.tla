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

(* A message consists of (a) the name of the destination actor, and (b) a set
   of references to other actors. Any other data a message could contain is 
   irrelevant for our purposes. *)
Message == [target: ActorName, refs : SUBSET ActorName] 

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
InitialConfiguration(actor, actorState) ==   
    LET state == [ actorState EXCEPT 
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

Spawn(a,b,actorState) == 
    /\ actors' = [actors EXCEPT 
        ![a].active[b] = 1,                                 \* Parent has a reference to the child.
        ![b] = [ 
            actorState EXCEPT 
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

Init == 
    InitialConfiguration(CHOOSE a \in ActorName: TRUE, InitialActorState)

Next == 
    \/ \E a \in BusyActors: Idle(a)
    \/ \E a \in BusyActors: \E b \in FreshActorName: Spawn(a,b,InitialActorState)
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

(* An actor's snapshot is up to date if its state has not changed since the 
   last snapshot. 
 *)
SnapshotUpToDate(a) == actors[a] = snapshots[a]

(* A snapshot from a past inverse acquaintance is recent enough if that the
   deactivated count in ths snapshot is up to date with the actual deactivated 
   count.
 *)
PastIAcqsRecentEnough(b) == \A a \in pdom(actors):
    actors[a].deactivated[b] > 0 =>
    a \in pdom(snapshots) /\ actors[a].deactivated[b] = snapshots[a].deactivated[b]

(* A set of snapshots is insufficient for b if:
   1. b's snapshot is out of date;
   2. b has a previous inverse acquaintance whose snapshot is not recent enough; or
   3. b is potentially reachable by an actor for which the snapshots are insufficient.
 *)
SnapshotsInsufficient == 
    CHOOSE S \in SUBSET pdom(actors) : \A a,b \in pdom(actors) :
    /\ (~SnapshotUpToDate(a) => a \in S)
    /\ (~PastIAcqsRecentEnough(a) => a \in S)
    /\ (a \in S /\ a \in piacqs(b) => b \in S)

SnapshotsSufficient == pdom(actors) \ SnapshotsInsufficient

(* The specification captures the following properties:
   1. Soundness: Every actor that appears quiescent is indeed quiescent.
   2. Completeness: Every quiescent actor with a sufficient set of snapshots
      will appear quiescent.
 *)
Spec == (Quiescent \intersect SnapshotsSufficient) = AppearsQuiescent

-----------------------------------------------------------------------------
(* TEST CASES: These invariants do not hold because garbage can be detected. *)

(* This invariant fails, showing that the set of quiescent actors is nonempty. *)
GarbageExists == ~(Quiescent = {})

(* This invariant fails, showing that quiescence can be detected. *)
GarbageIsDetected == ~(AppearsQuiescent = {})

(* An actor `b' can appear quiescent when a past inverse acquaintance `a' is not
quiescent. This is because `a' has deactivated all its references to `b'. *)
DeactivatedGarbage ==
  ~(\E a,b \in pdom(actors): a # b /\ a \notin Quiescent /\ b \in AppearsQuiescent /\ 
    actors[a].active[b] = 0 /\ actors[a].deactivated[b] > 0)

====