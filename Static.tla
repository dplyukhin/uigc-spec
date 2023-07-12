---- MODULE Static ----
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(*
ActorState represents the GC-relevant state of an actor.
- status indicates whether the actor is currently processing a message.
- recvCount is the number of messages that this actor has received.
- sendCount[b] is the number of messages this actor has sent to b.
- acqs is the set of actors that this actor is acquainted with.
*)
ActorState == [ 
    status      : {"busy", "idle"},
    recvCount   : Nat,
    sendCount   : [ActorName -> Nat],
    acqs        : SUBSET ActorName
]

(* In this simple model, a message has only one field `target' representing
   the name of the destination actor. The payload of the message is omitted. *)
Message == [target: ActorName] 

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
    acqs        |-> {}
]
        
(* In the initial configuration, there is one busy actor with a reference
   to itself. *)
InitialConfiguration(actor, actorState) ==   
    LET state == [ actorState EXCEPT 
                   !.acqs  = {actor}
                 ]
    IN
    /\ msgs = EmptyBag
    /\ actors = [a \in ActorName |-> IF a = actor THEN state ELSE null ]
    /\ snapshots = [a \in ActorName |-> null]

-----------------------------------------------------------------------------
(* DEFINITIONS *)

msgsTo(a)    == { m \in BagToSet(msgs) : m.target = a }
acqs(a)      == actors[a].acqs
iacqs(b)     == { a \in Actors : b \in acqs(a) }

BusyActors   == { a \in Actors     : actors[a].status = "busy" }
IdleActors   == { a \in Actors     : actors[a].status = "idle" }
Blocked      == { a \in IdleActors : msgsTo(a) = {} }
Unblocked    == Actors \ Blocked

-----------------------------------------------------------------------------
(* TRANSITIONS *)

Idle(a) ==
    /\ actors' = [actors EXCEPT ![a].status = "idle"]
    /\ UNCHANGED <<msgs,snapshots>>

Send(a,b,m) ==
    /\ actors' = [actors EXCEPT ![a].sendCount[b] = @ + 1]
    /\ msgs' = put(msgs, m)
    /\ UNCHANGED <<snapshots>>

Receive(a,m) ==
    /\ actors' = [actors EXCEPT ![a].recvCount = @ + 1, ![a].status = "busy"]
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
    \/ \E a \in BusyActors: \E b \in acqs(a): Send(a,b,[target |-> b])
    \/ \E a \in IdleActors: \E m \in msgsTo(a): Receive(a,m)
    \/ \E a \in IdleActors \union BusyActors: Snapshot(a)

-----------------------------------------------------------------------------

PotentiallyUnblocked ==
    CHOOSE S \in SUBSET Actors : \A a, b \in Actors :
    /\ (a \notin Blocked => a \in S)
    /\ (a \in S /\ a \in iacqs(b) => b \in S)

Quiescent == Actors \ PotentiallyUnblocked

countSentTo(b)   == sum([ a \in Snapshots |-> snapshots[a].sendCount[b]])
countReceived(b) == IF b \in Snapshots THEN snapshots[b].recvCount ELSE 0

AppearsIdle    == { a \in Snapshots : snapshots[a].status = "idle" }
AppearsClosed  == { b \in Snapshots : iacqs(b) \subseteq Snapshots }
AppearsBlocked == { b \in AppearsIdle \cap AppearsClosed : countSentTo(b) = countReceived(b) }
AppearsUnblocked == Snapshots \ AppearsBlocked

AppearsPotentiallyUnblocked == 
    CHOOSE S \in SUBSET Snapshots : \A a, b \in Snapshots :
    /\ (a \notin AppearsBlocked => a \in S)
    /\ (a \in S /\ a \in iacqs(b) => b \in S)

AppearsQuiescent == Snapshots \ AppearsPotentiallyUnblocked

(* A set of snapshots is insufficient for b if:
   1. b's snapshot is out of date; or
   2. b is reachable by an actor for which the snapshots are insufficient.
 *)
SnapshotsInsufficient == 
    CHOOSE S \in SUBSET Actors : \A a \in Actors :
    /\ actors[a] # snapshots[a] => a \in S
    /\ \A b \in Actors :
        /\ (a \in S /\ a \in iacqs(b) => b \in S)

SnapshotsSufficient == Actors \ SnapshotsInsufficient

(* The specification captures the following properties:
   1. Soundness: Every actor that appears quiescent is indeed quiescent.
   2. Completeness: Every quiescent actor with a sufficient set of snapshots
      will appear quiescent.
 *)
Spec == (Quiescent \intersect SnapshotsSufficient) = AppearsQuiescent

====