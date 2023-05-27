---- MODULE Dropped ----
(* This model extends the Monitors model with dropped messages.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Operators from the Monitors model are imported within the `M' namespace. *)
M == INSTANCE Monitors

VARIABLE droppedMsgs \* This variable tracks dropped messages in the configuration.

InitialActorState == M!InitialActorState

TypeOK == M!TypeOK /\ BagToSet(droppedMsgs) \subseteq Message

Init == M!Init /\ droppedMsgs = EmptyBag

-----------------------------------------------------------------------------

droppedMsgsTo(a) == { m \in BagToSet(droppedMsgs) : m.target = a }

-----------------------------------------------------------------------------

Drop == \E m \in BagToSet(msgs) :
    /\ msgs' = remove(msgs, m)
    /\ droppedMsgs' = put(droppedMsgs, m)
    /\ UNCHANGED <<actors,snapshots>>

DropOracle == \E a \in pdom(actors) : \E S \in SUBSET droppedMsgsTo(a) :
    LET droppedRefs == { b \in ActorName : \E m \in S : b \in m.refs }
        droppedCount == Cardinality(S) IN
    /\ actors' = [ actors EXCEPT 
                   ![a].recvCount = @ + droppedCount,
                   ![a].deactivated = @ ++ [ b \in droppedRefs |-> 1 ]
                 ]
    /\ droppedMsgs' = removeAll(droppedMsgs, S)
    /\ UNCHANGED <<msgs,snapshots>>

Next == (M!Next /\ UNCHANGED <<droppedMsgs>>) \/ Drop \/ DropOracle

-----------------------------------------------------------------------------

Soundness == M!Soundness

SnapshotUpToDate(a) == 
    /\ actors[a] = snapshots[a]
    /\ droppedMsgsTo(a) = {}   \* The actor has been notified about all dropped messages

SnapshotsInsufficient == 
    CHOOSE S \in SUBSET pdom(actors) : \A a,b \in pdom(actors) :
    /\ (~SnapshotUpToDate(a) => a \in S)
    /\ (~M!RecentEnough(a,b) => b \in S)
    /\ (a \in S /\ a \in piacqs(b) => b \in S)
    /\ (a \in S /\ a \in M!monitoredBy(b) => b \in S)

SnapshotsSufficient == pdom(actors) \ SnapshotsInsufficient

(* If an actor is garbage and its snapshot is up to date and the snapshots of
   all its historical inverse acquaintances are recent enough and 
 *)
Completeness == (M!Quiescent \intersect SnapshotsSufficient) \subseteq M!AppearsQuiescent

====