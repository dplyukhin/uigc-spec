---- MODULE Dropped ----
(* This model extends the Monitors model with dropped messages.  *)
EXTENDS Common, Integers, FiniteSets, Bags, TLC

(* Operators from the Monitors model are imported within the `M' namespace. *)
M == INSTANCE Monitors

VARIABLE 
    droppedMsgs \* We add this to the configuration to track dropped messages.

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

Soundness == M!Safety

Completeness == M!Liveness

====