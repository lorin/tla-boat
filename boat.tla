(*

A farmer is on one shore of a river and has with him a fox, a chicken,
and a sack of grain. He has a boat that fits one object besides himself.

In the presence of the farmer nothing gets eaten, but if left without the
farmer, the fox will eat the chicken, and the chicken will eat the grain.
How can the farmer get all three possessions across the river safely?


*)

-------------------------------- MODULE boat --------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Farmer, Fox, Chicken, Grain

CREATURES == {Farmer, Fox, Chicken, Grain}

alone(animals, side) == (animals \in SUBSET side) /\ ~ Farmer \in side

somebodyGetsEaten(l, r) == \/ alone({Fox, Chicken}, l)
                           \/ alone({Fox, Chicken}, r)
                           \/ alone({Chicken, Grain}, l)
                           \/ alone({Chicken, Grain}, r)

safe(l, r) == ~somebodyGetsEaten(l, r)

safeBoats(from, to) == { boat \in SUBSET from : /\ Farmer \in boat
                                                /\ Cardinality(boat) <= 2
                                                /\ safe(from \ boat, to \cup boat) }

(***************************************************************************
--algorithm RiverCrossing {

variables left = CREATURES; right = {};

process ( LeftToRight = 0 )
    { l: while (left /= {})
         { await (Farmer \in left);
           with(boat \in safeBoats(left, right))
             {
               left := left \ boat;
               right := right \cup boat
             }
         }
    }

process ( RightToLeft = 1 )
    { r: while (left /= {})
         { await (Farmer \in right);
           with(boat \in safeBoats(right, left))
             {
               left := left \cup boat;
               right := right \ boat
             }
         }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES left, right, pc

vars == << left, right, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ left = CREATURES
        /\ right = {}
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l"
                                        [] self = 1 -> "r"]

l == /\ pc[0] = "l"
     /\ IF left /= {}
           THEN /\ (Farmer \in left)
                /\ \E boat \in safeBoats(left, right):
                     /\ left' = left \ boat
                     /\ right' = (right \cup boat)
                /\ pc' = [pc EXCEPT ![0] = "l"]
           ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                /\ UNCHANGED << left, right >>

LeftToRight == l

r == /\ pc[1] = "r"
     /\ IF left /= {}
           THEN /\ (Farmer \in right)
                /\ \E boat \in safeBoats(right, left):
                     /\ left' = (left \cup boat)
                     /\ right' = right \ boat
                /\ pc' = [pc EXCEPT ![1] = "r"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                /\ UNCHANGED << left, right >>

RightToLeft == r

Next == LeftToRight \/ RightToLeft
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Jun 04 21:54:45 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
