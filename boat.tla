(*

A farmer is on one shore of a river and has with him a fox, a chicken,
and a sack of grain. He has a boat that fits one object besides himself.

In the presence of the farmer nothing gets eaten, but if left without the
farmer, the fox will eat the chicken, and the chicken will eat the grain.
How can the farmer get all three possessions across the river safely?


*)

-------------------------------- MODULE boat --------------------------------

CREATURES == {"farmer", "fox", "chicken", "grain"}

done(l, r) == r = CREATURES

alone(animals, side) == (animals \in SUBSET side) /\ ~ "farmer" \in side

somebodyGetsEaten(l, r) == \/ alone({"fox", "chicken"}, l)
                           \/ alone({"fox", "chicken"}, r)
                           \/ alone({"chicken", "grain"}, l)
                           \/ alone({"chicken", "grain"}, r)

validPassengersFromLeftToRight(l, r) == { x \in l : ~somebodyGetsEaten(l \ {"farmer", x}, r \cup {"farmer", x})}
validPassengersFromRightToLeft(l, r) == { x \in r : ~somebodyGetsEaten(l \cup {"farmer", x}, r \ {"farmer", x})}

farmerCanTravelAloneFromLeftToRight(l, r) == ~ somebodyGetsEaten(l \ {"farmer"}, r \cup {"farmer"}) 
farmerCanTravelAloneFromRightToLeft(l, r) == ~ somebodyGetsEaten(r \ {"farmer"}, l \cup {"farmer"})


validBoatsFromLeftToRight(l, r) ==  
    IF farmerCanTravelAloneFromLeftToRight(l, r) THEN {x \in validPassengersFromLeftToRight(l, r) : {x, "farmer"} } \cup {"farmer"} 
                                                 ELSE {x \in validPassengersFromLeftToRight(l, r) : {x, "farmer"} }
          

validBoatsFromRightToLeft(l, r) ==  
    IF farmerCanTravelAloneFromRightToLeft(l, r) THEN {x \in validPassengersFromRightToLeft(l, r) : {x, "farmer"} } \cup {"farmer"} 
                                                 ELSE {x \in validPassengersFromRightToLeft(l, r) : {x, "farmer"} }




(***************************************************************************
--algorithm Boat {

variables left = CREATURES; right = {};

process ( LeftToRight = 0 )
    { p1: while (~done(left, right))
        { await ("farmer" \in left);
          with(boat \in validBoatsFromLeftToRight(left, right))
            { left := left \ boat;
              right := right \cup boat
            }
        }
    }

process ( RightToLeft = 1 )
    { p1: while (~done(left, right))
        { await ("farmer" \in right);
          with(boat \in validBoatsFromRightToLeft(left, right))
            { right := right \ boat;
              left := left \cup boat
            } 
        }
    }

}
 ***************************************************************************)
\* BEGIN TRANSLATION
\* Label p1 of process LeftToRight at line 51 col 11 changed to p1_
VARIABLES left, right, pc

vars == << left, right, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ left = CREATURES
        /\ right = {}
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "p1_"
                                        [] self = 1 -> "p1"]

p1_ == /\ pc[0] = "p1_"
       /\ IF ~done(left, right)
             THEN /\ ("farmer" \in left)
                  /\ \E boat \in validBoatsFromLeftToRight(left, right):
                       /\ left' = left \ boat
                       /\ right' = (right \cup boat)
                  /\ pc' = [pc EXCEPT ![0] = "p1_"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ UNCHANGED << left, right >>

LeftToRight == p1_

p1 == /\ pc[1] = "p1"
      /\ IF ~done(left, right)
            THEN /\ ("farmer" \in right)
                 /\ \E boat \in validBoatsFromRightToLeft(left, right):
                      /\ right' = right \ boat
                      /\ left' = (left \cup boat)
                 /\ pc' = [pc EXCEPT ![1] = "p1"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                 /\ UNCHANGED << left, right >>

RightToLeft == p1

Next == LeftToRight \/ RightToLeft
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Mon Jun 02 21:40:10 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
