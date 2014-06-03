(*

A farmer is on one shore of a river and has with him a fox, a chicken,
and a sack of grain. He has a boat that fits one object besides himself.

In the presence of the farmer nothing gets eaten, but if left without the
farmer, the fox will eat the chicken, and the chicken will eat the grain.
How can the farmer get all three possessions across the river safely?


*)

-------------------------------- MODULE boat --------------------------------

CONSTANTS Farmer, Fox, Chicken, Grain

CREATURES == {Farmer, Fox, Chicken, Grain}

done(l, r) == r = CREATURES

alone(animals, side) == (animals \in SUBSET side) /\ ~ Farmer \in side

somebodyGetsEaten(l, r) == \/ alone({Fox, Chicken}, l)
                           \/ alone({Fox, Chicken}, r)
                           \/ alone({Chicken, Grain}, l)
                           \/ alone({Chicken, Grain}, r)

safe(l, r) == ~somebodyGetsEaten(l, r)

validPassengersFromLeft(l, r)  == { x \in l : safe(l \ {Farmer, x}, r \cup {Farmer, x})}
validPassengersFromRight(l, r) == { x \in r : safe(l \cup {Farmer, x}, r \ {Farmer, x})}

farmerCanGoAloneFromLeft(l, r)  == safe(l \ {Farmer}, r \cup {Farmer}) 
farmerCanGoAloneFromRight(l, r) == safe(r \ {Farmer}, l \cup {Farmer})


validBoatsFromLeft(l, r) ==  
    IF farmerCanGoAloneFromLeft(l, r) THEN {x \in validPassengersFromLeft(l, r) : {x, "farmer"} } \cup {"farmer"} 
                                      ELSE {x \in validPassengersFromLeft(l, r) : {x, "farmer"} }
          

validBoatsFromRight(l, r) ==  
    IF farmerCanGoAloneFromRight(l, r) THEN {x \in validPassengersFromRight(l, r) : {x, "farmer"} } \cup {"farmer"} 
                                       ELSE {x \in validPassengersFromRight(l, r) : {x, "farmer"} }



(***************************************************************************
--algorithm Boat {

variables left = CREATURES; right = {};

process ( LeftToRight = 0 )
    { p1: while (~done(left, right))
        { await (Farmer \in left);
          with(boat \in validBoatsFromLeft(left, right))
            { left := left \ boat;
              right := right \cup boat
            }
        }
    }

process ( RightToLeft = 1 )
    { p1: while (~done(left, right))
        { await (Farmer \in right);
          with(boat \in validBoatsFromRight(left, right))
            { right := right \ boat;
              left := left \cup boat
            } 
        }
    }

}
 ***************************************************************************)
\* BEGIN TRANSLATION
\* Label p1 of process LeftToRight at line 54 col 11 changed to p1_
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
             THEN /\ (Farmer \in left)
                  /\ \E boat \in validBoatsFromLeft(left, right):
                       /\ left' = left \ boat
                       /\ right' = (right \cup boat)
                  /\ pc' = [pc EXCEPT ![0] = "p1_"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ UNCHANGED << left, right >>

LeftToRight == p1_

p1 == /\ pc[1] = "p1"
      /\ IF ~done(left, right)
            THEN /\ (Farmer \in right)
                 /\ \E boat \in validBoatsFromRight(left, right):
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
\* Last modified Mon Jun 02 22:12:07 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
