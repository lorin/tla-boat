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

validPassengersFromLeftToRight == {"fox", "grain"}

validBoatsFromLeftToRight == { {"farmer", "grain" } }

alone(animals, side) == (animals \in SUBSET side) /\ ~ "farmer" \in side

somebodyGetsEaten(l, r) == \/ alone({"fox", "chicken"}, l)
                           \/ alone({"fox", "chicken"}, r)
                           \/ alone({"chicken", "grain"}, l)
                           \/ alone({"chicken", "grain"}, r)


farmerCanTravelAloneFromLeftToRight(l, r) == ~ somebodyGetsEaten(l \ {"farmer"}, r \cup {"farmer"}) 
farmerCanTravelAloneFromRightToLeft(l, r) == ~ somebodyGetsEaten(r \ {"farmer"}, l \cup {"farmer"})




mySet == {x \in validPassengersFromLeftToRight : {x, "farmer"} }

(*
validBoatsFromLeftToRight == IF (farmerCanTravelAloneFromLeftToRight) THEN
        {x \in validPassengersFromLeftToRight : {x, "farmer"}} \cup {"farmer"}}
    ELSE 
        {x \in validPassengersFromLeftToRight : {x, "farmer"}}
          

validBoatsFromRightToLeft == validBoatsFromLeftToRight
*)

(***************************************************************************
--algorithm Boat {

variables left = CREATURES; right = {};

process ( LeftToRight = 0 )
    { p1: while (~done(left, right))
        { await ("farmer" \in left);
          with(boat \in validBoatsLeftToRight)
            { left := left \ boat;
              right := right \cup boat
            }
        }
    }

process ( RightToLeft = 1 )
    { p1: while (~done(left, right))
        { await ("farmer" \in right);
          with(boat \in validBoatsRightToLeft)
            { right := right \ boat;
              left := left \cup boat
            } 
        }
    }



}
 ***************************************************************************)


=============================================================================
\* Modification History
\* Last modified Mon Jun 02 21:28:35 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
