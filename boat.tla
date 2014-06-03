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

(***************************************************************************
--algorithm Boat {

variables left = CREATURES; right = {};

process ( LeftToRight = 0 )
    { p1: while (~done(left, right))
        { await (Farmer \in left);
          with(passenger \in validPassengersFromLeft(left, right))
            {        
              if(farmerCanGoAloneFromLeft(left, right))
                either
                    { left := left \ {Farmer};
                      right := right \cup {Farmer};
                    }
                or
                    {
                      left := left \ {Farmer, passenger};
                      right := right \cup {Farmer, passenger}
                    }
              else
                {
                  left := left \ {Farmer, passenger};
                  right := right \cup {Farmer, passenger}  
                }
            }
        }
    }

process ( RightToLeft = 1 )
    { p2: while (~done(left, right))
        { await (Farmer \in right);
          with(passenger \in validPassengersFromRight(left, right))
            {        
              if(farmerCanGoAloneFromRight(left, right))
                either
                    { right := right \ {Farmer};
                      left := left \cup {Farmer};
                    }
                or
                    {
                      right := right \ {Farmer, passenger};
                      left := left \cup {Farmer, passenger}
                    }
              else
                {
                  right := right \ {Farmer, passenger};
                  left := left \cup {Farmer, passenger}  
                }
            }
        }
    }

}
 ***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Mon Jun 02 22:48:00 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
