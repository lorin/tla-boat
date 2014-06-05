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

done(l, r) == r = CREATURES

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
    { l: while (~done(left, right))
         { await (Farmer \in left);
           with(boat \in safeBoats(left, right))
             {
               left := left \ boat;
               right := right \cup boat
             }
         }
    }

process ( RightToLeft = 1 )
    { r: while (~done(left, right))
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

=============================================================================
\* Modification History
\* Last modified Wed Jun 04 21:40:04 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
