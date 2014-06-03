(*

A farmer is on one shore of a river and has with him a fox, a chicken,
and a sack of grain. He has a boat that fits one object besides himself.

In the presence of the farmer nothing gets eaten, but if left without the
farmer, the fox will eat the chicken, and the chicken will eat the grain.
How can the farmer get all three possessions across the river safely?


*)

-------------------------------- MODULE boat --------------------------------

CREATURES == {"farmer", "fox", "chicken", "grain"}


(***************************************************************************
--algorithm Boat {

variables left = CREATURES, right = {}

done == right = CREATURES;

process ( LeftToRight = 0 )
    { p1: while (~done)
        { await ("farmer" \in left) 
        }
    }

process ( RightToLeft = 1 )
    { p1: while (~done)
        { await ("farmer" \in right) 
        }
    }


}
 ***************************************************************************)
\* BEGIN TRANSLATION
\* Label p1 of process Left at line 31 col 11 changed to p1_
VARIABLES left, right, pc

vars == << left, right, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ left = CREATURES
        /\ right =                                     {}
                   
                   done == right = CREATURES
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "p1_"
                                        [] self = 1 -> "p1"]

p1_ == /\ pc[0] = "p1_"
       /\ IF ~done
             THEN /\ ("farmer" \in left)
                  /\ pc' = [pc EXCEPT ![0] = "p1_"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
       /\ UNCHANGED << left, right >>

Left == p1_

p1 == /\ pc[1] = "p1"
      /\ IF ~done
            THEN /\ ("farmer" \in right)
                 /\ pc' = [pc EXCEPT ![1] = "p1"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << left, right >>

Right == p1

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Mon Jun 02 20:57:10 EDT 2014 by lorinhochstein
\* Created Mon Jun 02 20:41:25 EDT 2014 by lorinhochstein
