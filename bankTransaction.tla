-------------------------------- MODULE Bank --------------------------------
EXTENDS Integers

\* BEGIN TRANSLATION
VARIABLES accHolders, account, pc

(* define statement *)
NoOverdrafts == \A p \in accHolders: account[p] >= 0
EventuallyConsistent == <>[](account["A"] + account["B"] = 100)

VARIABLES sender, receiver, balance

vars == << accHolders, account, pc, sender, receiver, balance >>

Case == (1..2)

Init == (* Global variables *)
        /\ accHolders = {"A", "B"}
        /\ account = [p \in accHolders |-> 50]
        (* Process Transaction *)
        /\ sender = [self \in 1..2 |-> "A"]
        /\ receiver = [self \in 1..2 |-> "B"]
        /\ balance \in [1..2 -> 1..account[sender[CHOOSE self \in  1..2 : TRUE]]]
        /\ pc = [self \in Case |-> "Transfer"]

Transfer(self) == /\ pc[self] = "Transfer"
                          /\ IF balance[self] <= account[sender[self]]
                                THEN /\ account' = [account EXCEPT ![sender[self]] = account[sender[self]] - balance[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "Deposit"] /\ UNCHANGED << accHolders, sender, receiver, balance >>
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ account' = account /\ UNCHANGED << accHolders, sender, receiver, balance >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ account' = [account EXCEPT ![receiver[self]] = account[receiver[self]] + balance[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << accHolders, sender, receiver, balance >>

Transaction(self) == Transfer(self) \/ Deposit(self)

Next == (\E self \in 1..2: Transaction(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in Case: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in Case: pc[self] = "Done")

\* END TRANSLATION



=============================================================================

=============================================================================
\* Modification History
\* Last modified Tue Dec 04 19:10:26 EST 2018 by Varsh
\* Created Sat Dec 01 18:40:49 EST 2018 by Varsh
