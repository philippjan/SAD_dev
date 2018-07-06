[read Forster/Reals.ftl]

Signature NaturalNum.
A natural number is a real number.

Axiom ZeroNat.
0 is a natural number.

Axiom OneNat.
1 is a natural number.

Let m,n denote natural numbers.

Axiom AddClosed.
m + n is a natural number.

Axiom MultClosed.
m * n is a natural number.

Axiom MinClosed.
Assume m =< n. n - m is a natural number.


Axiom PosNaturals.
Let n be a natural number. (not n = 0 => pos(n)).


Let 2 denote 1 + 1.


Lemma PosTwo.
pos(2).

Lemma TwoNotZero.
not 2 = 0.

###Archimedes

Axiom ArchimedeanAxiom.
Let x,y be real numbers. If (pos(x) /\ pos(y)) then there exists a natural number
n such that y < n * x.





###Some Operations.


Lemma maxtype.
Let n,m be natural numbers. Then max(n,m) is a natural number.
Proof.
Case n =< m. Obvious.
Case m =< n. Obvious.
qed.
[exit]
