[integer/-s] [program/-s] [code/-s]
[succeed/-s] [decide/-s] [halt/-s]

Signature PrgSort.  A program is a notion.
Signature IntSort.  An integer is a notion.

Let U,V,W stand for programs.
Let x,y,z stand for integers.

Signature CodeInt.  A code of W is an integer.
Axiom ExiCode.      Every program has a code.

Signature HaltRel.  W halts on x is an atom.
Signature SuccRel.  W succeeds on x with input y is an atom.

Definition DefDH.   W decides halting iff
    for every z and every code x of every V
        W succeeds on x with input z iff V halts on z.

Axiom Cantor.       Let W decide halting.
    Then there exists V such that for every y
    V halts on y iff W does not succeed on y with input y.

Proposition.        No program decides halting.
Proof.
Assume the contrary.
Take a program W that decides halting.
Take V such that for every y 
V halts on y iff W does not succeed on y with input y. 
Then for any code c of V W succeeds on c with input c iff
W does not succeed on c with input c. Contradiction.
qed.
