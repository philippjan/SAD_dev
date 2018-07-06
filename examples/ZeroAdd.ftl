[number/numbers]

Signature Nat.
    A natural number is a notion.
Signature Zer.
    0 is a natural number.
Signature Suc.
    Let i be a natural number.
    succ i is a natural number.
Signature Add.
    Let i,j be natural number.
    i + j is a natural number.
Signature Ord.
    Let i,j be natural numbers.
    i -<- j is an atom.

Axiom ZerSuc.
    For any natural number i if i != 0 then
    there exists a natural number j such that succ j = i.
Axiom AddZer.
    For any natural number i (i + 0 = i).
Axiom AddSuc.
    For all natural numbers i,j (i  + succ j  = succ (i + j)).
Axiom OrdSuc.
    For any natural number i (i -<- succ i).



Lemma ZerAdd.
    For any natural number i (0 + i = i).
Proof by induction.
    Let i be a natural number.

    Case i = 0.
    Obvious.

    Case i !=0.
        Take a natural number j such that succ j = i.
        We have j -<- i.
        Hence 0 + j = j.
        Then we have the thesis.
    end.
    qed.
