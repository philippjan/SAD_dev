
Signature.
Let M,N be sets. Prod(M,N) is a set. with constructors any x, any y | x is an element of M, y is an element of N | (x,y)

Signature.
Let M be a set. A list of M is a notion. with constructors - | - | empty, any x, any L | x is an element of M, L is a list of M | cons(x,L)

Signature.
Let M be a set. list(M) is a set S such that every element of S is a list of M and every list of M is an element of S.

Signature.
Let M be a set. append(M) is a function f such that Dom(f) = Prod(list(M),list(M)) and for every list L of M (append(M)[(empty,L)] = L and for every element x of M and every list L2 of M append(M)[(cons(x,L2),L)] = cons(x, append(M)[(L2,L)])).

Proposition. Let M be a set. For every list L of M append(M)[(L,empty)] = L.
Proof by structure induction. Obvious.
