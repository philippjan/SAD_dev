[number/-s]
Signature Real. A real number is a notion.

Let x,y,z denote real numbers.

###Addition
Signature Add. x + y is a real number.

Axiom AssAdd. (x + y) + z = x + (y + z).
Axiom ComAdd. x + y = y + x.
Signature Zero. 0 is a real number such that for every real number x x + 0 = x.
Signature Neg. -x is a real number such that x + (-x) = 0.

Axiom BubbleAdd. x + (y + z) = y + (x + z).

Lemma ZeroUnique.
Let a be a real number. Assume that for all real numbers x x + a = x. Then a = 0.


Lemma NegUnique.
Let a, x be real numbers. Assume that x + a = 0. Then a = -x.

Lemma NegOfZero. -0 = 0.

Let x - y stand for x + (-y).

Lemma MinusRule1.
- (x + y) = (-x) + (-y).


Lemma MinusRule2.
-(-x) = x.

Lemma MinusRule3.
-(y - x) = (x - y).


###Multiplication
Signature Mult. x * y is a real number.
Axiom AssMult. (x * y) * z = x * (y * z).
Axiom ComMult. x * y = y * x.
Signature One. 1 is a real number such that for every real number x x * 1 = x.
Signature Inverse. Assume not x = 0. inv(x) is a real number such that x * inv(x) = 1.


Axiom ZeroNotOne. not 1 = 0.
Axiom Distrib. (x * y) + (x * z) = x * (y + z).
Axiom DistribDummy. (y * x) + (z * x) = (y + z) * x.

Lemma OneUnique.
Let a be a real number. Assume for all real numbers x x * a = x. Then a = 1.

Lemma ZeroMult. 0 * x = 0.

Lemma InvNotZero.
Assume not x = 0. Then not inv(x) = 0.

Lemma InvUnique.
Let a be a real number. Assume x * a = 1. Then (not x = 0) and a = inv(x).

Lemma NoZeroDivisors.
Assume x != 0 and y != 0. Then x * y != 0.


Lemma InvRule1.
Assume not x = 0. then inv(inv(x)) = x.



Lemma InvRule2. Assume x != 0 and y !=0. Then x * y != 0 and inv(x * y) =  inv(x) * inv(y).



Lemma MinusRule4. -x = (-1) * x.





###Ordering

Signature positive.
Let x be a real number. pos(x) is an atom.

Let x is positive stand for pos(x).

Definition nonnegativeAdj.
Let x be a real number. x is nonnegative iff x = 0 \/ pos(x).

Lemma PosIsNonNeg.
Every positive real number is nonnegative.

Axiom TrichExi. pos(x) \/ x = 0 \/ pos(-x).
Axiom TrichUnique. not (pos(x) /\ pos(-x)) /\ not pos(0).
Axiom AddClosed. (pos(x) /\ pos(y)) => pos(x + y).
Axiom MultClosed. (pos(x) /\ pos(y)) => pos(x * y).

Definition less. x < y iff pos(y - x).
Let x > y stand for y < x.

Definition leq. x =< y iff (x < y \/ x = y).
Let x >= y stand for y =< x.

Lemma TotalityOfOrderExi.
(x < y \/ y < x \/ y = x).

Lemma LargerMult.
Assume x is positive and a is a real number such that 1 < a. Then x < a * x.


Lemma SmallerMult.
Assume x is positive and a is a real number such that a < 1. then a * x < x.


Lemma TotalityOfOrderUnique.
not((x < y /\ y < x) \/ (x < y /\ y = x) \/ (y < x /\ y = x)).


Lemma TransitivityOfOrder.
x < y /\ y < z => x < z.



Lemma TranslationInvariance.
x < y => x + z < y + z.


Lemma AddInvariance.
Let a,b be real numbers. x < a /\ y < b => x + y < a + b.

Lemma PosAdd.
Assume pos(y). Then x < x + y.


Lemma LeqAddInvariance.
Let a,b be real numbers. x =< a /\ y =< b => x + y =< a + b.


Lemma OrdMirror.
x < y => -y < -x.


Lemma OrdMirrorLeq.
x =< y => -y =< -x.


Lemma MultInvariance.
(x < y /\ pos (z)) => z * x < z * y.






Lemma OnePos.
pos(1).


Lemma PosMono.
(pos(x) /\ x < y) => pos(y).

Lemma NonNegMono.
Assume x is nonnegative. Assume x =< y. Then y is nonnegative.

Lemma NonNegMultInvariance.
Assume x,y,a,b are nonnegative real numbers. Assume x < a /\ y < b. x * y < a * b.


Lemma MinusAndMinus.
Assume pos(-x) and pos(-y). Then pos(x*y).

Lemma PosSquare.
Assume not x = 0. Then pos(x*x).

Lemma InvMono.
If pos(x) then pos(inv(x)).


Lemma InvIneq.
Assume x is positive.
inv(x) < 1 <=> 1 < x.


Lemma MixedTransitivity.
x =< y /\ y < z => x < z.


Lemma LeqTransitivity.
(x =< y) /\ (y =< z) => x =< z.


Signature Maximum.
max(x,y) is a real number such that (x =< y => max(x,y) = y) /\ (y =< x => max(x,y) = x).



Lemma MaxIneq.
x =< max(x,y).


Lemma MaxSym.
max(x,y) = max(y,x).


###Absolute Value
Signature Abs.
abs(x) is a real number.

Axiom AbsValue.
(pos(x) => abs(x) = x) /\ (pos(-x) => abs(x) = -x) /\ abs(0) = 0.


Lemma NonNegAbsValue.
If x is nonnegative then abs(x) = x.

Lemma NonNegAbs.
abs(x) is nonnegative.


Lemma AbsIneq1.
x =< abs(x).

Lemma AbsPosNeg.
abs(x) = abs(-x).

Lemma AbsIneqCharac1.
(abs(x) =< y) <=> -y =< x =< y.


Lemma AbsIneqCharac2.
(abs(x) =< y) <=> (x =< y /\ -x =< y).


Lemma AbsStrongIneqCharac1.
(abs(x) < y) <=> (-y < x < y).


Lemma AbsStrongIneqCharac2.
(abs(x) < y) <=> (x < y /\ -x < y).


Lemma AbsTriangleIneq.
abs(x + y) =< abs(x) + abs(y).

Lemma AbsPos.
If not x = 0 then pos(abs(x)).

Lemma AbsMult.
abs(x * y) = abs(x) * abs(y).


###Distance

Signature Dist.
dist(x,y) is a nonnegative real number.

Axiom DistDefinition. dist(x,y) = abs(x - y).

Lemma IdOfInd.
dist(x,y) = 0 <=> x = y.


Lemma DistSymm. dist(x,y) = dist(y,x).


Lemma DistTriangleIneq. dist(x,z) =< dist(x,y) + dist(y,z).

[exit]




[Main] sections 259 - goals 53 - failed 19 - trivial 1 - proved 33 - equations 0
[Main] symbols 513 - checks 0 - trivial 0 - proved 0 - unfolds 294
[Main] parser 00:00.10 - reason 00:00.07 - simplifier 00:00.00 - prover 07:15.73/00:03.87
[Main] total 07:15.92


[Main] sections 259 - goals 53 - failed 9 - trivial 1 - proved 43 - equations 0
[Main] symbols 513 - checks 0 - trivial 0 - proved 0 - unfolds 166
[Main] parser 00:00.08 - reason 00:00.05 - simplifier 00:00.00 - prover 04:00.02/00:03.42
[Main] total 04:00.15



