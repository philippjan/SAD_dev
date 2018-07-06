[number/-s]

Signature NatSort.  A natural number is a notion.

Let i,j,k,l,m,n denote natural numbers.

Signature ZeroNat.  0 is a natural number.

Let x is nonzero stand for x != 0.

Signature SuccNat.  succ n is a nonzero natural number.

Axiom NatExtr.      For every nonzero m there exists n
                                    such that m = succ n.

Axiom SuccEqu.      succ m = succ n  =>  m = n.

Signature IHOrd.    m -<- n is an atom.
Axiom IH.           n -<- succ n.

[scalar/-s]

Signature ScSort.   A scalar is a notion.

Let u,v,w,x,y,z denote scalars.

Signature SZeroSc.  00 is a scalar.
Signature SumSc.    x + y is a scalar.
Signature MulSc.    x * y is a scalar.
Signature NegSc.    -x is a scalar.

Let x - y stand for x + -y.
Let sq x stand for x * x.

Axiom ScZero.   x + 00 = x  and 00 + x = x
            and x * 00 = 00 and 00 * x = 00
            and x + -x = 00 and -x + x = 00
            and --x = x and -00 = 00.

Axiom Arith.    (x + y) + z = x + (y + z) and x + y = y + x
            and (x * y) * z = x * (y * z) and x * y = y * x.

Axiom Distr.    x * (y + z) = (x * y) + (x * z)
            and (x + y) * z = (x * z) + (y * z).

Lemma Distr2.   (x + y) * (u + v) =
    ((x * u) + (x * v)) + ((y * u) + (y * v)) (by Distr).
Indeed  (x + y) * (u + v) =
                (x * (u + v)) + (y * (u + v)) (by Arith).

Axiom MNeg.     x * -y = -(x * y) and -x * y = -(x * y).
Lemma MDNeg.    -x * -y = x * y.


Signature Less. x <= y is an atom.

Let x is nonnegative stand for 00 <= x.

Axiom LERef.    x <= x.
Axiom LEASm.    x <= y <= x => x = y.
Axiom LETrn.    x <= y <= z => x <= z.
Axiom LEMon.    x <= y /\ u <= v => x + u <= y + v.
Axiom LEMonM.   x <= y /\ 00 <= u <= v => x * u <= y * v.
Axiom LETot.    x <= y \/ y <= x.

Axiom PosMon.   00 <= x /\ 00 <= y =>
                                00 <= x + y /\ 00 <= x * y.
Axiom SqPos.    00 <= sq x.
Axiom Sqrt.     00 <= x /\ 00 <= y /\ sq x = sq y => x = y.

[vector/-s] [dimension/-s]

Signature VcSort.   A vector is a notion.

Let p,q,r,s,t denote vectors.

Signature DimNat.   The dimension of s is a natural number.

Let Dim x stand for the dimension of x.

Signature ElmSc.    s[n] is a scalar.

Definition DefInit. Let Dim s != 0.
  init s is a vector such that succ Dim init s = Dim s
    and for every natural number n  (init s)[n] = s[n].

Lemma EqInit.   Let Dim s = Dim t != 0.
                Then Dim init s = Dim init t.

Signature ScPr. Let Dim s = Dim t.
                s ** t is a scalar.

Axiom DefSPZ.   Let Dim s = Dim t = 0.
                s ** t = 00.

Axiom DefSPN.   Let Dim s = Dim t != 0.
                s ** t = (init s ** init t)
                       + (s[Dim s] * t[Dim t]).

Let scsq x stand for x ** x.

Lemma ScSqPos.  For all s scsq s is nonnegative.
Proof by induction on Dim s.
  Assume that Dim s is nonzero.
  Then scsq s = scsq init s + sq s[Dim s].
  scsq init s and sq s[Dim s] are nonnegative.
  Hence the thesis.
qed.

Theorem Cauchy.
  For all s,t if Dim s = Dim t then
    sq (s ** t) <= scsq s * scsq t.
Proof by induction on Dim s.

  Let Dim s = Dim t.
  Assume that Dim s != 0.

  Take a vector p equal to init s.
  Take a vector q equal to init t.

  (A) Take a scalar A equal to s[Dim s].
  (B) Take a scalar B equal to t[Dim t].
  (C) Take a scalar C equal to scsq p.
  (D) Take a scalar D equal to scsq q.
  (E) Take a scalar E equal to p ** q.
  (F) Take a scalar F equal to sq A.
  (G) Take a scalar G equal to sq B.
  (H) Take a scalar H equal to A * B.
  (R) Take a scalar R equal to C * G.
  (P) Take a scalar P equal to E * H.
  (S) Take a scalar S equal to F * D.
  (N) Take a scalar N equal to R * S.

  We have sq E <= C * D.

  P + P <= R + S.
  proof.
    Let us show that sq P <= N.
      sq P = sq H * sq E (by Arith).
      N = sq H * (C * D) (by Arith).
      Hence the thesis (by LERef,LEMonM,SqPos).
    end.

    Let us show that sq P + sq P <= sq R + sq S.
      R * -S = -N and -S * R = -N and sq -S = sq S.
      sq (R - S) = (sq R - N) + (-N + sq S).
      sq (R - S) = (sq R - N) + (sq S - N) (by Arith).
      sq (R - S) = ((sq R + sq S) - N) - N (by Arith).
      (sq (R - S) + N) + N = sq R + sq S (by Arith,ScZero).
      sq (R - S) is nonnegative.
      N + N <= sq R + sq S (by LERef,LEMon,ScZero).
      Hence the thesis (by LEMon, LETrn).
    end.

    Let us show that sq (P + P) <= sq (R + S) (by Distr2).
      ((sq P + sq P) + sq P) + sq P  <=
          ((sq R + sq S) + N) + N (by LEMon).
      ((sq R + N) + sq S) + N = (sq R + N) + (sq S + N).
      (sq P + sq P) + (sq P + sq P)  <=
          (sq R + (R * S)) + ((S * R) + sq S) (by Arith).
    end.

    Assume the contrary.
    We have R + S <= P + P.
    R + S, P + P are nonnegative.
    Then sq (R + S) <= sq (P + P).
    Then R + S = P + P (by LEASm,Sqrt).
    We have a contradiction.
  end.

  We have sq (E + H) <= (C + F) * (D + G) (by Distr2).
  proof.
    sq E + ((P + P) + sq H)  <=
      (C * D) + ((R + S) + sq H) (by LERef,LEMon).
    (P + P) + sq H = (E*H) + ((H*E) + sq H).
    (sq E + (E*H)) + ((H*E) + sq H)  <=
      ((C*D)+(C*G)) + ((F*D)+(F*G)) (by Arith).
  end.

  Hence the thesis (by DefSPN).
qed.
