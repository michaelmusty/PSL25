R<a0,a1,a2,a3,a4,a5,r1,r2,r3,r4,r5,r6,x> := PolynomialRing(QQ,13);
a := [R.i : i in [1..6]];
r := [R.i : i in [7..12]];
f := &*[x-el : el in r];
S<s1,s2,s3,s4,s5,s6> := PolynomialRing(QQ,6);
mp := hom< S -> R | r >;
syms := [mp(ElementarySymmetricPolynomial(S,i)) : i in [1..6]];
gens := [a[i] - syms[6-i+1] : i in [1..6]];
gens cat:= [f];
I := ideal< R | gens >;
EliminationIdeal(I, {a0,a1,a2,a3,a4,a5,x});
