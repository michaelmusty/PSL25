// Example 4.3.4 in Couvillion's thesis
/*
  C2 := CyclicGroup(2);
  C3 := CyclicGroup(3);
  W := WreathProduct(C3,C2);
  D0 := DirectProduct(C3,C2);
  D := [el : el in Subgroups(W : OrderEqual := (#C3*#C2)) | IsIsomorphic(el`subgroup, D0)][1]`subgroup;
  T := Transversal(W,D);
  p := RelativeInvariant(W,D);
  R := Parent(p);
  S<y> := SLPolynomialRing(R,1);
  h := &*[y - Evaluate(p, [R.(i^t) : i in [1..Degree(W)]]) : t in T];

  pp := MultivariatePolynomial(p);
  R0<[x]> := Parent(pp);
  SS<yy> := PolynomialRing(R0);
  hh := &*[yy - Evaluate(pp, [R0.(i^t) : i in [1..Degree(W)]]) : t in T];
*/

// copypasta

// Example 4.3.4 in Couvillion's thesis
C2 := CyclicGroup(2);
C3 := CyclicGroup(3);
W := WreathProduct(C3,C2);
D0 := DirectProduct(C3,C2);
D := [el : el in Subgroups(W : OrderEqual := (#C3*#C2)) | IsIsomorphic(el`subgroup, D0)][1]`subgroup;
T := Transversal(W,D);
p := RelativeInvariant(W,D);
p;
R := Parent(p);
S<y> := PolynomialRing(R);
h := &*[y - Evaluate(p, [R.(i^t) : i in [1..Degree(W)]]) : t in T];
h;
cs := Coefficients(h);
invs := [];
for pi in Sym(6) do
  inv_bool := true;
  for c in cs do 
    if not IsInvariant(c,pi) then
      inv_bool := false;
    end if;
  end for;
  if inv_bool then
    Append(~invs, pi);
  end if;
end for;

// group under which coefficients are invariant
K := sub< Sym(6) | invs>;
#K;    
ReduceGenerators(~K);

// compute G-relative H-invariant resolvent
pp := MultivariatePolynomial(p);
R0<[x]> := Parent(pp);
R1 := ChangeRing(R0,QQ);
R3<x1,x2,x3,x4,x5,x6,t0,t1> := PolynomialRing(QQ,8);
SS<yy> := PolynomialRing(R0);
hh := &*[yy - Evaluate(pp, [R0.(i^t) : i in [1..Degree(W)]]) : t in T];
S<s1,s2,s3,s4,s5,s6> := PolynomialRing(QQ,6);
mp_S := hom< S -> R3 | [R3.i : i in [1..6]] >;
syms := [mp_S(ElementarySymmetricPolynomial(S,i)) : i in [1..6]];
cs_hh := Coefficients(hh);

mp_x := hom<R1 -> R3 | [x1,x2,x3,x4,x5,x6]>;
//gens := [mp_x(syms[1]), mp_x(syms[2]), -mp_x(syms[3]) - (-2*t0+t1), mp_x(syms[4]), mp_x(syms[5]), mp_x(syms[6]) - (t0^2 - t0*t1 + t1^2)];
gens := [(syms[1]), (syms[2]), -(syms[3]) - (-2*t0+t1), (syms[4]), (syms[5]), (syms[6]) - (t0^2 - t0*t1 + t1^2)];
I := ideal< R3 | gens >;
EliminationIdeal(I, {t0,t1});

/*
  pp := MultivariatePolynomial(p);
  R0 := Parent(pp);
  SS<yy> := PolynomialRing(R0);
  hh := &*[yy - Evaluate(pp, [R0.(i^t) : i in [1..Degree(W)]]) : t in T];
  hh;
  R0<[x]> := Parent(pp);
  SS<yy> := PolynomialRing(R0);
  hh := &*[yy - Evaluate(pp, [R0.(i^t) : i in [1..Degree(W)]]) : t in T];
  hh;
  h;
  MultivariatePolynomial(h);
  cs_hh := Coefficients(hh);
  cs_hh[1];
  SFA;
  BaseRing(cs_hh[1]);
  Parent(cs_hh[1]);
  R;
  RR;
  R0;
  Sym;
  sym;
  sym := SFA(R0);
  sym!cs_hh[1];
  SFA.1;
  sym.1;
  sym.2;
  Eltseq($1);
  R0;
  R0!sym.1;
  sym;
  sym.[1,1,1];
  R0!$1;
  ChangeRing(R0,QQ);
  R1 := $1;
  sym;
  sym := SFA(R1);
  Parent(cs_hh[1]);
  Parent(R1!cs_hh[1]);
  R1!cs_hh[1];
  sym.[1,1,1];
  R1!$1;
  sym := SFA(QQ);
  R0!sym.[1,1,1];
  R1!sym.[1,1,1];
  S;
  R3<x1,x2,x3,x4,x5,x6,t0,t1> := PolynomialRing(QQ,8);
  R3!sym.[6]
  ;
  R3!sym.[1,1,1,1,1,1];
  R2;
  R1;
  R1!sym.[1,1,1,1,1,1];
  hom<R1 -> R3 | [x1,x2,x3,x4,x5,x6]>;
  mp_x := hom<R1 -> R3 | [x1,x2,x3,x4,x5,x6]>;
  mp_x(R3!sym.[1,1,1,1,1,1]);
  R1;
  R2;
  mp_x(R1!sym.[1,1,1,1,1,1]);
  sym.[1];
  R1!$1;
  R1!sym.[2];
  R1!sym.[1,1];
  p;
  R1!sym.[1,1,1];
  vecs := [[1 : i in [1..m]] : m in [1..6]];
  vecs;
  ss := [R1 | sym.el : el in vecs];
  ss;
  gens := [mp_x(ss[1]), mp_x(ss[2]), -mp_x(ss[3]) - (-2*t0+t1), ss[4], ss[5], ss[6] - (t0^2 - t0*t1 + t1^2)];
  gens := [mp_x(ss[1]), mp_x(ss[2]), -mp_x(ss[3]) - (-2*t0+t1), mp_x(ss[4]), mp_x(ss[5]), mp_x(ss[6]) - (t0^2 - t0*t1 + t1^2)];
  Parent(gens[1]);
  R3;
  I := ideal< R3 | gens >;
  EliminationIdeal(I, {t0,t1});
  EliminationIdeal(I, {x1,x2,x3,x4,x5,x6});
  g;
  cs_hh[1];
  cs_hh[2];
  cs_hh[3];
  cs_hh[4];
  h;
  hh;
  I;
  p;
  h;
  hh;
  Parent(h);
  S;
  R;
  gens;
  gens[3];
  I;
  Parent(I);
  Parent(gens[1]);
  EliminationIdeal(I, {t0,t1});
  Basis($1);
  EliminationIdeal(I, {x1,x2,x3,x4,x5,x6});
  h;
  hh;
  Parent(hh);
  R3;
  R3<x1,x2,x3,x4,x5,x6,t0,t1,y> := PolynomialRing(QQ,9);
  I;
  Parent(hh);
  BaseRing($1);
  mp_x;
  R1;
  mp_x := hom<R1 -> R3 | [x1,x2,x3,x4,x5,x6]>;
  Parent(hh);
  hom< Parent(hh) -> R3 | mp_x, y >;
  hom< Parent(hh) -> R3 | mp_x, [y] >;
  Codmain(mp_x);
  Codomain(mp_x);
  $1 eq R3;
  Domain(mp_x);
  $1 eq BaseRing(Parent(hh));
  R1;
  mp_x := hom<BaseRing(hh) -> R3 | [x1,x2,x3,x4,x5,x6]>;
  mp_y := hom< Parent(hh) -> R3 | mp_x, y >;
  gens := [mp_x(ss[1]), mp_x(ss[2]), -mp_x(ss[3]) - (-2*t0+t1), mp_x(ss[4]), mp_x(ss[5]), mp_x(ss[6]) - (t0^2 - t0*t1 + t1^2)];
  I := ideal< R3 | gens cat [mp_y(hh)] >;
  EliminationIdeal(I, {t0,t1,y});
*/
