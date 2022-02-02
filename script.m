Attach("utils.m");
Attach("enumerating_triples.m");
load "6T12-5.1_5.1_2.2.1.1-a.m";

Y := ExtractRoot(X, x/(x+1), 2);
Ybar := ProjectiveClosure(Y);
phi2 := map< Ybar -> X | [Ybar.1, Ybar.3]>;
phi_mp := ProjectiveMap(phi);
phi_comp := phi2*phi_mp;
DefiningEquations(phi_comp);
KYbar<x,y> := FunctionField(Ybar);
eqns := DefiningEquations(phi_comp);
phi_new := Evaluate(eqns[1], [x,y,1])/Evaluate(eqns[2], [x,y,1]);

phi_old := phi;
phi := phi_new;

// copy-pasta'd from PlaneEquation in LLL.m in BelyiDB
  KC := Parent(phi);
  C := Curve(KC);
  K := BaseRing(C);
  nu := K.1;
  phi0 := Numerator(phi);
  phioo := Denominator(phi);
C;
    KC<x,y> := KC;
    R<X,Y,Phi,v> := PolynomialRing(K,4);
    h := hom< KC -> R | [X,Y]>;
    curve_eqn := DefiningEquation(AffinePatch(C,1));
    h_curve := hom< Parent(curve_eqn) -> R | [X,Y] >;
    // need last equation to avoid points where phioo = 0
    I := ideal< R | h_curve(curve_eqn), h(phioo)*Phi - h(phi0), v*h(phioo) - 1>;
    // eliminate X and v to obtain plane equation
    basis := Basis(EliminationIdeal(I,{Y,Phi}));
    assert #basis eq 1;
    new_eqn := basis[1];
    S<x,y> := PolynomialRing(K,2);
    h_plane := hom< Parent(new_eqn) -> S | [0,y,x,0] >;
  C_plane := Curve(AffineSpace(S),h_plane(new_eqn));
C_plane;
// returns x*y^12 + 76/5*x*y^10 + 44*x*y^8 - 96*x*y^6 + 112*x*y^4 - 64*x*y^2 + 64/5*x - 128/5*y^10

KC_plane<x> := FunctionField(C_plane);
Support(Divisor(x));
Support(Divisor(x));
Support(Divisor(x-1));
Support(Divisor(phi));
Support(Divisor(phi-1));
C_plane;

// now using Sage, computed monodromy group
/*
  sage: R.<x,y> = PolynomialRing(QQ,2);
  ....: f = x*y^12 + 76/5*x*y^10 + 44*x*y^8 - 96*x*y^6 + 112*x*y^4 - 64*x*y^2 + 64/5*x - 128/5*y^10
  ....: C = Curve(f)
  ....:
  sage: S = C.riemann_surface()
  ....: S.monodromy_group()
*/
// returned // new minimal polynomial: a8-104a6+2666a4+1976a2+72361
// [(0,1,4,3,2)(7,8,9,11,10), (0,11)(1,9,8,6,7,10,2,3,5,4), (0,9)(2,11)(4,5)(6,7)]

// It turns out that this triple generates C_2 x A_5, not SL(2,5) :(

S0 := Sym({0..11});
sigma0 := S0!(0,1,4,3,2)(7,8,9,11,10);
sigma1 := S0!(0,11)(1,9,8,6,7,10,2,3,5,4);
sigmaoo := S0!(0,9)(2,11)(4,5)(6,7);
sigma := [sigma0, sigma1, sigmaoo];
G := sub< S0 | sigma>;
TransitiveGroupIdentification(G); // returns 12T76
IsIsomorphic(G, SL(2,5)); // returns false
