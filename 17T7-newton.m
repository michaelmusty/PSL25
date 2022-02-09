// phi0: 15, 1^2
// phi1: 2^6, 1^5
// phioo: 4^4, 1^1
R0<b,c,d0,d2,d3,e0,e1,e2,e3,e4,e5,f0,f1,f2,f3,f4,lc> := PolynomialRing(QQ,17);
R<x> := PolynomialRing(R0);

phi0 := lc*(x^2 + b);
phioo := (x^4 + d3*x^3 + d2*x^2 + x + d0)^4*(x-c);
phi1 := (-1)*(x^6 + e5*x^5 + e4*x^4 + e3*x^3 + e2*x^2 + e1*x + e0)^2*(x^5 + f4*x^4 + f3*x^3 + f2*x^2 + f1*x + f0);

eqns := Coefficients(phi0 - (phi1 + phioo));
