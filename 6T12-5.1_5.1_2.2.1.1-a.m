
// Belyi maps downloaded from the LMFDB on 17 January 2022.
// Magma code for Belyi map with label 6T12-5.1_5.1_2.2.1.1-a


// Group theoretic data

d := 6;
i := 1;
G := TransitiveGroup(d,i);
sigmas := [[Sym(6) | [2, 3, 4, 6, 5, 1], [5, 1, 3, 2, 6, 4], [5, 2, 4, 3, 1, 6]]];
embeddings := [ComplexField(15)![1.0, 0.0]];

// Geometric data

// Define the base field
//K<nu> := RationalsAsNumberField();
K := Rationals();
// Define the curve
X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
// Define the map
KX<x> := FunctionField(X);
phi := (128/125*x^6+128/125*x^5)/(x^6+4/5*x^5-4/5*x^4-32/25*x^3-16/25*x^2+64/125*x+64/125);
