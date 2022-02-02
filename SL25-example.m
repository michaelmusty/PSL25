AttachSpec("spec");
SetVerbose("Shimura",true);
G := SmallGroup(120,5);
triples := PassportRepresentatives(G);
/*
genera := [];
for i := 1 to #triples do
  sigma := triples[i][2][1];
  Gamma := TriangleSubgroup(sigma : Simplify := 0);
  Append(~genera, Genus(Gamma));
end for;
*/
sigma := [ PermutationGroup<24 |  
  \[ 2, 4, 6, 8, 3, 9, 12, 1, 5, 14, 15, 13, 17, 11, 10, 20, 7, 22, 23, 21, 24, 19, 18, 16 ],
  \[ 3, 5, 7, 9, 10, 11, 1, 6, 13, 2, 8, 16, 4, 18, 19, 20, 21, 22, 23, 12, 24, 14, 15, 17 ]:
   Order := 120 > |
   [ 3, 5, 7, 9, 10, 11, 1, 6, 13, 2, 8, 16, 4, 18, 19, 20, 21, 22, 23, 12, 24, 14, 15, 17 ],
   [ 7, 10, 19, 13, 16, 21, 12, 11, 18, 14, 15, 6, 17, 3, 9, 4, 5, 8, 2, 20, 1, 22, 23, 24 ],
   [ 1, 2, 21, 4, 19, 18, 14, 8, 16, 17, 12, 20, 15, 22, 23, 7, 24, 10, 11, 5, 13, 9, 3, 6 ]
   ];
Gamma := TriangleSubgroup(sigma);
X, phi := BelyiMap(Gamma : prec := 80);
