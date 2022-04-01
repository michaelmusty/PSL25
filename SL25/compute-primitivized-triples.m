AttachSpec("spec");
G := SmallGroup(120,5);
assert IsIsomorphic(G,SL(2,5));
triples := PassportRepresentatives(G);
printf "# of triples = %o\n", #triples;

// compute genera
genera := [];
for i := 1 to #triples do
  sigma := triples[i][2][1];
  Append(~genera, Genus(sigma));
end for;
printf "genera = %o\n", genera;

load "~/github/primitive-belyi-maps/code/primitivize.m";
// primitivize
triples_prim := [* *];
for pass in triples do
  pass_prim := [* *];
  for sigma in pass[2] do
    sigma_prim := Primitivize(sigma);
    Append(~pass_prim, sigma_prim);
  end for;
  Append(~triples_prim, pass_prim);
end for;
printf "# of primitivized triples = %o\n", #triples_prim;

genera_prim := [];
for i := 1 to #triples_prim do
  sigma := triples_prim[i][1];
  Append(~genera_prim, Genus(sigma));
end for;
printf "primitive genera = %o\n", genera_prim;

triples_list := [];
for i := 1 to #triples do
  for j := 1 to #triples[i][2] do
    Append(~triples_list, triples[i][2][j]);
  end for;
end for;

triples_prim_list := [triples_prim[i][1] : i in [1..#triples_prim]];
