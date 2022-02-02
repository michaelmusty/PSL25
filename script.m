Attach("utils.m");
Attach("enumerating_triples.m");
load "6T12-5.1_5.1_2.2.1.1-a.m";

Y := ExtractRoot(X, x/(x+1), 2);
Ybar := ProjectiveClosure(Y);
phi2 := map< Ybar -> X | [Ybar.1, Ybar.3]>;
Degree(phi2);
