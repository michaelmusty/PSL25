AttachSpec("spec");
QQ := Rationals();
L<nu> := QuadraticField(5);
R<t,x> := PolynomialRing(QQ,2);
// genus 0
F := t*x^17 + 15/4*t*x^16 + 69/10*t*x^15 + 359/40*t*x^14 + 2943/320*t*x^13 + 48301/6400*t*x^12 + 328079/64000*t*x^11 + 745869/256000*t*x^10 + 27691787/20480000*t*x^9 + 41887701/81920000*t*x^8 + 60286491/409600000*t*x^7 + 41159017/1638400000*t*x^6 - 2535961/13107200000*t*x^5 - 602647659/262144000000*t*x^4 - 2137207039/2621440000000*t*x^3 - 1355028301/10485760000000*t*x^2 - 16350628239/1677721600000000*t*x - 1908029761/6710886400000000*t + 8192/263671875*x^2 + 512/48828125;
S<s> := PolynomialRing(L);
t0s := [a+b*nu : a,b in [-10..10]];
//t0s := [t0 : t0 in t0s | not t0 in [0,1]];
t0s := [t0 : t0 in t0s | not t0 in QQ];
t0s := SetToSequence(SequenceToSet(t0s));
for t0 in t0s do
  printf "evaluating at %o\n", t0;
  Fev := Evaluate(F, [t0, s]);
  Grel := GaloisGroup(Fev);
  assert TransitiveGroupIdentification(Grel) eq 7;
  print "relative extension has Galois group 17T7";
  M := ext< L | Fev>;
  Mabs := AbsoluteField(M);
  Mabs_poly := DefiningPolynomial(Mabs);
  Mabs_poly := Polredbest(Mabs_poly);
  printf "polredbest-ed polynomial for extension over QQ:\n%o\n", Mabs_poly;
  G, seq, data := GaloisGroup(Mabs_poly);
  k := TransitiveGroupIdentification(G);
  if k ne 88 then
    print "\n\nsmaller than generic Galois group found!\n\n";
    print t0;
    print G;
  end if;
end for;