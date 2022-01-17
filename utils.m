// intrinsic IsoText(var::MonStgElt, lower::RngIntElt, upper::RngIntElt) -> MonStgElt
//   {returns text "var.lower, var.lower+1, ..., var.upper-1, var.upper".}
//   assert upper ge lower;
//   var_text := "";
//   if upper eq lower then
//     var_text *:= Sprintf("%o.%o", var, lower);
//   else
//     for i := lower to upper-1 by 1 do
//       var_text *:= Sprintf("%o.%o, ", var, i);
//     end for;
//     var_text *:= Sprintf("%o.%o", var, upper);
//   end if;
//   return var_text;
// end intrinsic;

// intrinsic SolvableBaseChange(s::SolvableDB, K::FldNum) -> SolvableDB
//   {Extend base field of object to K.}
//   assert assigned s`SolvableDBBelyiCurve and assigned s`SolvableDBBelyiMap;
//   X<[x]> := BaseChange(BelyiCurve(s), K);
//   rk := Rank(Generic(Ideal(X)));
//   phi := BelyiMap(s);
//   KX<[x]> := Parent(phi); // before base change (to rename variables)
//   KX<[x]> := FunctionField(X); // after base change
//   phi := eval Sprintf("return KX!(%o);", phi);
//   s`SolvableDBBelyiCurve := X;
//   s`SolvableDBBelyiMap := phi;
//   return s;
// end intrinsic;

intrinsic SolvableCheckResidueFields(D::DivCrvElt) -> BoolElt, Any
  {Computes the residue fields at places in support of D. Returns false, FldRat if these are all trivial. Returns true, Compositum of all residue fields if any residue fields are not trivial.}
  supp := Support(D);
  assert #supp gt 0;
  fields := [* *];
  non_trivial := false;
  for pt in supp do
    field := AbsoluteField(ResidueClassField(FunctionFieldPlace(pt)));
    if Degree(field) gt 1 then
      non_trivial := true;
    end if;
    Append(~fields, field);
  end for;
  if non_trivial eq false then
    return false, Rationals();
  else
    return_field := Rationals();
    for i := 1 to #fields do
      // return_field := Compositum(return_field, fields[i]);
      return_field := CompositeFields(return_field, fields[i])[1];
    end for;
    return true, AbsoluteField(return_field);
  end if;
end intrinsic;

intrinsic SolvableSetToDivisor(set::SetEnum[PlcCrvElt]) -> DivCrvElt
  {Given a set of places, return the divisor.}
  DivX := Parent(Divisor(Random(set)));
  D := DivX!0;
  for pt in set do
    D := D+Divisor(pt);
  end for;
  return D;
end intrinsic;

intrinsic SolvableRamificationDivisorUsingAllPoints(D::DivCrvElt) -> BoolElt, DivCrvElt
  {Attempt to find 1 dimensional Lspace using all points in D.}
  vprintf Solvable: "#supp(Divisor) = %o\n", #Support(D);
  worked := false;
  supp := Support(D);
  suppset := SequenceToSet(supp);
  subs := Subsets(suppset);
  for sub in subs do
    if #sub ne 0 and #sub ne #suppset then
      pos := SolvableSetToDivisor(sub);
      neg := SolvableSetToDivisor(suppset diff sub);
      supp, mult := Support(pos-neg);
      vprintf Solvable: "Checking divisor:\n%o\n%o\n", supp, mult;
      if Dimension(RiemannRochSpace(pos-neg)) eq 1 then
        vprintf Solvable: "It worked!\n";
        return true, pos-neg;
      else
        vprintf Solvable: "Didn't work >_<.\n";
      end if;
    end if;
  end for;
  return false, Parent(D)!0;
end intrinsic;

intrinsic SolvableDimensionOneLspacesUsingAllPoints(D::DivCrvElt) -> BoolElt, List
  {Find all 1 dimensional Lspace using all points in D. Return true if at least one such divisor.}
  supp := Support(D);
  suppset := SequenceToSet(supp);
  subs := Subsets(suppset);
  dimension_one_spaces := [* *];
  for sub in subs do
    if #sub ne 0 and #sub ne #suppset then
      pos := SolvableSetToDivisor(sub);
      neg := SolvableSetToDivisor(suppset diff sub);
      supp, mult := Support(pos-neg);
      vprintf Solvable: "Checking divisor:\n%o\n%o\n", supp, mult;
      if Dimension(RiemannRochSpace(pos-neg)) eq 1 then
        vprintf Solvable: "It worked!\n";
        Append(~dimension_one_spaces, pos-neg);
      else
        vprintf Solvable: "Didn't work >_<.\n";
      end if;
    end if;
  end for;
  if #dimension_one_spaces gt 0 then
    return true, dimension_one_spaces;
  else
    return false, [* Parent(D)!0 *];
  end if;
end intrinsic;

intrinsic SolvableRamificationToDivisor(ram::SeqEnum[BoolElt], Ds::List) -> DivCrvElt
  {Given ramification data and [D0, D1, Doo], return corresponding divisor.}
  assert #ram eq 3;
  ram0, ram1, ramoo := Explode(ram);
  assert #Ds eq 3;
  D0, D1, Doo := Explode(Ds);
  if ram0 then
    if ram1 then
      if ramoo then
        // 0,1,oo ramified
        return D0+D1+Doo;
      else
        // 0,1 ramified
        return D0+D1;
      end if;
    else
      if ramoo then
        // 0,oo ramified
        return D0+Doo;
      else
        // 0 ramified
        return D0;
      end if;
    end if;
  else
    if ram1 then
      if ramoo then
        // 1,oo ramified
        return D1+Doo;
      else
        // 1 ramified
        return D1;
      end if;
    else
      if ramoo then
        // oo ramified
        return Doo;
      else
        // unramified
        error "unramified...what?";
      end if;
    end if;
  end if;
end intrinsic;

intrinsic VarSeq(var::MonStgElt, lower::RngIntElt, upper::RngIntElt) -> SeqEnum[MonStgElt]
  {returns SeqEnum ["varlower", "varlower+1", ..., "varupper-1", "varupper"].}
  assert upper ge lower;
  var_seq := [];
  for i := lower to upper do
    Append(~var_seq, Sprintf("%o%o", var, i));
  end for;
  return var_seq;
end intrinsic;

intrinsic ExtractRoot(Y::Crv, f::FldFunFracSchElt, m::RngIntElt) -> Crv
  {Given a curve Y, and f in KY the function field of Y, return a new curve X with function field KX where KX = KY(mthroot(f)).}
  // assertions
    if not IsAffine(Y) then
      Y := AffinePatch(Y, 1);
    end if;
    assert IsAffine(Y);
    KY := FunctionField(Y);
    assert Parent(f) eq KY;
  // ambient, ideal, polynomial ring of Y
    IY := Ideal(Y);
    PY := Generic(IY);
    AAY := Ambient(Y);
  // polynomial ring and ideal upstairs
    IYext, mp := VariableExtension(IY, 1, false); // mp: PY -> PX
    PX := Codomain(mp);
    assert PX eq Generic(IYext);
    AssignNames(~PX, VarSeq("x", 1, Rank(PX)));
  // map numerator and denominator of f into PX
    numer := mp(Numerator(f, Y));
    denom := mp(Denominator(f, Y));
  // basis of new ideal
    basis := Basis(IYext);
    new_equation := denom*PX.Rank(PX)^m-numer;
    Append(~basis, new_equation);
    IX := ideal< PX | basis >;
    vprintf Solvable : "saturating at...";
    // S := Saturation(IX, numer); // saturate at numerator
    // vprintf Solvable : "numerator...\n";
    S := Saturation(IX, denom); // saturate at numerator
    vprintf Solvable : "denominator...\n";
    assert IsPrime(S);
  // new ambient
    AAX := AffineSpace(PX);
  // make curve
    X := Curve(AAX, S);
    return X;
end intrinsic;

// intrinsic SolvableAssignRamification(s::SolvableDB) -> SolvableDB
//   {assigns [ram0, ram1, ramoo] to s.}
//   t := SolvableDBRead(Child(s) cat ".m");
//   abc_below := Orders(t);
//   abc := Orders(s);
//   // ramification above 0
//     if abc_below[1] eq abc[1] then
//       ram0 := false;
//     else
//       assert abc[1] eq 2*abc_below[1];
//       ram0 := true;
//     end if;
//   // ramification above 1
//     if abc_below[2] eq abc[2] then
//       ram1 := false;
//     else
//       assert abc[2] eq 2*abc_below[2];
//       ram1 := true;
//     end if;
//   // ramification above oo
//     if abc_below[3] eq abc[3] then
//       ramoo := false;
//     else
//       assert abc[3] eq 2*abc_below[3];
//       ramoo := true;
//     end if;
//   // assign to s and return s
//   s`SolvableDBRamification := [ram0, ram1, ramoo];
//   return s;
// end intrinsic;

// intrinsic SolvableAssignResidueFieldsAndDivisors(s::SolvableDB, t::SolvableDB) -> SolvableDB
//   {assigns F0, F1, Foo to s.}
//   child_s := SolvableDBRead(Child(s) cat ".m");
//   assert assigned s`SolvableDBRamification;
//   assert PassportName(t) eq PassportName(child_s);
//   ram0, ram1, ramoo := Explode(Ramification(s));
//   X_below := BelyiCurve(t);
//   phi_below := BelyiMap(t);
//   DivX_below := DivisorGroup(X_below);
//   // ram0
//     if ram0 then
//       D0 := Numerator(Divisor(phi_below));
//       _, F0 := SolvableCheckResidueFields(D0);
//       vprintf Solvable: "D0 divisor:\n";
//       supp0, mult0 := Support(D0);
//       vprintf Solvable: "%o\n%o\n", supp0, mult0;
//       vprintf Solvable: "D0 degree of residue fields: %o\n", Degree(F0);
//       vprintf Solvable: "#supp(D0) before base change = %o.\n", #Support(D0);
//     else
//       vprintf Solvable: "D0 nothing to do.\n";
//       D0 := DivX_below!0;
//       F0 := Rationals();
//     end if;
//   // ram1
//     if ram1 then
//       D1 := Numerator(Divisor(phi_below-1));
//       _, F1 := SolvableCheckResidueFields(D1);
//       vprintf Solvable: "D1 divisor:\n";
//       supp1, mult1 := Support(D1);
//       vprintf Solvable: "%o\n%o\n", supp1, mult1;
//       vprintf Solvable: "D1 degree of residue fields: %o\n", Degree(F1);
//       vprintf Solvable: "#supp(D1) before base change = %o.\n", #Support(D1);
//     else
//       vprintf Solvable: "D1 nothing to do.\n";
//       D1 := DivX_below!0;
//       F1 := Rationals();
//     end if;
//   // ramoo
//     if ramoo then
//       Doo := Denominator(Divisor(phi_below));
//       _, Foo := SolvableCheckResidueFields(Doo);
//       vprintf Solvable: "Doo divisor:\n";
//       suppoo, multoo := Support(Doo);
//       vprintf Solvable: "%o\n%o\n", suppoo, multoo;
//       vprintf Solvable: "Doo degree of residue fields: %o\n", Degree(Foo);
//       vprintf Solvable: "#supp(Doo) before base change = %o.\n", #Support(Doo);
//     else
//       vprintf Solvable: "Doo nothing to do.\n";
//       Doo := DivX_below!0;
//       Foo := Rationals();
//     end if;
//   // assign and return
//     vprintf Solvable: "ResidueFields:\n";
//     vprintf Solvable: "F0 = %o\n", F0;
//     vprintf Solvable: "F1 = %o\n", F1;
//     vprintf Solvable: "Foo = %o\n", Foo;
//     s`SolvableDBResidueField0 := F0;
//     s`SolvableDBResidueField1 := F1;
//     s`SolvableDBResidueFieldoo := Foo;
//     s`SolvableDBDivisor0 := D0;
//     s`SolvableDBDivisor1 := D1;
//     s`SolvableDBDivisoroo := Doo;
//     return s;
// end intrinsic;

intrinsic PullbackBelyiMap(X_below::Crv, f::FldFunFracSchElt, phi_below::FldFunFracSchElt) -> Any
  {}
  vprintf Solvable : "Extracting root to make new curve...";
  t0 := Cputime();
  X<[x]> := ExtractRoot(X_below, f, 2);
  t1 := Cputime();
  vprintf Solvable : "done. %o seconds.\n", t1-t0;
  vprintf Solvable : "Making new Belyi map...";
  assert IsAffine(X);
  KX<[x]> := FunctionField(X);
  if IsAffine(X_below) then
    X_below<[x]> := X_below;
  else
    assert IsProjective(X_below);
    X_below<[x]> := AffinePatch(X_below, 1);
  end if;
  rk_below := Rank(Generic(Ideal(X_below)));
  rk_above := Rank(Generic(Ideal(X)));
  assert rk_above eq rk_below+1;
  // projection map X -> X_below: [x1,x2,x3]->[x1,x2]
  map_text := VarText("X.", 1, rk_below);
  mp := eval Sprintf("return map< X->X_below | [%o] >;", map_text);
  // pullback phi_below under this map
  phi := Pullback(mp, phi_below);
  assert phi_below in FunctionField(X_below);
  assert phi in FunctionField(X);
  vprintf Solvable : "done.\n";
  return X, phi;
end intrinsic;

// intrinsic SolvableBelyiMap(s::SolvableDB, t::SolvableDB : measure_bound := 0) -> SolvableDB
//   {}
//   s := SolvableDBCopy(s);
//   t := SolvableDBCopy(t);
//   if measure_bound ne 0 then
//     assert SolvableMeasure(t) lt measure_bound;
//   end if;
//   t_start := Cputime();
//   if not IsRamifiedAtEveryLevel(s) then
//     error Sprintf("%o is unramified at some level, no method to compute unramified covers (currently).\n", Name(s));
//   end if;
//   // [ram0, ram1, ramoo] a sequence of bools
//     vprintf Solvable: "Determining ramification:\n";
//     abc_below := Orders(t);
//     abc := Orders(s);
//     s := SolvableAssignRamification(s);
//     ram0, ram1, ramoo := Explode(Ramification(s));
//     vprintf Solvable: "Orders below = %o.\n", abc_below;
//     vprintf Solvable: "ramification = %o.\n", [ram0, ram1, ramoo];
//     vprintf Solvable: "Orders above = %o.\n", abc;
//   // assign residue fields F0, F1, Foo, and divisors D0, D1, Doo
//     vprintf Solvable : "Assign residue fields and divisors to s...\n";
//     t0 := Cputime();
//     s := SolvableAssignResidueFieldsAndDivisors(s, t);
//     F0 := s`SolvableDBResidueField0;
//     F1 := s`SolvableDBResidueField1;
//     Foo := s`SolvableDBResidueFieldoo;
//     D0 := s`SolvableDBDivisor0;
//     D1 := s`SolvableDBDivisor1;
//     Doo := s`SolvableDBDivisoroo;
//     t1 := Cputime();
//     vprintf Solvable : "done. %o seconds.\n", t1-t0;
//   // find dimension one Lspaces
//     // try before base change
//       vprintf Solvable: "Try to find dimension one L-spaces before base change:\n";
//       Dinitial := SolvableRamificationToDivisor([ram0, ram1, ramoo], [*D0, D1, Doo*]); // divisor without basechange
//       vprintf Solvable : "Initial ramification divisor computed.\n";
//       vprintf Solvable : "First try without base change.\n";
//       vprintf Solvable : "#supp(Divisor) = %o\n", #Support(Dinitial);
//       vprintf Solvable : "Trying all combinations...";
//       t0 := Cputime();
//       worked_before_basechange, D := SolvableRamificationDivisorUsingAllPoints(Dinitial);
//       s`SolvableDBRamificationDivisorBeforeBaseChange := D;
//       t1 := Cputime();
//       vprintf Solvable : "done. %o seconds.\n", t1-t0;
//     // base change if necessary
//       if worked_before_basechange then
//         vprintf Solvable: "No need to BaseChange.\n";
//       else
//         // make composite of residue fields
//           vprintf Solvable: "Base changing...\n";
//           vprintf Solvable: "Updating curve base field:\n";
//           F := BaseField(BelyiCurve(t));
//           vprintf Solvable: "Degree of current base field = %o\n", Degree(F);
//           newF := Compositum(F, F0);
//           vprintf Solvable: "Degree with F0 = %o.\n", Degree(newF);
//           newF := Compositum(newF, F1);
//           vprintf Solvable: "Degree with F1 = %o.\n", Degree(newF);
//           newF := Compositum(newF, Foo);
//           vprintf Solvable: "Degree with Foo = %o.\n", Degree(newF);
//           t := SolvableBaseChange(t, newF);
//           vprintf Solvable: "OK done. Here is the new field:\n%o\n", newF;
//           vprintf Solvable: "Now updating divisors D0, D1, Doo.\n";
//         // update D0, D1, Doo after base change
//           t0 := Cputime();
//           s := SolvableAssignResidueFieldsAndDivisors(s, t);
//           F0 := s`SolvableDBResidueField0;
//           F1 := s`SolvableDBResidueField1;
//           Foo := s`SolvableDBResidueFieldoo;
//           D0 := s`SolvableDBDivisor0;
//           D1 := s`SolvableDBDivisor1;
//           Doo := s`SolvableDBDivisoroo;
//           t1 := Cputime();
//         // make ramification divisor after BaseChange
//           vprintf Solvable: "Try to find dimension one L-spaces after base change:\n";
//           Dinitial := SolvableRamificationToDivisor([ram0, ram1, ramoo], [*D0, D1, Doo*]);
//           vprintf Solvable : "Initial divisor computed.\n";
//           vprintf Solvable : "#supp(Divisor) = %o\n", #Support(Dinitial);
//           vprintf Solvable : "Trying all combinations...";
//           t0 := Cputime();
//           worked_after_basechange, D := SolvableRamificationDivisorUsingAllPoints(Dinitial);
//           s`SolvableDBRamificationDivisorAfterBaseChange := D;
//           t1 := Cputime();
//           vprintf Solvable : "done. %o seconds.\n", t1-t0;
//           assert worked_after_basechange;
//       end if;
//   // setup curve downstairs
//     X_below := BelyiCurve(t);
//     phi_below := BelyiMap(t);
//   // RiemannRoch
//     vprintf Solvable: "Applying RiemannRoch to following divisor:\n";
//     supp, mult := Support(D);
//     vprintf Solvable: "%o\n%o\n", supp, mult;
//     LD, mpLDtoKX := RiemannRochSpace(D);
//     assert Dimension(LD) eq 1;
//     f := mpLDtoKX(LD.1);
//     denom := Denominator(f, X_below);
//     numer := Numerator(f, X_below);
//     assert Parent(denom) eq Parent(numer);
//     vprintf Solvable: "Parent(f) =\n%o\n", Parent(f);
//     vprintf Solvable: "f = \n%o\n", f;
//     vprintf Solvable: "Numerator(f) = %o.\n", numer;
//     vprintf Solvable: "Denominator(f) = %o.\n", denom;
//     f_measure := SolvableMeasure(f);
//     vprintf Solvable: "Measure of f = %o.\n", f_measure;
//     if measure_bound ne 0 then
//       assert f_measure lt measure_bound div 2;
//     end if;
//   // make the curve (brutal) using primary decomposition or (less brutal) use saturation
//     X, phi := PullbackBelyiMap(X_below, f, phi_below);
//     // if Degree(BaseField(X)) gt 1 then
//       // assert IsCyclotomic(BaseField(X));
//     // end if;
//   // assertions
//     vprintf Solvable : "Checking genus of curve...";
//     t0_genus := Cputime();
//     assert IsGenusComputable(X);
//     assert Genus(s) eq Genus(X);
//     t1_genus := Cputime();
//     vprintf Solvable : "done. %o seconds\n", t1_genus - t0_genus;
//   // assign information to s and return s
//     s`SolvableDBBelyiCurve := X;
//     s`SolvableDBBelyiMap := phi;
//   // timing
//     t_end := Cputime();
//     s`SolvableDBBelyiMapTiming := t_end - t_start;
//   // return
//     return s;
// end intrinsic;

// intrinsic SolvableBelyiMap(s::SolvableDB : best_child := false) -> SolvableDB
//   {overloaded using child of s.}
//   t := ChildObject(s);
//   if best_child then
//     pass := SolvableDBToPassportDB(t);
//     objs := PassportObjects(pass);
//     if PointedPassportSize(t) gt 1 and #objs gt 1 then
//       error "Careful about which map chosen below: \n", Filename(s);
//     end if;
//     below := t;
//     better_base_fields := [];
//     for obj in objs do
//       if BelyiMapIsComputed(obj) then
//         is_base_field_better := Degree(BaseField(BelyiCurve(obj))) lt Degree(BaseField(BelyiCurve(below)));
//         if is_base_field_better then
//           Append(~better_base_fields, obj);
//         end if;
//       end if;
//     end for;
//     for obj in better_base_fields do
//       is_measure_better := SolvableMeasure(obj) lt SolvableMeasure(below);
//       if is_measure_better then
//         below := obj;
//       end if;
//     end for;
//     return SolvableBelyiMap(s, below);
//   else
//     return SolvableBelyiMap(s, t);
//   end if;
// end intrinsic;

// intrinsic SolvableBelyiMapLowMeasure(s::SolvableDB, m::RngIntElt) -> Any
//   {Compute solvable Belyi map m times, return the one with smallest SolvableMeasure. Careful with reassigning objects...}
//   // make initial object
//   current := SolvableDBCopy(s);
//   // m iterations
//   measure_list := [];
//   errors := [];
//   for i := 1 to m do
//     if BelyiMapIsComputed(current) then
//       try
//         // make test object
//         test := SolvableDBCopy(s);
//         test := SolvableBelyiMap(test);
//         test_measure := SolvableMeasure(test);
//         Append(~measure_list, test_measure);
//         vprintf Solvable : "measures so far = %o\n", measure_list;
//         // compare with current object
//         current_measure := SolvableMeasure(current);
//         if test_measure lt current_measure then
//           current := SolvableDBCopy(test);
//         end if;
//       catch e1
//         Append(~errors, e1);
//       end try;
//     else
//       assert #measure_list eq 0;
//       try
//         current := SolvableBelyiMap(current);
//         current_measure := SolvableMeasure(current);
//         Append(~measure_list, current_measure);
//       catch e2
//         Append(~errors, e2);
//       end try;
//     end if;
//   end for;
//   if #measure_list eq 0 then
//     return errors,errors;
//   else
//     vprintf Solvable : "Computed %o SolvableBelyiMaps for %o.\n", m, s`SolvableDBName;
//     vprintf Solvable : "List of measures:\n";
//     vprintf Solvable : "%o\n", measure_list;
//     vprintf Solvable : "Minimum = %o\n", Min(measure_list);
//     assert SolvableMeasure(current) le Min(measure_list);
//     return current, errors;
//   end if;
// end intrinsic;

// intrinsic SolvableBelyiMapWrapper(s::SolvableDB) -> Any
//   {}
//   s := SolvableBelyiMap(s);
//   SolvableLocalSanityCheck(s, 101);
//   SolvableDBWrite(s);
//   return "ola";
// end intrinsic;

/*
intrinsic SolvableProjectToPP3(s::SolvableDBObject) -> Any
  {Try to embed Belyi curve in PP3 (or PP2) and update SolvableDBObject. Return before and after versions.}
  vprintf Solvable : "%o Project to PP3 or PP2:\n", s`SolvableDBName;
  curve_assigned := assigned s`SolvableDBBelyiCurve;
  map_assigned := assigned s`SolvableDBBelyiMap;
  if curve_assigned and map_assigned then
    t_start := Cputime();
    // make before and after objects
      before := SolvableCopy(s);
      after := SolvableCopy(s);
    // setup for various cases
      vprintf Solvable : "  Belyi curve and map assigned.\n";
      X := before`SolvableDBBelyiCurve;
      assert IsAffine(X);
      X_proj := ProjectiveClosure(X);
      f := before`SolvableDBBelyiMap;
      degree_start := Degree(X_proj);
      vprintf Solvable : "  Degree of Belyi curve = %o.\n", degree_start;
      vprintf Solvable : "  Checking Canonical map...";
      t0 := Cputime();
      g, is_low_genus_or_hyp, mp := GenusAndCanonicalMap(X); // better to take projective closure?
      s`SolvableDBIsLowGenusOrHyperelliptic := is_low_genus_or_hyp;
      before`SolvableDBIsLowGenusOrHyperelliptic := is_low_genus_or_hyp;
      after`SolvableDBIsLowGenusOrHyperelliptic := is_low_genus_or_hyp;
      t1 := Cputime();
      vprintf Solvable : "done. %o seconds.\n", t1-t0;
    // cases
      if IsHyperelliptic(X) then
        assert is_low_genus_or_hyp;
        // computing hyperelliptic model
          vprintf Solvable : "  Curve is hyperelliptic.\n";
          vprintf Solvable : "  Computing hyperelliptic model...";
          t0 := Cputime();
          hyp_bool, hyp_H, hyp_mp := IsHyperelliptic(X);
          t1 := Cputime();
          vprintf Solvable : "done. %o seconds.\n", t1-t0;
          vprintf Solvable : "  Degree of new Belyi curve = %o.\n", Degree(hyp_H);
        // make new Belyi map, curve, and base field, assign to after object
          vprintf Solvable : "  Pushing forward Belyi map under iso...";
          g := Pushforward(hyp_mp, f);
          vprintf Solvable : "done.\n";
          X<x1, x2, x3> := hyp_H;
          KX<x1, x2> := FunctionField(X);
          assert KX eq Parent(g);
          K := BaseField(X);
          if Type(K) eq FldNum then
            K<nu> := BaseField(X);
          end if;
          after`SolvableDBBelyiCurve := X;
          after`SolvableDBBelyiMap := g; // not necessarily KX.1
        // timing and return
          t_end := Cputime();
          after`SolvableDBLowDegreeTiming := t_end - t_start;
          return before, after;
      else // g > 1 and curve is not hyperelliptic
        // computing new model
          vprintf Solvable : "  Curve is not hyperelliptic.\n";
          t0 := Cputime();
          printf "  Projecting to PP3...";
          C, mp := EmbedPlaneCurveInP3(X); // the scheme is the codomain of mp
          assert IsProjective(Ambient(C));
          assert Curve(C) eq C;
          C := Curve(C);
          fix := map< X_proj -> C | DefiningEquations(mp) >;
          g := Pushforward(fix, f);
          t1 := Cputime();
          vprintf Solvable : "done. %o seconds.\n", t1-t0;
          C := AffinePatch(C, 1); // TODO not pick blindly?
          I := Ideal(C);
          P := Generic(I);
          num_vars := Rank(P);
          Ceval := C;
          C := eval Sprintf("C<%o> := Ceval; return C;", VarText("x", 1, num_vars));
          KC := eval Sprintf("KC<%o> := FunctionField(C); return KC;", VarText("x", 1, num_vars-1));
          assert Parent(g) eq KC;
          K := BaseField(C);
          if ISA(Type(K), FldNum) then
            K<nu> := BaseField(C);
          end if;
          after`SolvableDBBelyiCurve := C;
          after`SolvableDBBelyiMap := g;
          assert Parent(g) eq KC;
          if not g eq KC.1 then
            vprintf Solvable : "  WARNING! new Belyi map is no longer KX.1\n";
          end if;
          Cproj := ProjectiveClosure(C);
          vprintf Solvable : "  Degree of new model = %o.\n", Degree(Cproj);
          // vprintf Solvable : "  Degree of new model = %o.\n", Degree(C);
        // bookkeeping and return
          assert Parent(g) eq FunctionField(C);
          t_end := Cputime();
          after`SolvableDBLowDegreeTiming := t_end - t_start;
          return before, after;
      end if;
  else
    vprintf Solvable : "Belyi map (or curve) is not assigned.\n";
    return s;
  end if;
end intrinsic;
*/

/*
intrinsic SolvableIsHyperelliptic(s::SolvableDBObject) -> Any
  {Determine if Belyi curve has a hyperelliptic model and if so, returns updated object.}
  vprintf Solvable : "%o IsHyperelliptic?\n", s`SolvableDBName;
  curve_assigned := assigned s`SolvableDBBelyiCurve;
  map_assigned := assigned s`SolvableDBBelyiMap;
  g := s`SolvableDBGenus;
  // cases to disregard
  if g in [0,1] then
    vprintf Solvable : "  Genus 0 or 1. Do nothing.\n";
    return false, s;
  end if;
  // if assigned s`SolvableDBIsLowGenusOrHyperelliptic and s`SolvableDBIsLowGenusOrHyperelliptic then
    // vprintf Solvable : "  Already hyperelliptic. Do nothing.\n";
    // return true, s;
  // end if;
  if curve_assigned and map_assigned then
    // make before and after objects
    before := SolvableCopy(s);
    after := SolvableCopy(s);
    // setup for various cases
    vprintf Solvable : "  Belyi curve and map assigned.\n";
    X := before`SolvableDBBelyiCurve;
    assert IsAffine(X);
    X_proj := ProjectiveClosure(X);
    f := before`SolvableDBBelyiMap;
    degree_start := Degree(X_proj);
    vprintf Solvable : "  Degree of Belyi curve = %o.\n", degree_start;
    vprintf Solvable : "  Checking Canonical map...";
    t0 := Cputime();
    g, is_low_genus_or_hyp, mp := GenusAndCanonicalMap(X); // better to take projective closure?
    s`SolvableDBIsLowGenusOrHyperelliptic := is_low_genus_or_hyp;
    before`SolvableDBIsLowGenusOrHyperelliptic := is_low_genus_or_hyp;
    after`SolvableDBIsLowGenusOrHyperelliptic := is_low_genus_or_hyp;
    t1 := Cputime();
    vprintf Solvable : "done. %o seconds.\n", t1-t0;
    // cases
    if is_low_genus_or_hyp then
      // computing hyperelliptic model
      vprintf Solvable : "  Curve is hyperelliptic.\n";
      vprintf Solvable : "  Computing hyperelliptic model...";
      t0 := Cputime();
      hyp_bool, hyp_H, hyp_mp := IsHyperelliptic(X);
      t1 := Cputime();
      vprintf Solvable : "done. %o seconds.\n", t1-t0;
      vprintf Solvable : "  Degree of new Belyi curve = %o.\n", Degree(hyp_H);
      // make new Belyi map, curve, and base field, assign to after object
      vprintf Solvable : "  Pushing forward Belyi map under iso...";
      g := Pushforward(hyp_mp, f);
      vprintf Solvable : "done.\n";
      X<x1, x2, x3> := hyp_H;
      KX<x1, x2> := FunctionField(X);
      assert KX eq Parent(g);
      K := BaseField(X);
      if Type(K) eq FldNum then
        K<nu> := BaseField(X);
      end if;
      after`SolvableDBBelyiCurve := X;
      after`SolvableDBBelyiMap := g; // not necessarily KX.1
      // timing and return
      return true, after;
    else
      vprintf Solvable : "  Curve is not hyperelliptic. Do nothing.\n";
      return false, s;
    end if;
  else
    vprintf Solvable : "Belyi map (or curve) is not assigned.\n";
    return false, s;
  end if;
end intrinsic;
*/

/*
intrinsic SolvableWrapper(s::SolvableDBObject, n::RngIntElt : only_local := false) -> SolvableDBObject
  {for internal use only}
  s := SolvableBelyiMapLowMeasure(s, n); // TODO change this for whatever d
  assert Type(s) eq SolvableDBObject;
  if s`SolvableDBGenus in [0,1] then // low genus
    before, after := SolvableProjectToPP3(s);
    if SolvableMeasure(after) lt SolvableMeasure(before) then
      s := after;
    end if;
  else // hyperelliptic
    is_hyp, hyp := SolvableIsHyperelliptic(s);
    if is_hyp then
      s := hyp;
    end if;
  end if;
  if only_local then
    // SolvableLocalSanityCheck(s,101);
    SolvableLocalSanityCheck(s,8736028057);
  else
    // SolvableLocalSanityCheck(s,101);
    SolvableLocalSanityCheck(s,8736028057);
    SolvableMapSanityCheck(s);
  end if;
  // SolvableDBWriteObject(s);
  // filename := s`SolvableDBFilename;
  // t := SolvableDBAccessEntry(filename);
  // assert SolvableLocalSanityCheck(t, 101);
  return s;
end intrinsic;
*/

/*
intrinsic SolvableWrapper(d::RngIntElt, n::RngIntElt) -> MonStgElt
  {for internal use only}
  assert d eq 32;
  a,b,c := SolvableDBStatus(d);
  for i := 8 to #b do // TODO start after "bad" ones
    s := SolvableBelyiMapLowMeasure(b[i], n); // TODO change this for whatever d
    if Type(s) eq SeqEnum then
      error "SolvableBelyiMapLowMeasure failed";
    end if;
    if s`SolvableDBGenus in [0,1] then // low genus
      before, after := SolvableProjectToPP3(s);
      if SolvableMeasure(after) lt SolvableMeasure(before) then
        s := after;
      end if;
    else // hyperelliptic
      is_hyp, hyp := SolvableIsHyperelliptic(s);
      if is_hyp then
        s := hyp;
      end if;
    end if;
    SolvableMapSanityCheck(s);
    // SolvableLocalSanityCheck(s,101);
    SolvableLocalSanityCheck(s,8736028057);
    SolvableDBWriteObject(s);
    filename := s`SolvableDBFilename;
    t := SolvableDBAccessEntry(filename);
    // assert SolvableLocalSanityCheck(t, 101);
    assert SolvableLocalSanityCheck(s,8736028057);
  end for;
  return Sprintf("Solvable wrapper completed for degree %o\n", d);
end intrinsic;
*/