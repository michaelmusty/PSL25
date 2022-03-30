intrinsic PermutationToCode(perm::GrpPermElt) -> SeqEnum[SeqEnum[RngIntElt]]
  {list encoding cycles of perm.}
  d := Degree(Parent(perm));
  fact := Factorization(d);
  //assert IsDivisibleBy(d, 2) and #fact eq 1; //hack
  cycles := CycleDecomposition(perm);
  code := [];
  for i in [1..#cycles] do
    cycle_code := [];
    for j in [1..#cycles[i]] do
      Append(~cycle_code, cycles[i][j]);
    end for;
    Append(~code, cycle_code);
  end for;
  return code;
end intrinsic;

intrinsic CodeToBlocks(code::SeqEnum) -> SetIndx
  {indexed set of blocks corresponding to code.}
  blocks := {@ @};
  for i := 1 to #code do
    block := {};
    for j := 1 to #code[i] do
      block join:= {code[i][j]};
    end for;
    blocks join:= {@ block @};
  end for;
  return blocks;
end intrinsic;

intrinsic PermutationToBlocks(perm::GrpPermElt) -> SetIndx
  {blocks corresponding to permutation.}
  return CodeToBlocks(PermutationToCode(perm));
end intrinsic;

intrinsic SolvableCycleStructure(triple::SeqEnum[GrpPermElt]) -> SeqEnum
  {returns sequence of 3 cycle structures for triple.}
  assert #triple eq 3;
  return [ CycleStructure(triple[i]) : i in [1..3] ];
end intrinsic;

intrinsic Extensions(sigma::SeqEnum[GrpPermElt]) -> Any
  {Let A be the trivial G-module for sigma. Computes H^2(G, A) and returns list of extensions 1->A->E->G->1.}
  // setup
  G := Parent(sigma[1]);
  d := Degree(G);
  G := sub<Sym(d)|sigma>;
  assert IsTransitive(G);
  //assert #G eq d; // Galois //hack
  l := Floor(Log(2,Degree(G)));
  //assert 2^l eq d; //hack
  // G-module
  triv := Matrix(GF(2), [[1]]);
  // FIXME?
  // trivs := [ triv : i in [1..#Generators(G)] ];
  trivs := [ triv : i in [1..3] ];
  A := GModule(G, trivs);
  // H^2
  CM := CohomologyModule(G, A);
  H2 := CohomologyGroup(CM, 2);
  // assert #DistinctExtensions(CM) eq #H2; // #H2 greater in general
  extensions := [* *];
  distinct_extensions := [];
  for h in H2 do
    E_fp, pi_fp, iota_fp := Extension(CM, h);
    // Append(~distinct_extensions, E_fp);
    // ct := CosetTable(E_fp, sub<E_fp|Id(E_fp)>);
    // iso, E := CosetTableToRepresentation(E_fp, ct);
    iso, E, K := CosetAction(E_fp, sub<E_fp|Id(E_fp)>);
    iotaE := iota_fp*iso;
    piE := (iso^-1)*pi_fp;
    assert Image(iotaE) eq Kernel(piE);
    assert Image(iotaE).1 in Center(E);
    block := PermutationToBlocks(Image(iotaE).1);
    Append(~extensions, [* E, iotaE, piE , block *]);
  end for;
  return extensions;
end intrinsic;

intrinsic EliminateRedundancies(pass::SeqEnum[SeqEnum[GrpPermElt]]) -> SeqEnum[SeqEnum[GrpPermElt]]
  {eliminate simultaneuous conjugation}
  S := Generic(Parent(pass[1][1]));
  for i := #pass to 1 by -1 do
    for j := 1 to i-1 do
      if IsConjugate(S, pass[i], pass[j]) then
        Remove(~pass, i);
        break j;
      end if;
    end for;
  end for;
  return pass;
end intrinsic;

intrinsic Lifts(extension::List, below::SeqEnum[GrpPermElt]) -> Any
  {the permutation triple below has 2^3 lifts by the extension, return the 4 that multiply to 1 in the extension.}
  // setup
    assert #below eq 3;
    G := Parent(below[1]);
    S := Generic(G);
    G := sub<S|below>;
    assert IsTransitive(G);
    assert below[3]*below[2]*below[1] eq Id(G);
    d := Degree(G);
    //assert #G eq d; // Galois //hack
    l := Floor(Log(2,Degree(G)));
    //assert 2^l eq d; //hack
    E, iotaE, piE, blocks_test := Explode(extension);
    assert IsTransitive(E); // TODO we don't need this?
    tau := Image(iotaE).1;
    blocks := PermutationToBlocks(tau);
    assert blocks eq blocks_test; // TODO kind of silly
    H := sub<E|tau>;
  // lift below via the extension
    assert tau in Center(E); // TODO investigate
    above := [ (below[i] @@ piE) : i in [1..3] ];
    a1, a2, a3 := Explode(above);
    assert a1 in E and a2 in E and a3 in E and tau*a1 in E;
    assert IsIsomorphic(E/H, G);
    assert not IsConjugate(Sym(2*d), [a1, a2, a3], [tau*a1, a2, a3]);
    // a1 := E!a1; a2 := E!a2; a3 := E!a3; tau := E!tau;
    a1 := Sym(2*d)!a1; a2 := Sym(2*d)!a2; a3 := Sym(2*d)!a3; tau := Sym(2*d)!tau;
  // make the lifts : 8 lifts, 4 multiply to 1, 4 multiply to tau
    lifts := [];
    if a3*a2*a1 eq Id(Sym(2*d)) then
      Append(~lifts, [a1, a2, a3]);
      Append(~lifts, [a1, tau*a2, tau*a3]);
      Append(~lifts, [tau*a1, a2, tau*a3]);
      Append(~lifts, [tau*a1, tau*a2, a3]);
    else
      assert tau*a3*a2*a1 eq Id(Sym(2*d));
      Append(~lifts, [tau*a1, a2, a3]);
      Append(~lifts, [a1, tau*a2, a3]);
      Append(~lifts, [a1, a2, tau*a3]);
      Append(~lifts, [tau*a1, tau*a2, tau*a3]);
    end if;
  // return
    return lifts;
end intrinsic;

intrinsic ExtensionToTriples(extension::List, below::SeqEnum[GrpPermElt]) -> Any
  {Lift the triple below of G to a triple of E via the extension 1->A->E->G->1.}
  // setup
    assert #below eq 3;
    G := Parent(below[1]);
    S := Generic(G);
    G := sub<S|below>;
    assert IsTransitive(G);
    assert below[3]*below[2]*below[1] eq Id(G);
    d := Degree(G);
    //assert #G eq d; // Galois //hack
    l := Floor(Log(2,Degree(G)));
    //assert 2^l eq d; //hack
    E, iotaE, piE, blocks_test := Explode(extension);
    assert IsTransitive(E); // TODO we don't need this?
    tau := Image(iotaE).1;
    blocks := PermutationToBlocks(tau);
    assert blocks eq blocks_test; // TODO kind of silly
    H := sub<E|tau>;
  // lift below and make the lifts : 8 lifts, 4 multiply to 1, 4 multiply to tau
    lifts := Lifts(extension, below);
    for i := #lifts to 1 by -1 do
      lift := lifts[i];
      if not IsIsomorphic(E, sub<Sym(2*d)|lift>) then
        Remove(~lifts, i);
      end if;
    end for;
    if #lifts eq 0 then
      return [],_;
    end if;
  // sort by cycle structure
    assert #lifts gt 0;
    cycle_structures := [SolvableCycleStructure(lifts[i]) : i in [1..#lifts]];
    unique_cycle_structures := SetToSequence(SequenceToSet(cycle_structures));
    assert #unique_cycle_structures in [1, 2];
    if #unique_cycle_structures eq 1 then
      // check for size greater than 1 passport
      cover := [lifts[1]];
      for lift in lifts do
        if not IsConjugate(Sym(2*d), cover[1], lift) then // not simultaneously conjugate
          Append(~cover, lift);
        end if;
      end for;
      // return
      cover := EliminateRedundancies(cover);
      return [cover], blocks;
    else // 2 unique cycle structures
      cover1 := [];
      cover2 := [];
      for lift in lifts do
        if SolvableCycleStructure(lift) eq unique_cycle_structures[1] then
          Append(~cover1, lift);
        else
          if SolvableCycleStructure(lift) eq unique_cycle_structures[2] then
            Append(~cover2, lift);
          else
            error "ERROR!";
          end if;
        end if;
      end for;
      cover1 := EliminateRedundancies(cover1);
      cover2 := EliminateRedundancies(cover2);
      return [cover1, cover2], blocks;
    end if;
end intrinsic;

intrinsic RamificationType(above::SeqEnum[GrpPermElt], below::SeqEnum[GrpPermElt]) -> MonStgElt
  {returns a string "unramified", "ramified", or "impossible" according to the orders.}
  a, b, c := Explode([Order(below[i]) : i in [1..3]]);
  A, B, C := Explode([Order(above[i]) : i in [1..3]]);
  if (A ge a) and (B ge b) and (C ge c) then
    if (A eq a) and (B eq b) and (C eq c) then
      return "unramified";
    else
      return "ramified";
    end if;
  else
    return "impossible";
  end if;
end intrinsic;

intrinsic Coverings(below::SeqEnum[GrpPermElt]) -> Any
  {returns a 3 lists [* [*ramified_orbit1,blocks1*], [*ramified_orbit2,blocks2*],..., *] , [* same but unramified *], [* same but impossible *]}
  // setup
    assert #below eq 3;
    G := Parent(below[1]);
    S := Generic(G);
    G := sub<S|below>;
    assert IsTransitive(G);
    assert below[3]*below[2]*below[1] eq Id(G);
    d := Degree(G);
    //assert #G eq d; // Galois // hack
    l := Floor(Log(2,Degree(G)));
    //assert 2^l eq d; // hack
  // extensions
    //vprintf Solvable : "Computing extensions...";
    t0 := Cputime();
    extensions := Extensions(below);
    t1 := Cputime();
    //vprintf Solvable : "done: %o seconds.\n", t1-t0;
  // initial lists for return
    ramified := [* *];
    unramified := [* *];
    impossible := [* *];
  // loop over extensions
    for i := 1 to #extensions do
      extension := extensions[i];
      t0 := Cputime();
      passports, blocks := ExtensionToTriples(extension, below); // [ [triple,triple],[triple,triple] ]
      assert #passports in [0, 1, 2];
      for passport in passports do
        ram_types := [];
        for above in passport do
          Append(~ram_types, RamificationType(above, below));
        end for;
        assert #SequenceToSet(ram_types) eq 1;
        ram_type := ram_types[1];
        if ram_type eq "ramified" then
          Append(~ramified, [* passport, blocks *]);
        end if;
        if ram_type eq "unramified" then
          Append(~unramified, [* passport, blocks *]);
        end if;
        if ram_type eq "impossible" then
          Append(~impossible, [* passport, blocks *]);
        end if;
      end for;
      t1 := Cputime();
      //vprintf Solvable : "extension %o out of %o took %o seconds.\n", i, #extensions, t1-t0;
    end for;
  // return
    return ramified, unramified, impossible;
end intrinsic;

intrinsic SolvableDBGenerateName(sigma::SeqEnum[GrpPermElt]) -> MonStgElt
  {Generate a unique string identifying the passport corresponding to sigma.}
  assert #sigma eq 3;
  H := Parent(sigma[1]);
  d := Degree(H);
  G := sub<Sym(d)|sigma>;
  assert IsTransitive(G);
  a,b,c := Explode([Order(sigma[1]), Order(sigma[2]), Order(sigma[3])]);
  if d gt 16 then
    d, g := Explode(IdentifyGroup(G)); // small group identification
    name := Sprintf("%oS%o-%o,%o,%o", d, g, a, b, c);
  else
    g, d := TransitiveGroupIdentification(G);
    name := Sprintf("%oT%o-%o,%o,%o", d, g, a, b, c);
  end if;
  c0 := #CycleDecomposition(sigma[1]);
  c1 := #CycleDecomposition(sigma[2]);
  coo := #CycleDecomposition(sigma[3]);
  genus := (d+2-c0-c1-coo)/2;
  name *:= Sprintf("-g%o", genus);
  return name;
end intrinsic;

intrinsic SolvableDBUnsolvableName(s::SolvableDB) -> MonStgElt
  {given an obj s, return "passport name" instead of "solvable name" ugh.}
  return SolvableDBGenerateName(s`SolvableDBGaloisOrbit[1]);
end intrinsic;

//intrinsic SolvableDBExample(galois_orbit::SeqEnum[SeqEnum[GrpPermElt]], blocks::SetIndx, path_number::RngIntElt) -> SolvableDB
//  {Creates a SolvableDB object corresponding to galois_orbit, blocks, and pathnumber. This assumes the current directory is SolvableDessins.}
//  // some sanity checks
//    for i in [1..#galois_orbit] do
//      sigma := galois_orbit[i];
//      assert #sigma eq 3;
//      assert Type(Parent(sigma[1])) eq GrpPerm;
//      d := Degree(Parent(sigma[1]));
//      G := sub< Sym(d) | sigma >;
//      assert IsTransitive(G);
//    end for;
//    check_pass := PassportRepresentatives(sigma);
//    check_pointed_pass := PassportRepresentatives(sigma : Pointed := true);
//  // stuff we need later
//    sigma := galois_orbit[1];
//    d := Degree(Parent(sigma[1]));
//    G := sub< Sym(d) | sigma >;
//  // directory stuff
//    dir := GetCurrentDirectory();
//    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
//    if parentdir ne "SolvableDessins\n" then
//      error "make sure your working directory is /SolvableDessins";
//    end if;
//    db := dir cat "/SolvableDB";
//    directory := Sprintf("%o/%o/", db, d);
//  // create one SolvableDB object per galois_orbit
//    s := SolvableDBInitialize();
//  // generate name
//    newname := SolvableDBGenerateName(sigma);
//  // SolvableDBName
//    s`SolvableDBName := Sprintf("%o-path%o", newname, path_number); // path number is passed
//  // SolvableDBBlocks
//    s`SolvableDBBlocks := blocks; // blocks are passed
//  // SolvableDBFilename
//    s`SolvableDBFilename := s`SolvableDBName cat ".m";
//  // SolvableDBPassportName
//    s`SolvableDBPassportName := newname;
//  // SolvableDBPathNumber
//    s`SolvableDBPathNumber := path_number;
//  // SolvableDBDegree
//    s`SolvableDBDegree := d;
//  // SolvableDBOrders
//    s`SolvableDBOrders := [Order(sigma[i]) : i in {1..3}];
//  // SolvableDBType
//    a,b,c := Explode(s`SolvableDBOrders);
//    if 1/a+1/b+1/c gt 1 then
//      s`SolvableDBType := "Spherical";
//    elif 1/a+1/b+1/c eq 1 then
//      s`SolvableDBType := "Euclidean";
//    else
//      s`SolvableDBType := "Hyperbolic";
//    end if;
//  // SolvableDBGenus
//    c0 := #CycleDecomposition(sigma[1]);
//    c1 := #CycleDecomposition(sigma[2]);
//    coo := #CycleDecomposition(sigma[3]);
//    genus := (d+2-c0-c1-coo)/2;
//    s`SolvableDBGenus := genus;
//  // SolvableDBGaloisOrbitSize
//    s`SolvableDBGaloisOrbitSize := #galois_orbit;
//  // SolvableDBPassportSize
//    s`SolvableDBPassportSize := #check_pass;
//  // SolvableDBPointedPassportSize
//    s`SolvableDBPointedPassportSize := #check_pointed_pass;
//  // SolvableDBLevel
//    floor := Floor(Log(d)/Log(2));
//    ceil := Ceiling(Log(d)/Log(2));
//    assert floor eq ceil;
//    s`SolvableDBLevel := floor;
//  // SolvableDBGaloisOrbit
//    s`SolvableDBGaloisOrbit := galois_orbit;
//  // SolvableDBPassport
//    s`SolvableDBPassport := check_pass;
//  // SolvableDBPointedPassport
//    s`SolvableDBPointedPassport := check_pointed_pass;
//  // SolvableDBMonodromyGroup
//    s`SolvableDBMonodromyGroup := G;
//  // SolvableDBAutomorphismGroup and SolvableDBDessinCode
//    if s`SolvableDBType eq "Hyperbolic" then
//      s`SolvableDBAutomorphismGroup := AutomorphismGroup(sigma);
//      s`SolvableDBPointedAutomorphismGroup := PointedAutomorphismGroup(sigma);
//    end if;
//  // (DO NOT) write the object to file
//  /*
//    ChangeDirectory(dbdirectory);
//    SolvableDBWriteObject(s);
//    returnText := Sprintf("SolvableDBObject file for %o written in directory %o\n", s`SolvableDBName, directory, d);
//    ChangeDirectory(dbdirectory);
//    return returnText;
//  */
//  return s;
//end intrinsic;
//
//intrinsic SolvableIsRamifiedAtEveryLevel(s::SolvableDB) -> BoolElt
//  {true if s is ramified (at at least one point) at every intermediate level.}
//  if s`SolvableDBDegree eq 2 then
//    s`SolvableDBIsRamifiedAtEveryLevel := true;
//    return true;
//  else
//    path := s`SolvableDBPathToPP1; // PP1, degree 2, degree 4, etc
//    path_filenames := [];
//    for i := #path to 2 by -1 do
//      Append(~path_filenames, path[i] cat ".m");
//    end for;
//    unramified_bool := false;
//    for i := 1 to #path_filenames-1 do
//      if i eq 1 then // for top level use passes SolvableDB object since it might not have a file yet.
//        top := s;
//      else
//        top := SolvableDBRead(path_filenames[i]);
//      end if;
//      bottom := SolvableDBRead(path_filenames[i+1]);
//      topABC := top`SolvableDBOrders;
//      bottomABC := bottom`SolvableDBOrders;
//      if topABC eq bottomABC then
//        unramified_bool := true;
//      end if;
//    end for;
//    if unramified_bool then
//      s`SolvableDBIsRamifiedAtEveryLevel := false;
//      return false;
//    else
//      s`SolvableDBIsRamifiedAtEveryLevel := true;
//      return true;
//    end if;
//  end if;
//end intrinsic;
//
//intrinsic GaloisOrbitsAtLevel(d::RngIntElt) -> Any
//  {All at once to save on database merging. returns lists below,above that then need to be written.}
//  if IsEven(d) and #Factorization(d) eq 1 then
//    d_below := d div 2;
//    filenames_below_old := SolvableDBFilenames(d_below);
//    filenames_below := SolvablePassportDBFilenamesFromObjects(d_below);
//    assert Seqset(filenames_below_old) eq Seqset(filenames_below);
//    if #filenames_below eq 0 then
//      error "we have not computed far enough to compute to this degree yet!";
//    else
//      need_to_write_below := [];
//      need_to_write_above := [];
//      for i := 1 to #filenames_below do // i loops over SolvableDBObjects below
//        t0_i := Cputime();
//        name := filenames_below[i];
//        vprintf Solvable : "Starting...\n";
//        vprintf Solvable : "Degree %o above %o: ", d, name;
//        vprintf Solvable : "%o out of %o\n\n", i, #filenames_below;
//        s_below := SolvableDBRead(name);
//        // assert not assigned s_below`SolvableDBParents;
//        s_below`SolvableDBParents := [];
//        orbit_below := s_below`SolvableDBGaloisOrbit;
//        vprintf Solvable : "Galois orbit size = %o\n", #orbit_below;
//        t0 := Cputime();
//        all_ramified := [* *];
//        all_unramified := [* *];
//        all_impossible := [* *];
//        for j := 1 to #orbit_below do
//          ramified, unramified, impossible := Coverings(orbit_below[j]);
//          all_ramified cat:= ramified;
//          all_unramified cat:= unramified;
//          all_impossible cat:= impossible;
//        end for;
//        t1 := Cputime();
//        vprintf Solvable : "Coverings of %o:", s_below`SolvableDBName;
//        vprintf Solvable : " %o seconds\n", t1-t0;
//        vprintf Solvable : "#ramified = %o\n", #ramified;
//        vprintf Solvable : "#unramified = %o\n", #unramified;
//        all := all_ramified cat all_unramified;
//        vprintf Solvable : "#total = %o\n", #all;
//        aboves := [];
//        for j := 1 to #all do
//          t0 := Cputime();
//          pass := all[j][1];
//          blocks := all[j][2];
//          // determine path number
//          new_name := SolvableDBGenerateName(pass[1]);
//          existing_path_numbers := [];
//          for k := 1 to #need_to_write_above do
//            test := need_to_write_above[k];
//            test_name := PassportName(test);
//            if test_name eq new_name then
//              Append(~existing_path_numbers, test`SolvableDBPathNumber);
//            end if;
//          end for;
//          for a in aboves do
//            a_name := PassportName(a);
//            if a_name eq new_name then
//              Append(~existing_path_numbers, a`SolvableDBPathNumber);
//            end if;
//          end for;
//          assert (#existing_path_numbers eq 0) or (Max(existing_path_numbers) eq #existing_path_numbers);
//          path_number := #existing_path_numbers+1;
//          // make new db object
//          above := SolvableDBExample(pass, blocks, path_number);
//          // update above`SolvableDBChild
//          above`SolvableDBChild := s_below`SolvableDBName;
//          // update above`SolvableDBPathToPP1
//          above`SolvableDBPathToPP1 := s_below`SolvableDBPathToPP1 cat [above`SolvableDBName];
//          // SolvableDBIsRamifiedAtEveryLevel
//          above`SolvableDBIsRamifiedAtEveryLevel := SolvableIsRamifiedAtEveryLevel(above);
//          // update s_below`SolvableDBParents
//          Append(~s_below`SolvableDBParents, above`SolvableDBName);
//          // append to aboves
//          Append(~aboves, above);
//          t1 := Cputime();
//          vprintf Solvable : "j = %o out of %o:\n", j, #all;
//          vprintf Solvable : "  #checks for path number = %o\n", #need_to_write_above;
//          vprintf Solvable : "  that took %o seconds\n", t1-t0;
//        end for;
//        // update need_to_write_above
//        need_to_write_above cat:= aboves;
//        // update need_to_write_below
//        Append(~need_to_write_below, s_below);
//        t1_i := Cputime();
//        vprintf Solvable : "\n";
//        vprintf Solvable : "Degree %o above %o done: ", d, name;
//        vprintf Solvable : "%o out of %o\n", i, #filenames_below;
//        vprintf Solvable : "That took %o seconds\n\n", t1_i-t0_i;
//      end for;
//      vprintf Solvable : "SolvableDB lists to be written returned\n";
//      return need_to_write_below, need_to_write_above;
//    end if;
//  else
//    error "degree is not valid";
//  end if;
//end intrinsic;
//
//intrinsic OrbitsToPassports(l::SeqEnum[SolvableDB]) -> SeqEnum[SeqEnum[SolvableDB]]
//  {Given a sequence of SolvableDB objects, sort them into passports.}
//  names := [PassportName(s) : s in l];
//  ParallelSort(~names, ~l);
//  passports := [[l[1]]];
//  for i := 2 to #names do
//    if names[i] eq names[i-1] then // same passport
//      Append(~passports[#passports], l[i]);
//    else // new passport
//      Append(~passports, [l[i]]);
//    end if;
//  end for;
//  return passports;
//end intrinsic;
//
//intrinsic IsRedundant(s::SolvableDB, t::SolvableDB) -> BoolElt
//  {}
//  check1 := PassportName(s) eq PassportName(t);
//  check2 := PassportName(ChildObject(s)) eq PassportName(ChildObject(t));
//  check3 := #GaloisOrbit(s) eq #GaloisOrbit(t);
//  if check1 and check2 and check3 then
//    gal_s := GaloisOrbit(s);
//    gal_t := GaloisOrbit(t);
//    S := Generic(Parent(gal_s[1][1]));
//    there_is_an_element_in_gal_s_not_conjugate_to_any_element_of_gal_t := false;
//    for sigma in gal_s do
//      sigma_conj_to_element_in_gal_s := false;
//      for tau in gal_t do
//        if IsConjugate(S, sigma, tau) then
//          sigma_conj_to_element_in_gal_s := true;
//        end if;
//      end for;
//      if not sigma_conj_to_element_in_gal_s then
//        there_is_an_element_in_gal_s_not_conjugate_to_any_element_of_gal_t := true;
//      end if;
//    end for;
//    if not there_is_an_element_in_gal_s_not_conjugate_to_any_element_of_gal_t then
//      return true;
//    else
//      return false;
//    end if;
//    return true;
//  end if;
//  return false;
//end intrinsic;
//
//intrinsic EliminateRedundancies(l::SeqEnum[SolvableDB]) -> SeqEnum[SolvableDB]
//  {uses IsRedundant over a sequence of objects.}
//  vprintf Solvable : "#before=%o:\n", #l;
//  for i := 1 to #l do
//    vprintf Solvable : " %o %o\n", Name(l[i]), IsRamifiedAtEveryLevel(l[i]);
//  end for;
//  for i := #l to 1 by -1 do
//    vprintf Solvable : " Comparing %o %o:\n", Name(l[i]), IsRamifiedAtEveryLevel(l[i]);
//    for j := 1 to i do
//      if IsRedundant(l[i],l[j]) and i ne j then
//        vprintf Solvable : "  %o %o redundant\n", Name(l[j]), IsRamifiedAtEveryLevel(l[j]);
//        is_i := IsRamifiedAtEveryLevel(l[i]);
//        is_j := IsRamifiedAtEveryLevel(l[j]);
//        if is_i then
//          if is_j then // both ramified
//            Remove(~l, i);
//            break j;
//          else // l[i] ramified, l[j] unramified
//            l[j] := l[i]; // want to keep l[i], so store it in l[j] and throw away l[i]
//            Remove(~l, i);
//            break j;
//          end if;
//        else
//          if is_j then // l[i] unramified, l[j] ramified
//            Remove(~l, i);
//            break j;
//          else // both unramified
//            Remove(~l, i);
//            break j;
//          end if;
//        end if;
//      else
//        vprintf Solvable : "  %o %o not redundant\n", Name(l[j]), IsRamifiedAtEveryLevel(l[j]);
//      end if;
//    end for;
//  end for;
//  vprintf Solvable : "#after=%o:\n", #l;
//  for i := 1 to #l do
//    vprintf Solvable : " %o %o\n", Name(l[i]), IsRamifiedAtEveryLevel(l[i]);
//  end for;
//  return l;
//end intrinsic;
//
//intrinsic PassportsAtLevel(d::RngIntElt : eliminate := false) -> Any
//  {returns passports as a SeqEnum[SeqEnum[SolvableDB]] all of which need to be written to file and below as SeqEnum[SolvableDB] which also need to be written to file.}
//  if IsEven(d) and #Factorization(d) eq 1 then
//    below, above := GaloisOrbitsAtLevel(d);
//    vprintf Solvable : "OrbitsToPassports...";
//    passports := OrbitsToPassports(above);
//    vprintf Solvable : "done.\n\n";
//    if eliminate then
//      new_passports := [];
//      for l in passports do
//        vprintf Solvable : "Eliminate redundancies %o out of %o\n", Index(passports, l), #passports;
//        l_new := EliminateRedundancies(l);
//        Append(~new_passports, l_new);
//        vprintf Solvable : Sprintf("Done: #before=%o, #after=%o\n\n", #l, #l_new);
//      end for;
//      return new_passports, below;
//    else
//      return passports, below;
//    end if;
//  else
//    error "degree is not valid";
//  end if;
//end intrinsic;
//
//intrinsic WritePassportsAtLevel(d::RngIntElt : eliminate := false) -> MonStgElt
//  {Calls PassportsAtLevel(d) and writes all relevant SolvablePassportDBs and SolvableDBs to file.}
//  if IsEven(d) and #Factorization(d) eq 1 then
//    passports, below := PassportsAtLevel(d : eliminate := eliminate);
//    // write all SolvableDBs
//    for l in passports do
//      for s in l do
//        SolvableDBWrite(s);
//      end for;
//    end for;
//    for s in below do
//      SolvableDBWrite(s);
//    end for;
//    // write all SolvabldPassportDBs
//    for l in passports do
//      spass := SolvablePassportDBExample(l);
//      SolvablePassportDBWrite(spass);
//    end for;
//    return Sprintf("\nSolvable Passports written for degree %o\n", d);
//  else
//    error "degree is not valid";
//  end if;
//end intrinsic;
//
//intrinsic ParentObjects(s::SolvableDB) -> SeqEnum[SolvableDB]
//  {}
//  filenames := [parent cat ".m" : parent in Parents(s)];
//  parents := [];
//  for filename in filenames do
//    try
//      parent := SolvableDBRead(filename);
//      Append(~parents, parent);
//    catch e1
//      vprintf Solvable : "only returning \"nonredundant\" parents\n";
//    end try;
//  end for;
//  return parents;
//end intrinsic;
//
//intrinsic ChildObject(s::SolvableDB) -> SolvableDB
//  {the object instead of the name}
//  return SolvableDBRead(Child(s) cat ".m");
//end intrinsic;
