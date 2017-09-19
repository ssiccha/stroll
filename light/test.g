

makeStandardPermutationLadder := function(n)
  local groups, gens, i;
  groups := [SymmetricGroup(n)];
  groups[2] := Stabilizer(groups[1],1);
  for i in [ 2 .. n ] do
    groups[2*i-1] := Stabilizer(groups[2*i-2],i);
    gens := List(GeneratorsOfGroup(groups[2*i-1]));
    Add(gens,(1,i));
    groups[2*i] := Group(gens);
  od;
# groups[2*n-1] := SymmetricGroup(n);
  return StroLLBuildLadder(groups);
end;


makeGraphGroup := function(n)
  local omega, hom;
  omega := Orbit( SymmetricGroup(n), [1,2], OnSets ); 
  omega := List(omega);
  Sort(omega);
  hom := ActionHomomorphism(SymmetricGroup(n),omega,OnSets);
  return Image(hom);
end;



LeiterspielLightDoubleCosets := function(k,B,ladder)
  local orbAndStab, cosetStack, coset, i, L, g, stab, U, V, preimage, canonizer, z, h;
  orbAndStab := rec();
  orbAndStab.C := [B];
  cosetStack := StackCreate(100);
  coset := rec(g := One(B), stabilizer := B, i := 1);
  StackPush(cosetStack,coset);
  L := [ [coset] ];
  for i in [ 2 .. k ] do
    L[i] := [];
  od;
  while not StackIsEmpty(cosetStack) do
    coset := StackPop(cosetStack);
    g := coset.g;
    i := coset.i+1;
    stab := coset.stabilizer;
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      U := ladder.cut1toI[i];
      V := ladder.cut1toI[i-1];
      preimage := RightTransversal(V,U);
      for h in preimage do
        # stab is more efficient then B
        # orbAndStab.C[i-1] := stab;
        # z := SmallestStrongPathToCoset(h*g,i,ladder);
        canonizer := CheckSmallestInDoubleCosetSplit(i,h*g,orbAndStab,ladder);
        if One(g) = canonizer then
          coset := rec(g := h*g, stabilizer := orbAndStab.C[i],i := i);
          Add(L[i],coset);
          if not i = k then
            StackPush(cosetStack,coset);
          fi;
        fi;
      od;
    else
      # If p is the smallest path to A_ip, then 
      # A_ig should be constructed from the coset A_{i-1}p.
      # So the check for canonity can be done with this z: 
      z := SmallestStrongPathToCoset(g,i,ladder);
      if not g*z^-1 in ladder.chain[i-1] then
        continue;
      fi;
      # In a breadth first search algorithm the stabilizer orbAndStab.C[i-1] 
      # could have been overwritten.
      # This is a depth first search algorithm so all stabilizers 
      # besides the last one stay unchanged.
      orbAndStab.C[i-1] := coset.stabilizer;
      canonizer := CheckSmallestInDoubleCosetFuse(i,g,orbAndStab,ladder);
      if not One(g) = canonizer then
        # coset can be constructed from a smaller coset
        continue;
      fi;
      coset := rec(g := g, stabilizer := orbAndStab.C[i], i := i);
      Add(L[i],coset);
      #### DEBUG begin ####
      # cut := Intersection(B^(g^-1),ladder.chain[i]);
      # if not Size(coset.stabilizer) = Size(cut) then
      #   Error("\nstabilizer sizes are not equal\n g = ",g," Size(stabilizer) = ",Size(coset.stabilizer)," Size(cut) = ",Size(cut)," stabilizer = ",coset.stabilizer,"\n\n");
      # fi;
      #### DEBUG end ####
      if not i = k then
        StackPush(cosetStack,coset);
      fi;
    fi; 
  od;
  return L;
end;


## This function can be checked against the sequence A008406 in www.oeis.org.
## If a_i refers to the number of doublecosets in A_i\A_1/B,
## the sequence of all a_i with even index is a subsequence of A008406.
LeiterspielLightGraphGeneration := function(n,k)
  local ladder, B, cosets, sum, graphs, i;
  if k < 2 or n < 3 then
    return;
  fi;
  Print("Constructing all graphs on ",n," vertices with up to ",k," edges:\n");
  ladder := makeStandardPermutationLadder(n*(n-1)/2);
  B := makeGraphGroup(n);
  cosets := LeiterspielLightDoubleCosets(k*2,B,ladder);
  sum := 0;
  graphs := [Size(cosets[1])];
  for i in [ 1 .. Size(cosets)  ] do 
    if 0 = i mod 2 then 
      graphs[i/2] := Size(cosets[i]);
    fi; 
  od;
  for i in [ 1 .. Size(graphs)  ] do 
    sum := sum + graphs[i];
    Print(graphs[i]," graphs with ",i," edges\n"); 
  od;
  Print("\n"); 
  for i in [ 1 .. Size(graphs)  ] do 
    Print(graphs[i],","); 
  od;
  Print("\n\n",sum," graphs on ",n," vertices with up to ",k," edges\n"); 
  # return cosets;
end;




LeiterspielLightCanonizeCoset := function( g, k, ladder, B )
  local c, result;
  c := One(g);
  repeat
    result := FindSmallerOrbitRepresentative(g,k,ladder,B);
    c := result.canonizer;
    g := g*c;
    if not c = One(c) then
      Print( "--- found smaller --- Canonizer is ", c, "\n" );
    fi;
  until c = One(g);
  return g;
end;



CreateRandomGraphWithLadderAndB := function(i, n)
  local ladder, B, g, result;
  ladder := makeStandardPermutationLadder(n*(n-1)/2);
  if i > Size(ladder.chain)  then
    Error("there is no ladder group for such a big index i"); 
  fi;
  B := makeGraphGroup(n); 
  g := PseudoRandom(ladder.G);
  result := rec( g := g, ladder := ladder, B := B );
  return result;
end;




LeiterspielLightGraphGenerationProfiling := function(n,k)
  local fkts;
  ClearProfile();
  fkts := [CanonicalRightCosetElement
          ,CheckSmallestInDoubleCosetSplit
          ,CheckSmallestInDoubleCosetFuse
          ,FindOrbitRep
          ,FindSmallerOrbitRepresentative
          ,FuseOrbit
          ,makeGraphGroup
          ,makeStandardPermutationLadder
          ,LeiterspielLightDoubleCosets
          ,PathRepresentative
          ,BlockStabilizerOrbit
          ,SmallestStrongPathToCoset
          ,SplitOrbit
          ,BlockStabilizerPosition
          ,ReinitializeOrbitAndStabilizerStorage
          ];
  ProfileFunctions(fkts);
  LeiterspielLightGraphGeneration(n,k);
  DisplayProfile();
  UnprofileFunctions(fkts);
  ClearProfile();
end;

















