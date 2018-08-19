

StandardPermutationLadder := function(n)
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


GraphGroup := function(n)
  local omega, hom;
  omega := Orbit( SymmetricGroup(n), [1,2], OnSets ); 
  omega := List(omega);
  Sort(omega);
  hom := ActionHomomorphism(SymmetricGroup(n),omega,OnSets);
  return Image(hom);
end;






## This function can be checked against the sequence A008406 in www.oeis.org.
## If a_i refers to the number of doublecosets in A_i\A_1/B,
## the sequence of all a_i with even index is a subsequence of A008406.
LeiterspielLightGraphGeneration := function(n,k)
  local graphs, B, ladder, cosets, m, sum, i;
  if n < 0 or k < 0 or 2*k > n*(n-1) then
    Error("There are no graphs on ",n," vertices with up to ",k," edges\n");
    return;
  fi;
  Print("\nConstructing all graphs on ",n," vertices with up to ",k," edges:\n");
  Print(1," graphs with ",0," edges\n"); 
  if k < 1 or n < 2 then
    return;
  fi;
  graphs := [1];
  B := GraphGroup(n);
  ladder := StandardPermutationLadder(n*(n-1)/2);
  cosets := StroLLLightDoubleCosets(k*2,B,ladder);
  for i in [ 1 .. k ] do 
    m := Size(cosets[2*i]);
    Print(m," graphs with ",i," edges\n"); 
    graphs[i+1] := m; 
  od;
  Print("\n"); 
  sum := 0;
  for i in [ 1 .. Size(graphs)  ] do 
    m := graphs[i];
    Print(m,","); 
    sum := sum + m;
  od;
  Print("\n\n",sum," graphs on ",n," vertices with up to ",k," edges\n"); 
  # return cosets;
end;



## This function can be checked against the sequence A008406 in www.oeis.org.
## If a_i refers to the number of doublecosets in A_i\A_1/B,
## the sequence of all a_i with even index is a subsequence of A008406.
LeiterspielBreadthGraphGeneration := function(n,k)
  local graphs, B, ladder, cosets, m, sum, i;
  if n < 0 or k < 0 or k > n*(n-1)/2 then
    Error("There are no graphs on ",n," vertices with up to ",k," edges\n");
    return;
  fi;
  Print("\nConstructing all graphs on ",n," vertices with up to ",k," edges:\n");
  Print(1," graphs with ",0," edges\n"); 
  if k < 1 or n < 2 then
    return;
  fi;
  graphs := [1];
  B := GraphGroup(n);
  ladder := StandardPermutationLadder(n*(n-1)/2);
  cosets := StroLLBreadthDoubleCosets(k*2,B,ladder);
  for i in [ 1 .. k ] do 
    m := Size(cosets[2*i]);
    Print(m," graphs with ",i," edges\n"); 
    graphs[i+1] := m; 
  od;
  Print("\n"); 
  sum := 0;
  for i in [ 1 .. Size(graphs)  ] do 
    m := graphs[i];
    Print(m,","); 
    sum := sum + m;
  od;
  Print("\n\n",sum," graphs on ",n," vertices with up to ",k," edges\n"); 
  # return cosets;
end;



LeiterspielLightCanonizeCoset := function( g, k, ladder, B )
  local c, result;
  c := One(g);
  repeat
    result := StroLLLightFindSmallerDCRep(g,k,ladder,B);
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
  ladder := StandardPermutationLadder(n*(n-1)/2);
  if i > Size(ladder.chain)  then
    Error("there is no ladder group for such a big index i"); 
  fi;
  B := GraphGroup(n); 
  g := PseudoRandom(ladder.G);
  result := rec( g := g, ladder := ladder, B := B );
  return result;
end;


LeiterspielLightGraphGenerationProfiling := function(n,k)
  local fkts;
  ClearProfile();
  fkts := [CanonicalRightCosetElement
          ,StroLLLightSplitCanonicalDCReps
          ,StroLLLightSplitCanonicalDCReps
          #,FindOrbitRep
          ,StroLLLightFindSmallerDCRep
          ,StroLLLightFuseOrbit
          ,GraphGroup
          ,StandardPermutationLadder
          ,StroLLLightDoubleCosets
          ,PathRepresentative
          ,BlockStabilizerOrbit
          ,StroLLSmallestPathToCoset
          ,StroLLLightSplitOrbit
          ,BlockPosition
          ,BlockStabilizerReinitialize
          ,PositionCanonical
          ,StroLLSmallestPathHelper
          ,Image
          ];
  ProfileFunctions(fkts);
  LeiterspielLightGraphGeneration(n,k);
  DisplayProfile();
  UnprofileFunctions(fkts);
  ClearProfile();
end;






LeiterspielBreadthGraphGenerationProfiling := function(n,k)
  local fkts;
  ClearProfile();
  fkts := [CanonicalRightCosetElement
          ,StroLLLightSplitCanonicalDCReps
          ,StroLLLightSplitCanonicalDCReps
          #,FindOrbitRep
          ,StroLLLightFindSmallerDCRep
          ,StroLLLightFuseOrbit
          ,GraphGroup
          ,StandardPermutationLadder
          ,StroLLLightDoubleCosets
          ,PathRepresentative
          ,BlockStabilizerOrbit
          ,StroLLSmallestPathToCoset
          ,StroLLLightSplitOrbit
          ,BlockPosition
          ,BlockStabilizerReinitialize
          ,PositionCanonical
          ,StroLLSmallestPathHelper
          ,Image
          ];
  ProfileFunctions(fkts);
  LeiterspielBreadthGraphGeneration(n,k);
  DisplayProfile();
  UnprofileFunctions(fkts);
  ClearProfile();
end;

















