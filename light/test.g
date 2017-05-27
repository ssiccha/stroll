

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
  return constructStrongLadder(groups);;
end;


makeGraphGroup := function(n)
  local omega, hom;
  omega := Orbit( SymmetricGroup(n), [1,2], OnSets ); 
  omega := List(omega);
  Sort(omega);
  hom := ActionHomomorphism(SymmetricGroup(n),omega,OnSets);
  return Image(hom);
end;



test := function(i,k)
  local ladder, U, g, s, u;
  ladder := makeStandardPermutationLadder(k);
  U := ladder.chain[i];
  g := Random(ladder.G);
  Print("found random element ",g,"\n");
  s := SmallestStrongPathToCoset(g,i,ladder);
  for u in U do
    if false = ladder.BoolLowerOrEqualPath(s,u*g,i) then
      Print("Fehler gefunden \n"); 
    fi;  
  od;
  if not s*g^-1 in U then
    Print("Fehler gefunden \nElement is not in coset"); 
  fi;
end;


LeiterspielLightDoubleCosets := function(k,B,ladder)
  local coset, stabilizer, L, g, stab, canonizer, result, z, U, tmp, i, h;
  coset := rec(g := One(B), stabilizer := B);
  L := [ [coset] ];
  for i in [ 2 .. k ] do
    L[i] := [];
    for coset in L[i-1] do
      g := coset.g;
      stab := coset.stabilizer;
      if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
        for h in ladder.transversal[i] do
          # stab is more efficient then B
          ladder.C[i-1] := stab;
          canonizer := CheckSmallestInDoubleCosetSplit(i,h*g,ladder);
          if One(g) = canonizer then
            coset := rec(g := h*g, stabilizer := ladder.C[i]);
            Add(L[i],coset);
          fi;
#         result := FindSmallerOrbitRepresentative(h*g,i,ladder,stab);
#         if true = result.isCanonical then
#           coset := rec(g := h*g, stabilizer := result.stabilizer);
#           Add(L[i],coset);
#         fi;
        od;
      else
        # this is needed to calculate the stabilizer
        result := FindSmallerOrbitRepresentative(g,i,ladder,B);
        if not result.isCanonical then
          # coset can be build from a smaller coset
          continue;
        fi;
        z := SmallestStrongPathToCoset(g,i,ladder);
        U := ConjugateGroup(result.stabilizer,z^-1);
        tmp := FindOrbitRep( g*z^-1, i, U, ladder);
        # the coset can be constructed from multiple cosets in the preimage
        # choose one of them, so that the new coset is constructed exactly once
        if not 1 = tmp.orbitMinPosition then
          # this is needed to prevent double counts
          continue;
        fi;
        coset := rec(g := g, stabilizer := result.stabilizer);
        Add(L[i],coset);
      fi; 
    od;
  od;
  return L;
end;


LeiterspielLightGraphGeneration := function(k,n)
  local ladder, B;
  ladder := makeStandardPermutationLadder(n*(n-1)/2);
  B := makeGraphGroup(n);
  return LeiterspielLightDoubleCosets(k,B,ladder);
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



BruteForceCanonizeCoset := function( g, k, ladder, B )
  local gu, orbit, smallest, o;
  gu := RightCoset(ladder.chain[k],g);  
  orbit := Orbit(B,gu,OnRight);
  smallest := orbit[1];
  smallest := Representative(smallest);
  smallest := SmallestStrongPathToCoset(smallest, k, ladder);
  for o in orbit do
    o := Representative(o);
    o := SmallestStrongPathToCoset(o,k,ladder);
    if not ladder.LowerOrEqualPath(smallest, o, k) then
      smallest := o;
    fi;
  od;
  return smallest;
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





