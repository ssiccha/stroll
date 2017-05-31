

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
  return constructStrongLadder(groups);
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
  local coset, stabilizer, L, cosetStack, g, i, stab, canonizer, result, z, U, tmp, h;
  ladder.C := [B];
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
    if  i = k then
      continue;
    fi;
    stab := coset.stabilizer;
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      for h in ladder.transversal[i] do
        # stab is more efficient then B
#       ladder.C[i-1] := stab;
#       z := SmallestStrongPathToCoset(h*g,i,ladder);
        canonizer := CheckSmallestInDoubleCosetSplit(i,h*g,ladder);
        if One(g) = canonizer then
          coset := rec(g := h*g, stabilizer := ladder.C[i],i := i);
          Add(L[i],coset);
          StackPush(cosetStack,coset);
        fi;
      od;
    else
      # If p is the smallest path to A_ip, then 
      # A_ig should be constructed from the coset A_{i-1}p.
      # So the check for canonity can be done with this z: 
      z := SmallestStrongPathToCoset(g,i-1,ladder);
      g := SmallestStrongPathToCoset(g,i,ladder);
      if not g*z^-1 in ladder.chain[i-1] then
        continue;
      fi;
      # the stabilizer ladder.C[i-1] could have been overwritten in 
      # another branch. 
      # In an depth first search algorithm the other stabilizers stay unchanged.
      ladder.C[i-1] := coset.stabilizer;
      canonizer := CheckSmallestInDoubleCosetFuse(i,g,ladder);
      if not One(g) = canonizer then
        # coset can be constructed from a smaller coset
        continue;
      fi;
      coset := rec(g := g, stabilizer := ladder.C[i], i := i);
      Add(L[i],coset);
      StackPush(cosetStack,coset);
    fi; 
  od;
  return L;
end;


## This function can be checked against the sequence A008406 in oeis.org.
## If a_i refers to the number of doublecosets in A_i\A_1/B,
## the sequence of all a_i with even index is a subsequence of A008406.
LeiterspielLightGraphGeneration := function(k,n)
  local ladder, B, graphs, i;
  ladder := makeStandardPermutationLadder(n*(n-1)/2);
  B := makeGraphGroup(n);
  graphs := LeiterspielLightDoubleCosets(k,B,ladder);
  for i in [ 1 .. Size(graphs)  ] do 
    if 0 = i mod 2 then 
      Print("Number of canonical coset in A_",i," G B is ",Size(graphs[i]),"\n"); 
    fi; 
  od; 
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





