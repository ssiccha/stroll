
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



LeiterspielLightGraphGeneration := function(k,n)
  local ladder, B, graph, stabilizer, L, g, stab, result, z, U, tmp, i, h;
  ladder := makeStandardPermutationLadder(n*(n-1)/2);
  B := makeGraphGroup(n);
  graph := rec(g := One(B), stabilizer := B);
  L := [ [graph] ];
  for i in [ 2 .. k ] do
    L[i] := [];
    for graph in L[i-1] do
      g := graph.g;
      stab := graph.stabilizer;
      if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
        for h in ladder.transversal[i] do
          # stab is more efficient then B
          result := FindSmallerOrbitRepresentative(h*g,i,ladder,stab);
          if true = result.isCanonical then
            graph := rec(g := h*g, stabilizer := result.stabilizer);
            Add(L[i],graph);
          fi;
        od;
      else
        z := SmallestStrongPathToCoset(g,i,ladder);
        # this is needed to calculate the stabilizer
        result := FindSmallerOrbitRepresentative(g,i,ladder,B);
        if not result.isCanonical then
          # graph can be build from a smaller graph
          continue;
        fi;
        U := ConjugateGroup(result.stabilizer,z^-1);
        tmp := FindOrbitRep( g*z^-1, i, U, ladder);
        # A_ig*z^-1 = A_i*tmp.orbitCanonicalElement ?
        if not g*z^-1*tmp.orbitCanonicalElement^-1 in ladder.chain[i-1] then
          # this is needed to prevent double counts
          continue;
        fi;
        graph := rec(g := g, stabilizer := result.stabilizer);
        Add(L[i],graph);
      fi; 
    od;
  od;
  return L;
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





