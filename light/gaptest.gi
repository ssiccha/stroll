BuildStroLLSubladder := 0;

buildStroLLTransversals := function(groups)
  local ladder, i, index, U ;
  ladder := rec();
  ladder.G := groups[1];
  ladder.chain := [groups[1]]; 
  ladder.subgroupIndex := [1];
  ladder.transversal := [RightTransversal(ladder.G,ladder.G)];
  ladder.rightcosets := [RightCosets(ladder.G,ladder.G)];
  for i in [2 .. Size(groups)] do
    if false = IsSubgroup(ladder.G,groups[i]) then
      Error("Entry ",i," in grouplist is not a subgroup of the group on the first position in the grouplist\n");
      return;
    fi;
    U := groups[i];
    index := IndexNC(ladder.G,U);
    ladder.subgroupIndex[i] := index;
    if ladder.subgroupIndex[i-1] > index then
      if false = IsSubgroup(U,ladder.chain[i-1]) then
        Error("Entry ",i," in grouplist is not a group containing the previous group on position ",i-1," in the grouplist\n"); 
        return;
      fi;
      ladder.transversal[i] := RightTransversal(U,ladder.chain[i-1]);
      ladder.rightcosets[i] := RightCosets(U,ladder.chain[i-1]);
    else
      if false = IsSubgroup(ladder.chain[i-1],U) then
        Error("Entry ",i," in list is not a subgroup of the previous group on position ",i-1," in the grouplist\n"); 
        return;
      fi;
      ladder.transversal[i] := RightTransversal(ladder.chain[i-1],U);
      ladder.rightcosets[i] := RightCosets(ladder.chain[i-1],U);
    fi;
    ladder.chain[i] := U;
  od;
  return ladder;
end;



BuildStroLLPathRepresentativeMapping := function(ladder)
  ladder.PathRepresentative := function(g,k)
    local z, position, canonical, i;
    z := One(ladder.G); 
    for i in [ 2 .. k ] do
      if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
        position := PositionCanonical(ladder.transversal[i],g);
        canonical := ladder.transversal[i][position];
        g := g*canonical^-1;
        z := canonical*z;
      fi;
    od;
    return z;
  end;
end;



BuildStroLLPathCompare := function(ladder)
  ladder.LowerOrEqualPath := function( a, b, k)
    local i, position_a, position_b, canonical;
    for i in [ 2 .. k ] do
      if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
        position_a := PositionCanonical(ladder.transversal[i],a);        
        position_b := PositionCanonical(ladder.transversal[i],b);        
        if  position_a < position_b then
          return true;
        elif  position_a > position_b  then 
          return false;
        fi;
        canonical := ladder.transversal[i][position_a];
        a := a*canonical^-1;
        b := b*canonical^-1;
      fi; 
    od;
    return true;
  end;
end;


BuildStroLLTransversalCompare := function(ladder)
  ladder.LowerOrEqualForLadderGroupCosets := function( a, b, i)
    local position_a, position_b, canonical;
    ## DEBUG 
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      if not a in ladder.chain[i-1] then
        Error("a is not in A_{i-1}");
      fi;
      if not b in ladder.chain[i-1] then
        Error("b is not in A_{i-1}");
      fi;
      position_a := PositionCanonical(ladder.transversal[i],a);        
      position_b := PositionCanonical(ladder.transversal[i],b);        
      if  position_a > position_b then
        return false;
      fi;
    fi; 
    return true;
  end;
end;



FindOrbitRep := function( g, k, V, ladder)
  local result, transv, U, H, ug, tmp, ur, o;
  result := rec();
  transv := ladder.transversal[k];
  if ladder.subgroupIndex[k-1] < ladder.subgroupIndex[k] then
    U := ladder.chain[k];
    H := ladder.chain[k-1];
  else
    U := ladder.chain[k-1];
    H := ladder.chain[k];
  fi;
  ug := RightCoset(U,g);
  ## DEBUG 
  if  not IsSubgroup(H,V) then
    Error("the operating group V is not a subgroup of k-th ladder group");
  fi;
  if  not g in H then
    Error("g is not in the k-th ladder group");
  fi;
  ## DEBUG end 
  tmp := OrbitStabilizer(V,ug,OnRight);
  result.stabilizer := tmp.stabilizer;
  result.orbitRepresentatives := List( tmp.orbit, x -> Representative(x) ); 
  result.orbitPositions := List( result.orbitRepresentatives, x -> PositionCanonical(transv,x) ); 
  result.orbitRepresentatives := List( result.orbitPositions, x -> transv[x] ); 
  result.orbitMinPosition := Minimum(result.orbitPositions);
  result.orbitCanonicalElement := transv[result.orbitMinPosition]; 
  ur := RightCoset(U,result.orbitCanonicalElement);
  result.canonizer := RepresentativeAction(V,ug,ur,OnRight);
  ## DEBUG begin
  if not result.orbitCanonicalElement in H then
    Error("the canonical element is outside of the given range");
  fi;
  if not result.canonizer in V then
    Error("canonizer is not in the operating group"); 
  fi;
  ## DEBUG end 
  return result;
end;




# This function needs a ladder [A_1,..,A_k] and for all indizes i<k with A_i >= A_i+1 a total order
# on the cosets A_i\A_i+1 must be defined. 
#
# For a given ladder [A_1,..,A_k] and elements a_1,..,a_k \in A_1 the tupel [A_1a_1,..,A_ka_k] is a 
# strong path, if and only if there exist an element h \in A_1, so that 
# [A_1h,..,A_kh] = [A_1a_1,..,A_ka_k].
# The given total order allows it to define a total order on the set of strong paths of length up to k.
# 
# Given the index k, a ladder [A_1,..,A_k] and an element g \in A_1 this function calculates the 
# smallest strong path of length k, whose last component is the coset A_kg.
#
SmallestStrongPathToCoset := function(g,k,ladder)
  local z, U, zi, i, b, stab, tmp, h;
  h := g;
  z := One(ladder.G);
  stab := ConjugateGroup(ladder.chain[k],h);
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      # After step i the first i components of the 
      # smallest path to the coset A_kg are (A_1h*z,...,A_ih*z) 
      # and A_kh*z = A_kg
      # stab^z is the combined stabilizer of
      # the path (A_1h*z,...,A_ih*z) and A_kh*z
      # h is in A_i, thus we can use the order on A_{i+1}\A_i to determine 
      # the (i+1)-th component of the smallest path to A_kg
      tmp := FindOrbitRep(h,i,stab,ladder);
      stab := tmp.stabilizer;
      b := tmp.canonizer; 
      zi := tmp.orbitCanonicalElement;   
      h := h*b;
      stab := ConjugateGroup(stab,b);
      h := h*zi^-1;
      stab := ConjugateGroup(stab,zi^-1);
      z := zi*z;
      # Print("h = ",h,"\n");
      # Print("b = ",b,"\n");
      # Print("zi = ",zi,"\n\n");
      if  not h*z*g^-1 in ladder.chain[k] then
        ## DEBUG !!!
        Error("A_kh*z <> A_kg \nargument g = ",g,"\nargument k = ",k,"\n"); 
      fi;
    fi; 
  od;
  return h*z;
end; 




NextStroLLStep := 0;
SplitOrbit := 0;
FuseOrbit := 0;
CheckCanonicalStroll := 0;

# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
SplitOrbit := function( block, blockStack, p, k, ladder, debug)
  local g, b, i, z, smallest, canonizerToSmallest, e, preimage, U, tmp, canonical, canonizer, newBlock, h;
  Print("\nDebug Mode");
  g := block.g;
  b := block.b;
  i := block.i;
  z := ladder.PathRepresentative(p,i);
  smallest := p*z^-1;
  canonizerToSmallest := One(p);
  # preimage is a transversal of E[k][i+1]\E[k][i];
  e := RightCoset(ladder.E[k][i+1],One(g));
  preimage := Orbit(ladder.E[k][i], e, OnRight);  
  preimage := List(preimage,x -> Representative(x));
  U := ConjugateGroup(ladder.C[i],z^-1);
  for h in preimage do
    ## DEBUG 
    if  not h*g*b*z^-1 in ladder.chain[i] then
      Error("h*g*b*z^-1 is not in A_i");
    fi;
    ## DEBUG end
    tmp := FindOrbitRep( h*g*b*z^-1, i+1, U, ladder );
    canonical := tmp.orbitCanonicalElement;
    ## DEBUG 
    if not canonical in ladder.chain[i] then
      Error("the canonical orbit representative is not in A_i");
    fi;
    ## DEBUG end
    canonizer := tmp.canonizer;
    if false = ladder.LowerOrEqualForLadderGroupCosets( smallest, canonical, i+1) then
      smallest := canonical;
      canonizerToSmallest := b*canonizer^z;
    elif false = ladder.LowerOrEqualForLadderGroupCosets( canonical, p*z^-1, i+1) then
      continue;
    fi;
    newBlock := rec( g := h*g, b := b*canonizer^z, i := i+1 );
    Print( "newBlock ", newBlock, "\n" );
    StackPush(blockStack,newBlock);
  od;
  return canonizerToSmallest; 
end;

# Several A_ig yield the same A_{i+1}g.
# FuseOrbit only puts one of these g onto the stack
FuseOrbit := function( block, blockStack, ladder )
  local g, i, b, z, U, tmp;
  g := block.g;
  i := block.i;
  b := block.b;
  ## TODO is this performance relevant?
  z := SmallestStrongPathToCoset(g,i+1,ladder);
  U := ConjugateGroup(ladder.C[i+1],b^-1*z^-1);
  tmp := FindOrbitRep( g*z^-1, i+1, U, ladder);
  # A_ig*z^-1 = A_i*tmp.orbitCanonicalElement ?
  if g*z^-1*tmp.orbitCanonicalElement^-1 in ladder.chain[i] then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
    Print( "newBlock ", block, "\n" );
  fi;
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
CheckSmallestInDoubleCosetFuse := function( k, p, ladder)
  local block, i, blockStack, b, isSplitStep, canonizer;
  Print("\n");
  Print(" ---- ---- ---- ", k, " ---- ---- ----\n");
  Print(" ---- ---- ---- ", k, " ---- ---- ----\n");
  Print(" ---- ---- ---- ", k, " ---- ---- ----\n");
  Print("\n");
  counter := 0;
  ladder.C[k] := ladder.C[k-1];
  block := rec( g := p, b := One(p), i := 1);
  blockStack := StackCreate(100);
  StackPush( blockStack, block);
  while not StackIsEmpty(blockStack) do
    counter := counter + 1;
    Print( "----------- counter = ", counter, "-----------\n" );
    block := StackPop(blockStack);
    Print( "Pop: ", block, "\n" );
    i := block.i;
    b := block.b;
    if i+1 = k then
      Print("Stabilizer size before: ", Size(ladder.C[i+1]), "\n");
      ladder.C[i+1] := ClosureGroup(ladder.C[i+1],b);
      Print("After: ", Size(ladder.C[i+1]), "\n");
      continue;
    fi;
    isSplitStep := ladder.subgroupIndex[i] < ladder.subgroupIndex[i+1];
    if isSplitStep then
      ## DEBUG 
      if  counter = 10 and k = 8 then
        canonizer := SplitOrbit(block,blockStack,p,k,ladder,true);
        Error("break");
      else
        canonizer := SplitOrbit(block,blockStack,p,k,ladder,false);
      fi;
      if not canonizer = One(g) then
        return canonizer; 
      fi;
    else
      FuseOrbit(block,blockStack,ladder);
    fi;
  od;
  return One(g);
end;



CheckSmallestInDoubleCosetSplit := function( i, p, ladder) 
  local z, U, tmp, c;
  # A_ipz^-1c is smallest in its C_{i-1} orbit
  z := ladder.PathRepresentative(p,i-1);
  U := ConjugateGroup(ladder.C[i-1],z^-1);
  tmp := FindOrbitRep( p*z^-1, i, U, ladder );
  c := tmp.canonizer;
  # A_ipz^-1 = A_ipz^-1c
  if not (p*z^-1*c)*(p*z^-1)^-1 in ladder.chain[i] then
    return c^z;
  fi;
  ladder.C[i] := ConjugateGroup(tmp.stabilizer,z);
  return One(p);
end;



FindSmallerOrbitRepresentative := function(g, k, ladder, B)
  local result, stabilizer, p, canonizer, i;
  ladder.C := [B];
  result := rec(isCanonical := false, 
                canonizer := One(g), 
                stabilizer := Group(One(g)));
  p := SmallestStrongPathToCoset(g,k,ladder);
  for i in [ 2 .. k ] do
    if  ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i]  then
      canonizer := CheckSmallestInDoubleCosetSplit(i,p,ladder); 
    else
      canonizer := CheckSmallestInDoubleCosetFuse(i,p,ladder);
    fi;
    if not canonizer = One(canonizer) then
      result.canonizer := canonizer;
      return result; 
    fi;
  od;
  result.isCanonical := true;
  result.stabilizer := ladder.C[k];
  return result;
end;




constructStrongLadder := function(groups)
  local ladder;
  ladder := buildStroLLTransversals(groups);
  BuildStroLLPathRepresentativeMapping(ladder);
  BuildStroLLPathCompare(ladder);
  BuildStroLLTransversalCompare(ladder);
  BuildStroLLSubladder(ladder);
  return ladder;
end;





makeStandardPermutationLadder := function(n)
  local groups, gens, i;
  groups := [SymmetricGroup(n)];
  groups[2] := Stabilizer(groups[1],1);
  for i in [ 2 .. n-1 ] do
    groups[2*i-1] := Stabilizer(groups[2*i-2],i);
    gens := List(GeneratorsOfGroup(groups[2*i-1]));
    Add(gens,(1,i));
    groups[2*i] := Group(gens);
  od;
  groups[2*n-1] := SymmetricGroup(n);
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




BuildStroLLSubladder := function(ladder)
  local i, j, c;
  ladder.E := [];
  for i in [ 2 .. Size(ladder.chain)-1 ] do
    ladder.E[i] := [ladder.chain[i]];
    for j in [ 2 .. i ] do
      if ladder.subgroupIndex[j-1] < ladder.subgroupIndex[j] then
        c := RightCoset(ladder.chain[j],One(ladder.G));
        ladder.E[i][j] := Stabilizer(ladder.E[i][j-1],c,OnRight); 
      else
        ladder.E[i][j] := Intersection(ladder.chain[i],ladder.chain[j]); 
      fi;
    od;
  od;
end;
