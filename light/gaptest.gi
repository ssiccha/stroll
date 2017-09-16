


LowerOrEqualPath := function( a, b, k, ladder)
  local perm_a, position_a, perm_b, position_b, canonical, i;
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      perm_a := Image(ladder.hom[i],a);
      position_a := 1^perm_a;
      perm_b := Image(ladder.hom[i],b);
      position_b := 1^perm_b;
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
  local z, position, preimage, tmp, hsmall, canonical, i, h;
  z := One(ladder.G);
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      position := Size(ladder.transversal[i]) + 1;
      preimage := ladder.splitTransversal[k][i]; 
      for h in preimage do
        tmp := PositionCanonical(ladder.transversal[i],h*g);
        if position > tmp then
          position := tmp; 
          hsmall := h;
        fi;
      od;
      canonical := ladder.transversal[i][position];
      g := hsmall*g*canonical^-1;
      z := canonical*z;
    fi; 
  od;
  return z;
end; 






# A_i <= A_{i-1} and a and b are in the preimage of A_{i-1}p;
LowerOrEqualInStabilizerOf_p := function( a, b, i, p, ladder )
  local z, position_a, position_b;
  z := PathRepresentative(p,i-1,ladder);
  if not a*z^-1 in ladder.chain[i-1] then
    Error("the Element a must be in the ladder group A_{i-1}p");
  fi;
  if not b*z^-1 in ladder.chain[i-1] then
    Error("the Element b must be in the ladder group A_{i-1}p");
  fi;
  position_a := PositionCanonical(ladder.transversal[i],a*z^-1);        
  position_b := PositionCanonical(ladder.transversal[i],b*z^-1);        
  if position_a <= position_b then
    return true; 
  fi;
  return false;
end;



# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
SplitOrbit := function( block, blockStack, p, k, ladder )
  local g, b, i, preimage, c, tmp, newBlock, h;
  g := block.g;
  b := block.b;
  i := block.i;
  # preimage is a transversal of E[k][i+1]\E[k][i];
  preimage := ladder.splitTransversal[k][i+1]; 
  for h in preimage do
    c := SmallestOrbitRepresentativeInStabilizerOf_p( h*g*b, i+1, p, ladder );
    if false = LowerOrEqualInStabilizerOf_p( p, h*g*b*c, i+1, p, ladder) then
      return b*c;
    elif false = LowerOrEqualInStabilizerOf_p( h*g*b*c, p, i+1, p, ladder) then
      continue;
    fi;
    newBlock := rec( g := h*g, b := b*c, i := i+1 );
    StackPush(blockStack,newBlock);
  od;
  return One(p); 
end;

# Several A_ig yield the same A_{i+1}g.
# FuseOrbit only puts exactly one of them onto the stack
FuseOrbit := function( block, blockStack, p, ladder )
  local g, i, b, z, c;
  g := block.g;
  i := block.i;
  b := block.b;
  if Size(ladder.C[i]) = Size(ladder.C[i+1]) then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
    return;
  fi;
  # prevent double processing:
  # the block is processed if and only if 
  # A_ig*z^-1*p is smallest in its orbit under the action of ladder.C[i+1]?
  ## TODO is this performance relevant?
  # z := SmallestStrongPathToCoset(g,i+1,ladder);
  # c := SmallestOrbitRepresentativeInStabilizerOf_p( g*(z^-1)*p, i+1, p, ladder );
  c := CanonicalRightCosetElement(ladder.C[i+1]^(b^-1),b);
  if g*c*p^-1 in ladder.chain[i] then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
  fi;
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
CheckSmallestInDoubleCosetFuse := function( k, p, ladder)
  local one, block, i, blockStack, b, isSplitStep, canonizer;
  one := One(p);
  ladder.C[k] := ladder.C[k-1];
  block := rec( g := p, b := One(p), i := 1);
  blockStack := StackCreate(100);
  StackPush( blockStack, block);
  while not StackIsEmpty(blockStack) do
    block := StackPop(blockStack);
    i := block.i;
    b := block.b;
    if i+1 = k then
      ladder.C[i+1] := ClosureGroup(ladder.C[i+1],b);
    else
      isSplitStep := ladder.subgroupIndex[i] < ladder.subgroupIndex[i+1];
      if isSplitStep then
        canonizer := SplitOrbit(block,blockStack,p,k,ladder);
        if not canonizer = one then
          return canonizer; 
        fi;
      else
        FuseOrbit(block,blockStack,p,ladder);
      fi;
    fi;
  od;
  return One(p);
end;



CheckSmallestInDoubleCosetSplit := function( i, p, ladder) 
  local z, U, tmp, c;
  # A_ipz^-1c is smallest in its C_{i-1} orbit
  z := PathRepresentative(p,i-1,ladder);
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




