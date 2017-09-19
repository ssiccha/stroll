





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
SmallestStrongPathToCoset := function( g, k, ladder )
  local z, position, preimage, tmp, hsmall, canonical, i, h;
  z := One(ladder.G);
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      position := Size(ladder.transversal[i]) + 1;
      preimage := ladder.splitTransversal[k][i]; 
      for h in preimage do
        # perm := Image(ladder.hom[i],h*g);
        # tmp := 1^perm;
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






# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
SplitOrbit := function( block, blockStack, p, k, orbAndStab, ladder )
  local g, b, i, small, preimage, pos, orbitInfo, min, c, h;
  # p := orbAndStab.p;
  g := block.g;
  b := block.b;
  i := block.i;
  small := BlockStabilizerPosition( p, i+1, orbAndStab, ladder );
  # preimage is a transversal of E[k][i+1]\E[k][i];
  preimage := ladder.splitTransversal[k][i+1]; 
  for h in preimage do
    pos := BlockStabilizerPosition( h*g*b, i+1, orbAndStab, ladder );
    orbitInfo := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
    min := orbitInfo.min;
    if small < min then
      continue;
    fi;
    c := BlockStabilizerCanonizingElmnt( i+1, orbitInfo.orbit, pos, min, orbAndStab);
    if small > min then
      return b*c;
    else
      block := rec( g := h*g, b := b*c, i := i+1 );
      StackPush(blockStack,block);
    fi;
  od;
  return One(g); 
end;




# Several A_ig yield the same A_{i+1}g.
# FuseOrbit only puts exactly one of them onto the stack
FuseOrbit := function( block, blockStack, p, orbAndStab, ladder )
  local g, i, b, c;
  # p := orbAndStab.p;
  g := block.g;
  i := block.i;
  b := block.b;
  if Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
    block.i := i+1; 
    StackPush(blockStack,block);
    return;
  fi;
  # prevent double processing:
  # the block is processed if and only if A_ig*z^-1*p is
  # the representative of its orbit under the action of
  # the group orbAndStab.C[i+1]
  c := CanonicalRightCosetElement(orbAndStab.C[i+1]^(b^-1),b);
  if g*c*p^-1 in ladder.chain[i] then
    block.i := i+1; 
    StackPush(blockStack,block);
  fi;
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
CheckSmallestInDoubleCosetFuse := function( k, p, orbAndStab, ladder)
  local one, block, i, blockStack, b, isSplitStep, canonizer;
  ReinitializeOrbitAndStabilizerStorage(p,k-1,orbAndStab, ladder);
  one := One(p);
  orbAndStab.C[k] := orbAndStab.C[k-1];
  block := rec( g := p, b := One(p), i := 1);
  blockStack := StackCreate(100);
  StackPush( blockStack, block);
  while not StackIsEmpty(blockStack) do
    block := StackPop(blockStack);
    i := block.i;
    b := block.b;
    if i+1 = k then
      orbAndStab.C[i+1] := ClosureGroup(orbAndStab.C[i+1],b);
    else
      isSplitStep := ladder.subgroupIndex[i] < ladder.subgroupIndex[i+1];
      if isSplitStep then
        canonizer := SplitOrbit(block,blockStack,p,k,orbAndStab,ladder);
        if not canonizer = one then
          return canonizer; 
        fi;
      else
        FuseOrbit(block,blockStack,p,orbAndStab,ladder);
      fi;
    fi;
  od;
  return One(p);
end;



CheckSmallestInDoubleCosetSplit := function( i, p, orbAndStab, ladder) 
  local z, U, tmp, c;
  # ReinitializeOrbitAndStabilizerStorage(p,i-1,orbAndStab,ladder);
  # A_ipz^-1c is smallest in its C_{i-1} orbit
  z := PathRepresentative(p,i-1,ladder);
  U := ConjugateGroup(orbAndStab.C[i-1],z^-1);
  tmp := FindOrbitRep( p*z^-1, i, U, ladder );
  c := tmp.canonizer;
  # A_ipz^-1 = A_ipz^-1c
  if not (p*z^-1*c)*(p*z^-1)^-1 in ladder.chain[i] then
    return c^z;
  fi;
  orbAndStab.C[i] := ConjugateGroup(tmp.stabilizer,z);
  return One(p);
end;



FindSmallerOrbitRepresentative := function(g, k, ladder, B)
  local result, orbAndStab, p, canonizer, i;
  orbAndStab := rec();
  orbAndStab.C := [B];
  result := rec(isCanonical := false, 
                canonizer := One(g), 
                stabilizer := Group(One(g)));
  p := SmallestStrongPathToCoset(g,k,ladder);
  for i in [ 2 .. k ] do
    if  ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i]  then
      canonizer := CheckSmallestInDoubleCosetSplit(i,p,orbAndStab,ladder); 
    else
      canonizer := CheckSmallestInDoubleCosetFuse(i,p,orbAndStab,ladder);
    fi;
    if not canonizer = One(canonizer) then
      result.canonizer := canonizer;
      return result; 
    fi;
  od;
  result.isCanonical := true;
  result.stabilizer := orbAndStab.C[k];
  return result;
end;




