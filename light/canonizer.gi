
# Returns One(g) if no smaller element was found.
# Otherwise returns an element c s.t. A_{i+1}gc < A_{i+1}p
StroLLLightSplitOrbit := function( blockStack, k, orbAndStab, ladder )
  local block, g, b, i, z, perm, small, preimage, pos, min, orbit, c, h, l;
  block := StackPop(blockStack);
  g := block.g;
  b := block.b;
  i := block.i;
  z := orbAndStab.z[i];
  perm := Image(ladder.hom[i+1],g*b*z^-1);
  small := orbAndStab.small[i+1];
  preimage := ladder.preimage[k][i+1];
  for l in [ 1 .. Size(preimage)] do
    pos := preimage[l]^perm;
    min := orbAndStab.orbitMap[i+1][pos];
    if min <= small then
      orbit := orbAndStab.orbits[i+1][min];
      c := orbAndStab.canon[i+1][pos];
      if min = small then
        h := ladder.splitTransversal[k][i+1][l];
        block := rec( g := h*g, b := b*c, i := i+1 );
        StackPush(blockStack,block);
      else
        return b*c;
      fi;
    fi;
  od;
  return ladder.one; 
end;




# Several A_ig yield the same A_{i+1}g.
# StroLLLightFuseOrbit only puts exactly one of them onto the stack
StroLLLightFuseOrbit := function( blockStack, orbAndStab, ladder )
  local block, g, i, b, z, h, perm, small, min;
  block := StackPop(blockStack);
  g := block.g;
  i := block.i;
  b := block.b;
  if Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
    return;
  fi;
  # prevent double processing:
  # z := StroLLSmallestPathToCoset(g,i,ladder);
  z := CanonicalRightCosetElement(ladder.chain[i+1],g);
  h := orbAndStab.z[i]*b^-1*z^-1;
  perm := Image(ladder.hom[i+1],h);
  small := orbAndStab.small[i+1];
  min := Minimum(List(orbAndStab.orbits[i+1][small],x->x^perm)); 
  if min = PositionCanonical(ladder.transversal[i+1],g*z^-1) then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
  fi;
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
StroLLLightFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local coset, stack, i, b, z, canonizer;
  orbAndStab.C[k] := AsSubgroup(ladder.chain[k],orbAndStab.C[k-1]);
  if ladder.subgroupIndex[k-1] <> ladder.subgroupIndex[k] then
    BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
    coset := rec( g := p, b := ladder.one, i := 1);
    stack := StackCreate(100);
    StackPush( stack, coset);
    while not StackIsEmpty(stack) do
      coset := StackPeek(stack);
      i := coset.i;
      if i+1 = k then
        b := coset.b;
        z := orbAndStab.z[i];
        #orbAndStab.C[k] := ClosureGroup(orbAndStab.C[k],b^(z^-1));
        orbAndStab.C[k] := ClosureSubgroupNC(orbAndStab.C[k],b^(z^-1));
        StackPop(stack);
      else
        if ladder.isSplitStep[i+1] then
          canonizer := StroLLLightSplitOrbit(stack,k,orbAndStab,ladder);
          if not canonizer = ladder.one then
            return canonizer; 
          fi;
        else
          StroLLLightFuseOrbit(stack,orbAndStab,ladder);
        fi;
      fi;
    od;
  fi;
  return ladder.one;
end;


StroLLLightSplitCanonicalDCReps := function( i, p, orbAndStab, ladder) 
  local pos, min, c, transv, homAct, z, group;
  BlockStabilizerReinitialize(p,i,orbAndStab,ladder);
  pos := orbAndStab.small[i];
  min := orbAndStab.orbitMap[i][pos];
  if min < pos then
    c := orbAndStab.canon[i][pos];
    return c; 
  fi;
  transv := ladder.transversal[i];
  homAct := function(x,h)
    return PositionCanonical(transv,transv[x]*h);
  end;
  if ladder.subgroupIndex[i-1] = ladder.subgroupIndex[i] then
    orbAndStab.C[i] := AsSubgroup(ladder.chain[i],orbAndStab.C[i-1]);
    #orbAndStab.C[i] := orbAndStab.C[i-1]; 
  else
    z := orbAndStab.z[i]*orbAndStab.z[i-1]^-1;
    group := orbAndStab.C[i-1];
    group := Stabilizer(group,min,homAct)^(z^-1); 
    #group := SmallGeneratingSet(group);
    #group := AsGroup(orbAndStab.C[i]);
    #group := Subgroup(ladder.chain[i],group);
    orbAndStab.C[i] := AsSubgroup(ladder.chain[i],group);
  fi;
  return ladder.one;
end;



StroLLLightFindSmallerDCRep := function(g, k, ladder, B)
  local result, orbAndStab, p, canonizer, i;
  orbAndStab := rec();
  orbAndStab.C := [B];
  result := rec(isCanonical := false, 
                canonizer := One(g), 
                stabilizer := Group(One(g)));
  p := StroLLSmallestPathToCoset(g,k,ladder);
  for i in [ 2 .. k ] do
    if ladder.isSplitStep[i] then
      canonizer := StroLLLightSplitCanonicalDCReps(i,p,orbAndStab,ladder); 
    else
      canonizer := StroLLLightFuseCanonicalDCReps(i,p,orbAndStab,ladder);
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



StroLLLightDoubleCosets := function(k,B,ladder)
  local one, orbAndStab, cosetStack, coset, i, L, g, stab, U, V, preimage, canonizer, z, h;
  one := One(B);
  orbAndStab := rec();
  orbAndStab.C := [B];
  cosetStack := StackCreate(100);
  coset := rec(g := one, stabilizer := B, i := 1);
  StackPush(cosetStack,coset);
  L := [ [coset] ];
  for i in [ 2 .. k ] do
    L[i] := [];
  od;
  while not StackIsEmpty(cosetStack) do
    coset := StackPop(cosetStack);
    g := coset.g;
    i := coset.i+1;
    # if ladder.subgroupIndex[i-1] <= ladder.subgroupIndex[i] then
    if ladder.isSplitStep[i] then
      U := ladder.cut1toI[i];
      V := ladder.cut1toI[i-1];
      preimage := RightTransversal(V,U);
      for h in preimage do
        canonizer := StroLLLightSplitCanonicalDCReps(i,h*g,orbAndStab,ladder);
        if one = canonizer then
          z := orbAndStab.z[i];
          coset := rec(g := h*g, stabilizer := orbAndStab.C[i]^z,i := i);
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
      z := StroLLSmallestPathToCoset(g,i,ladder);
      if not g*z^-1 in ladder.chain[i-1] then
        continue;
      fi;
      # In a breadth first search algorithm the stabilizer orbAndStab.C[i-1] 
      # could have been overwritten.
      # This is a depth first search algorithm so all stabilizers 
      # besides the last one stay unchanged.
      orbAndStab.C[i-1] := coset.stabilizer^(z^-1);
      canonizer := StroLLLightFuseCanonicalDCReps(i,z,orbAndStab,ladder);
      if not one = canonizer then
        # this coset can be constructed from a smaller coset
        continue;
      fi;
      coset := rec(g := g, stabilizer := orbAndStab.C[i]^z, i := i);
      Add(L[i],coset);
      if not i = k then
        StackPush(cosetStack,coset);
      fi;
    fi; 
  od;
  return L;
end;



