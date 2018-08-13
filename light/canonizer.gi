
# Returns One(g) if no smaller element was found.
# Otherwise returns an element c s.t. A_{i+1}gc < A_{i+1}p
StroLLLightSplitOrbit := function( blockStack, k, orbAndStab, ladder )
  local g, b, i, z, perm, small, preimage, pos, min, orbit, c, h, l;
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
      elif min < small then
        return b*c;
      fi;
    fi;
  od;
  return ladder.one; 
end;




# Several A_ig yield the same A_{i+1}g.
# StroLLLightFuseOrbit only puts exactly one of them onto the stack
StroLLLightFuseOrbit := function( blockStack, orbAndStab, ladder )
  local g, i, b, z, h, perm, small, min;
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
  local one, block, i, blockStack, b, isSplitStep, canonizer;
  orbAndStab.C[k] := orbAndStab.C[k-1];
  if ladder.subgroupIndex[k-1] <> ladder.subgroupIndex[k] then
    BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
    block := rec( g := p, b := ladder.one, i := 1);
    blockStack := StackCreate(100);
    StackPush( blockStack, block);
    while not StackIsEmpty(blockStack) do
      block := StackPeek(blockStack);
      i := block.i;
      if i+1 = k then
        b := block.b;
        orbAndStab.C[i+1] := ClosureGroup(orbAndStab.C[i+1],b);
        block := StackPop(blockStack);
      else
        if ladder.isSplitStep[i+1] then
          canonizer := StroLLLightSplitOrbit(blockStack,k,orbAndStab,ladder);
          if not canonizer = ladder.one then
            return canonizer; 
          fi;
        else
          StroLLLightFuseOrbit(blockStack,orbAndStab,ladder);
        fi;
      fi;
    od;
  fi;
  return ladder.one;
end;


StroLLLightSplitCanonicalDCReps := function( i, p, orbAndStab, ladder) 
  local pos, o, min, c, homAct, z, group, transv, tmp;
  if ladder.subgroupIndex[i-1] = ladder.subgroupIndex[i] then
    orbAndStab.C[i] := orbAndStab.C[i-1]; 
  else
    BlockStabilizerReinitialize(p,i,orbAndStab,ladder);
    #pos := BlockPosition( p, i, orbAndStab, ladder );
    #pos := PositionCanonical(ladder.transversal[i],p*orbAndStab.z[i-1]^-1);
    pos := orbAndStab.small[i];
    #o := BlockStabilizerOrbit( pos, i, orbAndStab, ladder );
    min := orbAndStab.orbitMap[i][pos];
    #min := o.min;
    if min < pos then
      #c := BlockStabilizerCanonizingElmnt( i, o.orbit, pos, min, orbAndStab);
      c := orbAndStab.canon[i][pos];
      return c; 
    fi;
    transv := ladder.transversal[i];
    homAct := function(x,h)
      return PositionCanonical(transv,transv[x]*h);
    end;
    #z := PathRepresentative(p,i-1,ladder);
    z := orbAndStab.z[i-1];
    group := orbAndStab.C[i-1]^(z^-1);
    orbAndStab.C[i] := Stabilizer(group,min,homAct)^z; 
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




