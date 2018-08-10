
# Returns One(g) if no smaller element was found.
# Otherwise returns an element c s.t. A_{i+1}gc < A_{i+1}p
StroLLLightSplitOrbit := function( block, blockStack, p, k, orbAndStab, ladder )
  local g, b, i, j, l, small, preimage, perm, pos, tmp, min, orbit, c, h, z;
  # p := orbAndStab.p;
  g := block.g;
  b := block.b;
  i := block.i;
  z := orbAndStab.z[i];
  perm := Image(ladder.hom[i+1],g*b*z^-1);
  small := BlockPosition( p, i+1, orbAndStab, ladder );
  #small := orbAndStab.small[i+1];
  # if small <> orbAndStab.small[i+1] then
  #   Print("hier ist der Fehler");
  #   return 2;
  # fi;
  preimage := ladder.preimage[k][i+1];
  for l in [ 1 .. Size(preimage)] do
    pos := preimage[l]^perm;
    tmp := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
    min := tmp.min;
    orbit := tmp.orbit;
    if small < min then
      continue;
    elif small > min then
      c := BlockStabilizerCanonizingElmnt( i+1, orbit, pos, min, orbAndStab);
      return b*c;
    else
      h := ladder.splitTransversal[k][i+1][l];
      c := BlockStabilizerCanonizingElmnt( i+1, orbit, pos, min, orbAndStab);
      block := rec( g := h*g, b := b*c, i := i+1 );
      StackPush(blockStack,block);
    fi;
  od;
  return One(g); 
end;




# Several A_ig yield the same A_{i+1}g.
# StroLLLightFuseOrbit only puts exactly one of them onto the stack
StroLLLightFuseOrbit := function( block, blockStack, p, orbAndStab, ladder )
  local g, i, b, c;
  g := block.g;
  i := block.i;
  b := block.b;
  if Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
    return;
  fi;
  # prevent double processing:
  # the block is processed if and only if A_ig*z^-1*p is
  # the representative of its orbit under the action of
  # the group orbAndStab.C[i+1]
  c := CanonicalRightCosetElement(orbAndStab.C[i+1]^(b^-1),b);
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
StroLLLightFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local one, block, i, blockStack, b, isSplitStep, canonizer;
  orbAndStab.C[k] := orbAndStab.C[k-1];
  if ladder.subgroupIndex[k-1] <> ladder.subgroupIndex[k] then
    BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
    block := rec( g := p, b := ladder.one, i := 1);
    blockStack := StackCreate(100);
    StackPush( blockStack, block);
    while not StackIsEmpty(blockStack) do
      block := StackPop(blockStack);
      i := block.i;
      if i+1 = k then
        b := block.b;
        orbAndStab.C[i+1] := ClosureGroup(orbAndStab.C[i+1],b);
      else
        if ladder.isSplitStep[i+1] then
          canonizer := StroLLLightSplitOrbit(block,blockStack,p,k,orbAndStab,ladder);
          if not canonizer = ladder.one then
            return canonizer; 
          fi;
        else
          StroLLLightFuseOrbit(block,blockStack,p,orbAndStab,ladder);
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
    pos := BlockPosition( p, i, orbAndStab, ladder );
    o := BlockStabilizerOrbit( pos, i, orbAndStab, ladder );
    min := o.min;
    if min < pos then
      c := BlockStabilizerCanonizingElmnt( i, o.orbit, pos, min, orbAndStab);
      return c; 
    fi;
    transv := ladder.transversal[i];
    homAct := function(x,h)
      return PositionCanonical(transv,transv[x]*h);
    end;
    z := PathRepresentative(p,i-1,ladder);
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




