





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
StroLLSmallestPathToCoset := function( g, k, ladder )
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
StroLLBreadthSplitOrbit := function( dcTree, blockQueue, p, k, orbAndStab, ladder )
  local block, dc, options, generators, gensImage, g, b, i, small, homAct, preimage, pos, tmp, min, c, child, z, orbit, h;
  # p := orbAndStab.p;
  block := QueuePopFront(blockQueue);
  dc := block.dc;
  options := rec();
  options.orbsizebound := Size(ladder.transversal[i+1]);
  generators := List(GeneratorsOfGroup(dc.stabilizer)); 
  gensImage := List(generators, x -> Image(ladder.hom[i+1],x));
  g := block.g;
  b := block.b;
  i := block.i;
  small := BlockStabilizerPosition( p, i+1, orbAndStab, ladder );
  homAct := function(x,h)
    x := PositionCanonical(ladder.transversal[i+1],x*h);
    return ladder.transversal[i+1][x];
  end;
  # preimage is a transversal of E[k][i+1]\E[k][i];
  preimage := ladder.splitTransversal[k][i+1]; 
  for h in preimage do
    pos := BlockStabilizerPosition( h*g*b, i+1, orbAndStab, ladder );
    # prevent double processing
    if IsBound(dc.child[pos]) then
      continue;
    fi;
    tmp := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
    min := tmp.min;
    if small < min then
      continue;
    elif small > min then
      c := BlockStabilizerCanonizingElmnt( i+1, tmp.orbit, pos, min, orbAndStab);
      return b*c;
    else
      child := rec();
      c := BlockStabilizerCanonizingElmnt( i+1, tmp.orbit, pos, min, orbAndStab);
      tmp := BlockStabilizerOrbitFromGenerators(pos,gensImage,options);
      min := tmp.min;
      z := dc.z*ladder.transversal[min];
      child.stabilizer := 
      Stabilizer(dc.stabilizer^(z^-1),ladder.transversal[i+1],ladder.transversal[i+1][min],homAct); 
      child.isCanonical := true; 
      child.z := dc.z*ladder.transversal[i+1][min]; 
      block := rec( g := h*g, b := b*c, i := i+1, dc := child );
      QueuePushBack(blockQueue,block);
      # prevent double processing
      orbit := tmp.orbit;
      for pos in orbit do
        if not min = pos then
          child := rec();
          child.isCanonical := false; 
          child.canonizingElmnt := 
          BlockStabilizerCanElmntFromGenerators(orbit,pos,min,generators,dc.z); 
          child.canonical := dc.child[min];
          dc.child[pos] := child;
        fi;
      od;
    fi;
  od;
  Unbind(dc.stabilizer);
  return One(g); 
end;



# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
StroLLLightSplitOrbit := function( block, blockStack, p, k, orbAndStab, ladder )
  local g, b, i, small, preimage, pos, o, min, c, h;
  # p := orbAndStab.p;
  g := block.g;
  b := block.b;
  i := block.i;
  small := BlockStabilizerPosition( p, i+1, orbAndStab, ladder );
  # preimage is a transversal of E[k][i+1]\E[k][i];
  preimage := ladder.splitTransversal[k][i+1]; 
  for h in preimage do
    pos := BlockStabilizerPosition( h*g*b, i+1, orbAndStab, ladder );
    o := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
    min := o.min;
    if small < min then
      continue;
    elif small > min then
      c := BlockStabilizerCanonizingElmnt( i+1, o.orbit, pos, min, orbAndStab);
      return b*c;
    else
      c := BlockStabilizerCanonizingElmnt( i+1, o.orbit, pos, min, orbAndStab);
      block := rec( g := h*g, b := b*c, i := i+1 );
      StackPush(blockStack,block);
    fi;
  od;
  return One(g); 
end;



# Several A_ig yield the same A_{i+1}g.
# StroLLBreadthFuseOrbit only puts exactly one of them onto the stack
StroLLBreadthFuseOrbit := function( dcTree, blockQueue, p, orbAndStab, ladder )
  local block, g, i, b, dc, child, representatives, pos, o, c, x;
  block := QueuePopFront(blockQueue);
  g := block.g;
  i := block.i;
  b := block.b;
  dc := block.dc;
  if Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
    child := rec( isCanonical := true, stabilizer := dc.stabilizer, z := dc.z );
    dc.child := [child];
    Unbind(dc.stabilizer);
    block := rec( g := g, b := b, i := i+1, dc := child );
    QueuePushBack(blockQueue,block);
    return;
  fi;
  # prevent double processing:
  if IsBound(dc.child) then
    return;
  else
    child := rec( isCanonical := true, stabilizer := dc.stabilizer, z := dc.z );
    dc.child := [child];
    representatives := [];
    pos := BlockStabilizerPosition( g*b, i+1, orbAndStab, ladder );
    o := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
    for x in o.orbit do
      c := BlockStabilizerCanonizingElmnt( i+1, o.orbit, pos, x, orbAndStab);
      x := g*b*c*b^-1;
      x := DCStoreFindCanonical(x,i,dcTree,ladder); 
      Unbind(x.rep.stabilizer);
      if IsIdenticalObj(dc,x.rep) then
        child.stabilizer := ClosureGroup(child.stabilizer,c);
      else
        x.rep.isCanonical := false;
        x.rep.canonizingElmnt := x.canonizingElmnt^-1*b*c^-1*b^-1;
        x.rep.canonical := dc;
      fi;
    od;
    block := rec( g := g, b := b, i := i+1, dc := child );
    QueuePushBack(blockQueue,block);
  fi;
end;



# Several A_ig yield the same A_{i+1}g.
# StroLLLightFuseOrbit only puts exactly one of them onto the stack
StroLLLightFuseOrbit := function( block, blockStack, p, orbAndStab, ladder )
  local g, i, b, c;
  # p := orbAndStab.p;
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
StroLLBreadthFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local one, dcTree, block, blockQueue, i, b, isSplitStep, canonizer;
  BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
  one := One(p);
  orbAndStab.C[k] := orbAndStab.C[k-1];
  dcTree := rec( isCanonical := true, stabilizer := orbAndStab.C[k], z := one );
  block := rec( g := p, b := one, i := 1, dc := dcTree);
  blockQueue := QueueCreate();
  QueuePushBack(blockQueue, block);
  while not QueueEmpty(blockQueue) do
    block := QueueFront(blockQueue);
    i := block.i;
    b := block.b;
    if i+1 = k then
      orbAndStab.C[i+1] := ClosureGroup(orbAndStab.C[i+1],b);
      QueuePopFront(blockQueue);
    else
      isSplitStep := ladder.subgroupIndex[i] < ladder.subgroupIndex[i+1];
      if isSplitStep then
        canonizer := StroLLBreadthSplitOrbit(dcTree,blockQueue,p,k,orbAndStab,ladder);
        if not canonizer = one then
          return canonizer; 
        fi;
      else
        StroLLBreadthFuseOrbit(dcTree,blockQueue,p,orbAndStab,ladder);
      fi;
    fi;
  od;
  return one;
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
StroLLLightFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local one, block, i, blockStack, b, isSplitStep, canonizer;
  BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
  one := One(p);
  orbAndStab.C[k] := orbAndStab.C[k-1];
  block := rec( g := p, b := one, i := 1);
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
        canonizer := StroLLLightSplitOrbit(block,blockStack,p,k,orbAndStab,ladder);
        if not canonizer = one then
          return canonizer; 
        fi;
      else
        StroLLLightFuseOrbit(block,blockStack,p,orbAndStab,ladder);
      fi;
    fi;
  od;
  return one;
end;


StroLLBreadthSplitCanonicalDCReps := function( i, p, orbAndStab, ladder) 
  local pos, o, min, c, homAct, z, tmp;
  BlockStabilizerReinitialize(p,i,orbAndStab,ladder);
  pos := BlockStabilizerPosition( p, i, orbAndStab, ladder );
  o := BlockStabilizerOrbit( pos, i, orbAndStab, ladder );
  min := o.min;
  c := BlockStabilizerCanonizingElmnt( i, o.orbit, pos, min, orbAndStab);
  if min < pos then
    return c; 
  fi;
    homAct := function(x,h)
      x := PositionCanonical(ladder.transversal[i],x*h);
      return ladder.transversal[i][x];
    end;
  z := PathRepresentative(p,i-1,ladder);
  tmp := Stabilizer(orbAndStab.C[i-1]^(z^-1),ladder.transversal[i],ladder.transversal[i][min],homAct); 
  orbAndStab.C[i] := tmp^z; 
  return One(p);
end;



StroLLLightSplitCanonicalDCReps := function( i, p, orbAndStab, ladder) 
  local pos, o, min, c, homAct, z, tmp;
  BlockStabilizerReinitialize(p,i,orbAndStab,ladder);
  pos := BlockStabilizerPosition( p, i, orbAndStab, ladder );
  o := BlockStabilizerOrbit( pos, i, orbAndStab, ladder );
  min := o.min;
  c := BlockStabilizerCanonizingElmnt( i, o.orbit, pos, min, orbAndStab);
  if min < pos then
    return c; 
  fi;
    homAct := function(x,h)
      x := PositionCanonical(ladder.transversal[i],x*h);
      return ladder.transversal[i][x];
    end;
  z := PathRepresentative(p,i-1,ladder);
  tmp := Stabilizer(orbAndStab.C[i-1]^(z^-1),ladder.transversal[i],ladder.transversal[i][min],homAct); 
  orbAndStab.C[i] := tmp^z; 
  return One(p);
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
    if  ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i]  then
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




