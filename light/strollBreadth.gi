
# PathRepresentative := function(g,k,ladder)
DCStoreFindCanonical := function(g,k,dcTree,ladder)
  local node, c, position, z, i;
  node := dcTree;
  c := One(g);
  for i in [ 2 .. k ] do
    position := 1;
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      z := node.rep;
      position := PositionCanonical(ladder.transversal[i],g*c*z^-1);
    fi;
    node := node.child[position];
    if false = node.isCanonical then
      c := c*node.canonizingElmnt; 
      node := node.canonical;
    fi;
  od;
  return rec(rep := node, canonizingElmnt := c);
end;


# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
StroLLBreadthSplitOrbit := function( dcTree, blockQueue, p, k, orbAndStab, ladder )
  local transv, block, g, b, i, dc, z, stab, generators, gensImage, options, small, homAct, preimage, pos, tmp, min, orbit, c, child, h;
  block := QueuePopFront(blockQueue);
  dc := block.dc;
  i := block.i;
  g := block.g;
  b := block.b;
  transv := ladder.transversal[i+1];
  small := BlockPosition( p, i+1, orbAndStab, ladder );
  # preimage is a transversal of E[k][i+1]\E[k][i];
  preimage := ladder.splitTransversal[k][i+1]; 
  for h in preimage do
    pos := BlockPosition( h*g*b, i+1, orbAndStab, ladder );
    # prevent double processing
    if IsBound(dc.child[pos]) then
      continue;
    fi;
    tmp := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
    min := tmp.min;
    orbit := tmp.orbit;
    if small < min then
      # here the whole orbit is dismissed!
      for tmp in orbit do
        dc.child[tmp] := 0;
      od;
      continue;
    elif small > min then
      c := BlockStabilizerCanonizingElmnt( i+1, orbit, pos, min, orbAndStab);
      return b*c;
    else
      z := orbAndStab.z[i];
      stab := block.stab;
      homAct := function(x,h)
        x := PositionCanonical(transv,x*h);
        return transv[x];
      end;
      # create node for representative
      child := rec(child := []);
      child.canonical := child;
      dc.child[pos] := child;
      # create and append new block on the queue
      c := BlockStabilizerCanonizingElmnt( i+1, orbit, pos, min, orbAndStab);
      block := rec( g := h*g, b := b*c, i := i+1 );
      block.dc := child;
      block.stab := Stabilizer(stab^(z^-1),transv,transv[pos],homAct)^z; 
      QueuePushBack(blockQueue,block);
      # calculate orbit of old block stabilizer 
      generators := List(GeneratorsOfGroup(stab)); 
      gensImage := List(generators, x -> Image(ladder.hom[i+1],x));
      options := rec();
      options.orbsizebound := Size(transv);
      tmp := OrbitFromGenerators(pos,gensImage,options);
      orbit := tmp.orbit;
      # prevent double processing
      for tmp in orbit do
        if not pos = tmp then
          child := rec();
          child.canonizer := 
          BlockStabilizerCanElmntFromGenerators(orbit,tmp,pos,generators,dc.z); 
          child.canonical := dc.child[pos];
          dc.child[tmp] := child;
        fi;
      od;
    fi;
  od;
  Unbind(dc.stabilizer);
  return One(g); 
end;


# Several A_ig yield the same A_{i+1}g.
# StroLLBreadthFuseOrbit only puts exactly one of them onto the stack
StroLLBreadthFuseOrbit := function( dcTree, blockQueue, p, orbAndStab, ladder )
  local block, stab, rep, g, i, b, dc, child, representatives, pos, o, c, x;
  block := QueuePopFront(blockQueue);
  g := block.g;
  i := block.i;
  b := block.b;
  dc := block.dc;
  stab := block.stab;
  # if Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
  #   child := rec( stabilizer := dc.stabilizer, z := dc.z );
  #   dc.child := [child];
  #   Unbind(dc.stabilizer);
  #   block := rec( g := g, b := b, i := i+1, dc := child );
  #   QueuePushBack(blockQueue,block);
  #   return;
  # fi;
  # prevent double processing:
  # if IsBound(dc.child) then
  #   return;
  child := rec(child := []);
  dc.child := [child];
  representatives := [];
  pos := BlockPosition( g*b, i+1, orbAndStab, ladder );
  o := BlockStabilizerOrbit( pos, i+1, orbAndStab, ladder );
  for x in o.orbit do
    c := BlockStabilizerCanonizingElmnt( i+1, o.orbit, pos, x, orbAndStab);
    x := g*b*c*b^-1;
    rep := DCStoreFindCanonical(x,i,dcTree,ladder); 
    if IsIdenticalObj(dc,rep) then
      child.stabilizer := ClosureGroup(child.stabilizer,c);
    else
      x.rep.canonizingElmnt := x.canonizingElmnt^-1*b*c^-1*b^-1;
      x.rep.canonical := dc;
    fi;
  od;
  block := rec( g := g, b := b, i := i+1, dc := child );
  QueuePushBack(blockQueue,block);
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
StroLLBreadthFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local one, dcTree, block, blockQueue, i, b, isSplitStep, canonizer;
  Print("\nIn StroLLBreadthFuseCanonicalDCReps(",k,",",p,")\n");
  BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
  one := One(p);
  orbAndStab.C[k] := orbAndStab.C[k-1];
  dcTree := rec(canonizer := one, child := [] );
  dcTree.canonical := dcTree;
  block := rec( g := p, b := one, i := 1, dc := dcTree);
  block.stab := orbAndStab.C[k];
  blockQueue := QueueCreate();
  QueuePushBack(blockQueue, block);
  while not QueueEmpty(blockQueue) do
    block := QueueFront(blockQueue);
    i := block.i;
    if i+1 = k then
      QueuePopFront(blockQueue);
      b := block.b;
      orbAndStab.C[k] := ClosureGroup(orbAndStab.C[k],b);
    else
      isSplitStep := ladder.subgroupIndex[i] < ladder.subgroupIndex[i+1];
      if isSplitStep then
        canonizer := StroLLBreadthSplitOrbit(dcTree,blockQueue,p,k,orbAndStab,ladder);
        if not canonizer = one then
          return canonizer; 
        fi;
      else StroLLBreadthFuseOrbit(dcTree,blockQueue,p,orbAndStab,ladder);
      fi;
    fi;
  od;
  return one;
end;



StroLLBreadthSplitCanonicalDCReps := function( i, p, orbAndStab, ladder) 
  local pos, o, min, c, homAct, z, tmp;
  BlockStabilizerReinitialize(p,i,orbAndStab,ladder);
  pos := BlockPosition( p, i, orbAndStab, ladder );
  o := BlockStabilizerOrbit( pos, i, orbAndStab, ladder );
  min := o.min;
  if min < pos then
    c := BlockStabilizerCanonizingElmnt( i, o.orbit, pos, min, orbAndStab);
    return c; 
  fi;
  Print("\nIn StroLLBreadthSplitCanonicalDCReps(",i,",",p,")\n");
  homAct := function(x,h)
    x := PositionCanonical(ladder.transversal[i],x*h);
    return ladder.transversal[i][x];
  end;
  z := PathRepresentative(p,i-1,ladder);
  tmp := Stabilizer(orbAndStab.C[i-1]^(z^-1),ladder.transversal[i],ladder.transversal[i][min],homAct); 
  orbAndStab.C[i] := tmp^z; 
  Print("Stabilisator zu A[",i,"]",p," ist ",orbAndStab.C[i],"\n");
  return One(p);
end;


