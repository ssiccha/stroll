
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

StroLLPrint := function(omega)
  local g, b, i, delta, t;
  if not IsBound(omega.i) then
    Error("Omega has no i\n");
  fi;
  if not IsBound(omega.g) then
    Error("Omega has no g\n");
  fi;
  if not IsBound(omega.b) then
    Error("Omega has no b\n");
  fi;
  g := omega.g;
  b := omega.b;
  i := omega.i;
  if i = 1 then
    delta := [];
  elif i = 2 then
    delta := [1];
  elif i mod 2 = 0 then
    delta := [1 .. i/2];
  else
    delta := [1 .. (i+1)/2];
  fi;
  Print("omega\t:= ",List(delta,x -> x^g),"\t"); 
  Print("omega^b\t:= ",List(delta,x -> x^(g*b)),"\t"); 
  # if IsBound(omega.child) then
  #   for i in [ 1 .. Size(omega.child) ] do
  #     if IsBound(omega.child[i]) then
  #       Print("child[",i,"] ");
  #     fi; 
  #   od;
  # fi;
end;





# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
StroLLBreadthSplitOrbit := function( queue, p, k, orbAndStab, ladder )
  local omega, g, b, i, z, perm, small, preimage, child, pos, min, orbit, c, h, stab, gens, acts, tmp, l, o;
  omega := QueuePopFront(queue);
  g := omega.g;
  b := omega.b;
  i := omega.i;
  z := orbAndStab.z[i];
  perm := Image(ladder.hom[i+1],g*b*z^-1);
  small := orbAndStab.small[i+1];
  preimage := ladder.preimage[k][i+1];
  child := [];
  omega.child := child;
  omega.representative := z*b^-1;
  Print("\n\nIn StroLLBreadthSplitOrbit:");
  Print("\n\t              \t");
  StroLLPrint(omega);
  for l in [ 1 .. Size(preimage)] do
    pos := preimage[l]^perm;
    min := orbAndStab.orbitMap[i+1][pos];
    if min <= small then
      orbit := orbAndStab.orbits[i+1][min];
      c := orbAndStab.canon[i+1][pos];
      if min = small then
        h := ladder.splitTransversal[k][i+1][l];
        child[pos] := rec( g := h*g, b := b*c, i := i+1 );
        stab := omega.stabilizer;
        gens := GeneratorsOfGroup(stab); 
        acts := List(gens,x -> Image(ladder.hom[i+1],x));
        tmp := OrbitStabilizer(stab,pos,gens,acts,OnPoints);
        for o in tmp.orbit do
          if o <> pos then
            c := RepresentativeAction(stab,o,pos,gens,acts,OnPoints);
            child[o] := rec(canonizer := c);
          fi;
        od;
        min := ladder.representativeMap[i+1][pos];
        c := ladder.pathTransversal[i+1][min];
        child[pos].stabilizer := tmp.stabilizer^(c^-1);
        QueuePushBack(queue,child[pos]);
        Print("\n\tQueuePushBack:\t");
        StroLLPrint(child[pos]);
      else
        return b*c;
      fi;
    fi;
  od;
  Unbind(omega.stabilizer);
  Unbind(omega.g);
  Unbind(omega.b);
  Unbind(omega.i);
  return ladder.one; 
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
  local one, tree, coset, queue, i, b, canonizer;
  orbAndStab.C[k] := AsSubgroup(ladder.chain[k],orbAndStab.C[k-1]);
  if ladder.subgroupIndex[k-1] <> ladder.subgroupIndex[k] then
    BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
    coset := rec( g := p, b := ladder.one, i := 1);
    queue := QueueCreate();
    coset.stabilizer := orbAndStab.C[k];
    QueuePushBack(queue, coset);
    Print("\n\n####################################\n\n");
    Print("\n\nIn StroLLBreadthFuseCanonicalDCReps:");
    Print("\n\t              \t");
    StroLLPrint(rec(g := p, b := ladder.one, i := k));

    while not QueueEmpty(queue) do
      coset := QueueFront(queue);
      i := coset.i;
      if i+1 = k then
        b := coset.b;
        z := orbAndStab.z[i];
        #orbAndStab.C[k] := ClosureGroup(orbAndStab.C[k],b^(z^-1));
        orbAndStab.C[k] := ClosureSubgroupNC(orbAndStab.C[k],b^(z^-1));
        QueuePopFront(queue);
      else
        if ladder.isSplitStep[i+1] then
          if not IsSubset(ladder.chain[i],orbAndStab.C[i]) then
            Error("\nThe Stabilizer is wrong(3)"); 
          fi;
          canonizer := StroLLBreadthSplitOrbit(queue,p,k,orbAndStab,ladder);
          if not canonizer = ladder.one then
            return canonizer; 
          fi;
        else 
          if not IsSubset(ladder.chain[i],orbAndStab.C[i]) then
            Error("\nThe Stabilizer is wrong(4)"); 
          fi;
          StroLLBreadthFuseOrbit(tree,queue,p,orbAndStab,ladder);
        fi;
      fi;
    od;
  fi;
  return ladder.one;
end;



StroLLBreadthSplitCanonicalDCReps := function( i, p, orbAndStab, ladder) 
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


StroLLBreadthDoubleCosets := function(k,B,ladder)
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
    if ladder.isSplitStep[i] then
      U := ladder.cut1toI[i];
      V := ladder.cut1toI[i-1];
      preimage := RightTransversal(V,U);
      for h in preimage do
        canonizer := StroLLBreadthSplitCanonicalDCReps(i,h*g,orbAndStab,ladder);
        if one = canonizer then
          if not IsSubset(ladder.chain[i],orbAndStab.C[i]) then
            Error("\nThe Stabilizer is wrong(1)"); 
          fi;
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
      Print("Rufe jetzt StroLLBreadthFuseCanonicalDCReps ",i);
      canonizer := StroLLBreadthFuseCanonicalDCReps(i,z,orbAndStab,ladder);
      if not one = canonizer then
        # this coset can be constructed from a smaller coset
        continue;
      fi;
      if not IsSubset(ladder.chain[i],orbAndStab.C[i]) then
        Error("\nThe Stabilizer is wrong(2)"); 
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


