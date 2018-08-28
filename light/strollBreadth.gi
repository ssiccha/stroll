
# PathRepresentative := function(g,k,ladder)
StroLLBreadthFindCanonicalNode := function(g,k,tree,ladder)
  local node, c, pos, z, i;
  node := tree;
  c := ladder.one;
  for i in [ 2 .. k ] do
    if ladder.isSplitStep[i] then
      z := node.g;
      pos := PositionCanonical(ladder.transversal[i],g*c*z^-1);
      node := node.child[pos];
    else
      node := node.child;
    fi;
    if IsBound(node.canonizer) then
      c := c*node.canonizer; 
      node := node.canonical;
    fi;
    if not g*c*node.g^-1 in ladder.chain[i] then
      Error("\nDa liegt das Haustier begraben\n");
    fi;
  od;
  return rec(canonical := node, canonizer := c);
end;


StroLLPrintStab := function(stab,i,g)
  local pos1, pos2, orbit;
  if i = 1 then
    pos1 := 1; 
  elif i = 2 then
    pos1 := 2;
  elif i mod 2 = 0 then
    pos1 := i/2;
    pos2 := i/2+1;
  else
    pos1 := (i-1)/2;
    pos2 := (i+3)/2;
  fi;
  orbit := Orbit(stab,pos1);
  Print("\tOrbits: ",List(orbit,x -> x^g),"\c");
  if IsBound(pos2) then
    orbit := Orbit(stab,pos2);
    Print("\t",List(orbit,x -> x^g),"\c");
  else
    Print("\t");
  fi;
  Print("\t|G| = ",Size(stab)); 
  Print("\t",stab^g,"\c");
end;


StroLLPrint := function(omega)
  local group, g, b, i, delta, t;
  if not IsBound(omega.i) then
    Error("Omega has no i\n");
  fi;
  if not IsBound(omega.g) then
    Error("Omega has no g\n");
  fi;
  if not IsBound(omega.b) then
    Error("Omega has no b\n");
  fi;
  if not IsBound(omega.stabilizer) then
    Print("kein Stabilizer\n");
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
  if i = 1 then
    Print("\t");
  fi;
  Print("omega^b\t:= ",List(delta,x -> x^(g*b)),"\t\c"); 
  if i = 1 then
    Print("\t");
  fi;
  if IsBound(omega.stabilizer) then
    StroLLPrintStab(omega.stabilizer,i,g); 
  fi;
end;








# Returns One(g) if no smaller element was found.
# Otherwise returns a c s.t. A_{i+1}gc < A_{i+1}p
StroLLBreadthSplitOrbit := function( queue, p, k, orbAndStab, ladder )
  local coset, g, b, i, z, perm, small, preimage, child, pos2, pos1, min, orbit, c, h, stab, gens, acts, tmp, l, o;
  coset := QueuePopFront(queue);
  g := coset.g;
  b := coset.b;
  i := coset.i;
  z := orbAndStab.z[i];
  perm := Image(ladder.hom[i+1],g*b*z^-1);
  small := orbAndStab.small[i+1];
  preimage := ladder.preimage[k][i+1];
  child := [];
  coset.child := child;
  stab := coset.stabilizer;
  gens := GeneratorsOfGroup(stab); 
  acts := List(gens,x -> Image(ladder.hom[i+1],x));
  for l in [ 1 .. Size(preimage)] do
    pos2 := preimage[l];
    pos1 := pos2^perm;
    min := orbAndStab.orbitMap[i+1][pos1];
    if min <= small and not IsBound(child[pos2]) then
      c := orbAndStab.canon[i+1][pos1];
      if min < small then
        return b*c;
      # elif Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
      #   child[pos2] := rec( g := g, b := b, i := i+1 );
      #   child[pos2].stabilizer := coset.stabilizer;
      else
        h := ladder.splitTransversal[k][i+1][l];
        child[pos2] := rec( g := h*g, b := b*c, i := i+1 );
        tmp := OrbitStabilizer(stab,pos2,gens,acts,OnPoints);
        child[pos2].stabilizer := tmp.stabilizer^(h^-1);
        for o in tmp.orbit do
          if o <> pos2 then
            c := RepresentativeAction(stab,o,pos2,gens,acts,OnPoints)^g;
            child[o] := rec(canonizer := c, canonical := child[pos2]);
          fi;
        od;
        QueuePushBack(queue,child[pos2]);
      fi;
    fi;
  od;
  return ladder.one; 
end;


# Several A_ig yield the same A_{i+1}g.
# StroLLBreadthFuseOrbit only puts exactly one of them onto the stack
StroLLBreadthFuseOrbit := function( tree, queue, p, orbAndStab, ladder )
  local coset, g, b, i, stabilizer, pos, min, orbit, c, tmp, node, x;
  coset := QueuePopFront(queue);
  # prevent double processing:
  if IsBound(coset.child) then
    return;
  fi;
  g := coset.g;
  b := coset.b;
  i := coset.i;
  coset.child := rec(g := g, b := b, i := i+1);
  stabilizer := AsSubgroup(ladder.chain[i+1],coset.stabilizer);
  if Size(orbAndStab.C[i]) <> Size(orbAndStab.C[i+1]) then
    pos := orbAndStab.small[i+1]; 
    min := orbAndStab.orbitMap[i+1][pos];
    orbit := orbAndStab.orbits[i+1][min];
    for x in orbit do
      if x <> min then
        c := orbAndStab.canon[i+1][x];
        tmp := StroLLBreadthFindCanonicalNode(p*c^-1*b^-1,i,tree,ladder); 
        node := tmp.canonical;
        c := tmp.canonizer;
        if IsIdenticalObj(node,coset) then
          stabilizer := ClosureSubgroupNC(stabilizer,c^(g^-1));
        elif not IsBound(node.child) then
          node.child := rec();
          node.child.canonical := coset.child;
          node.child.canonizer := c^-1;
        fi;
      fi;
    od;
  fi;
  coset.child.stabilizer := stabilizer;
  QueuePushBack(queue,coset.child);
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
StroLLBreadthFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local coset, queue, tree, i, b, z, canonizer;
  if ladder.isSplitStep[k] then
    Error("\nThis function must not be used for splitting steps!\n");
  fi;
  orbAndStab.C[k] := AsSubgroup(ladder.chain[k],orbAndStab.C[k-1]);
  BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
  coset := rec( g := p, b := ladder.one, i := 1);
  coset.stabilizer := orbAndStab.C[k];
  queue := QueueCreate();
  QueuePushBack(queue, coset);
  tree := coset;
  z := orbAndStab.z[k-1];
  while not QueueEmpty(queue) do
    i := QueueFront(queue).i;
    if i+1 = k then
      b := QueuePopFront(queue).b;
      orbAndStab.C[k] := ClosureSubgroupNC(orbAndStab.C[k],b^(z^-1));
    elif ladder.isSplitStep[i+1] then
      canonizer := StroLLBreadthSplitOrbit(queue,p,k,orbAndStab,ladder);
      if not canonizer = ladder.one then
        return canonizer; 
      fi;
    else 
      StroLLBreadthFuseOrbit(tree,queue,p,orbAndStab,ladder);
    fi;
  od;
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
            Error("\nThe Stabilizer is wrong(4)"); 
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
      #Print("\n\nRufe jetzt StroLLBreadthFuseCanonicalDCReps ",i);
      canonizer := StroLLBreadthFuseCanonicalDCReps(i,z,orbAndStab,ladder);
      if not one = canonizer then
        # this coset can be constructed from a smaller coset
        continue;
      fi;
      if not IsSubset(ladder.chain[i],orbAndStab.C[i]) then
        Error("\nThe Stabilizer is wrong(5)"); 
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


