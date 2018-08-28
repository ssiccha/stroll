
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
  Print("\n\nIn StroLLBreadthSplitOrbit:");
  Print("\n\t              \t");
  StroLLPrint(coset);
  for l in [ 1 .. Size(preimage)] do
    pos2 := preimage[l];
    pos1 := pos2^perm;
    if IsBound(child[pos2]) then
      continue; 
    fi;
    min := orbAndStab.orbitMap[i+1][pos1];
    if min <= small then
      orbit := orbAndStab.orbits[i+1][min];
      c := orbAndStab.canon[i+1][pos1];
      if min = small then
        h := ladder.splitTransversal[k][i+1][l];
        if pos2 <> PositionCanonical(ladder.transversal[i+1],h) then
          Error("\nWarum geht das nicht?\n"); 
        fi;
        child[pos2] := rec( g := h*g, b := b*c, i := i+1 );
        stab := coset.stabilizer;
        gens := GeneratorsOfGroup(stab); 
        acts := List(gens,x -> Image(ladder.hom[i+1],x));
        tmp := OrbitStabilizer(stab,pos2,gens,acts,OnPoints);
        child[pos2].stabilizer := tmp.stabilizer^(h^-1);
        for o in tmp.orbit do
          if o <> pos2 then
            c := RepresentativeAction(stab,o,pos2,gens,acts,OnPoints)^g;
            if not c in orbAndStab.C[1] then
              Error("\nDas darf doch nicht sein!\n");
            fi;
            child[o] := rec(canonizer := c, canonical := child[pos2]);
          fi;
        od;
        QueuePushBack(queue,child[pos2]);
        Print("\n\tQueuePushBack:\t");
        StroLLPrint(child[pos2]);
      else
        return b*c;
      fi;
    fi;
  od;
  #Unbind(coset.stabilizer);
  #Unbind(coset.b);
  #Unbind(coset.i);
  return ladder.one; 
end;


# Several A_ig yield the same A_{i+1}g.
# StroLLBreadthFuseOrbit only puts exactly one of them onto the stack
StroLLBreadthFuseOrbit := function( tree, queue, p, orbAndStab, ladder )
  local coset, g, b, i, z, stabilizer, pos, min, orbit, c, tmp, node, x;
  coset := QueuePopFront(queue);
  # prevent double processing:
  if IsBound(coset.child) then
    return;
  fi;
  Print("\n\nIn StroLLBreadthSplitOrbit:");
  Print("\n\t              \t");
  StroLLPrint(coset);
  g := coset.g;
  b := coset.b;
  i := coset.i;
  z := orbAndStab.z[i];
  coset.child := rec(g := g, b := b, i := i+1);
  stabilizer := AsSubgroup(ladder.chain[i+1],coset.stabilizer);
  # if Size(orbAndStab.C[i]) = Size(orbAndStab.C[i+1]) then
  #   child := rec( stabilizer := dc.stabilizer, z := dc.z );
  #   dc.child := [child];
  #   Unbind(dc.stabilizer);
  #   coset := rec( g := g, b := b, i := i+1, dc := child );
  #   QueuePushBack(queue,coset);
  #   return;
  # fi;
  pos := orbAndStab.small[i+1]; 
  min := orbAndStab.orbitMap[i+1][pos];
  orbit := orbAndStab.orbits[i+1][min];
  if Size(orbAndStab.C[i+1])/Size(orbAndStab.C[i]) <> Size(orbit) then
    Error("\nDas kann gar nicht sein!(1)\n"); 
  fi;
  for x in orbit do
    c := orbAndStab.canon[i+1][x];
    if min <> pos then
      Error("\ndieser Fall kommt tatsächlich vor!\n");
      c := c*orbAndStab.canon[i+1][pos]^-1;
    fi;
    # c := c^z;
    if not c in orbAndStab.C[1] then
      Error("\nDas kann doch nicht sein!(2)\n");
    fi;
    tmp := StroLLBreadthFindCanonicalNode(p*c^-1*b^-1,i,tree,ladder); 
    node := tmp.canonical;
    c := tmp.canonizer;
    if not c in orbAndStab.C[1] then
      Error("\nDas kann doch nicht sein!(3)\n");
    fi;
    if IsIdenticalObj(node,coset) then
      if not g*c*g^-1 in ladder.chain[i+1] then
        Error("\nFehler in StroLLBreadthFuseOrbit\n"); 
      fi;
      stabilizer := ClosureSubgroupNC(stabilizer,c^(g^-1));
    elif not IsBound(node.child) then
      node.child := rec();
      node.child.canonical := coset.child;
      node.child.canonizer := c^-1;
    fi;
  od;
  #Unbind(coset.stabilizer);
  #Unbind(coset.b);
  #Unbind(coset.i);
  coset.child.stabilizer := stabilizer;
  QueuePushBack(queue,coset.child);
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
StroLLBreadthFuseCanonicalDCReps := function( k, p, orbAndStab, ladder)
  local coset, queue, tree, intersection, i, g, b, z, canonizer;
  orbAndStab.C[k] := AsSubgroup(ladder.chain[k],orbAndStab.C[k-1]);
  if ladder.subgroupIndex[k-1] <> ladder.subgroupIndex[k] then
    BlockStabilizerReinitialize(p,k-1,orbAndStab, ladder);
    coset := rec( g := p, b := ladder.one, i := 1);
    coset.stabilizer := orbAndStab.C[k];
    queue := QueueCreate();
    QueuePushBack(queue, coset);
    tree := coset;

    coset := rec( g := p, b := ladder.one, i := k);
    coset.stabilizer := orbAndStab.C[k];
    Print("\n\n\n\n####################################\n");
    Print("\nIn StroLLBreadthFuseCanonicalDCReps: k := ",k," p := ",p);
    Print("\n\t              \t");
    StroLLPrint(coset);

    for i in [ 2 .. k-1 ] do
      z := orbAndStab.z[i];
      intersection := Intersection(ladder.chain[i],orbAndStab.C[1]^(z^-1));
      if intersection <> orbAndStab.C[i] then
        Error("\nThe given stabilizer is wrong (i := ",i,")\n");
      fi;
    od;

    while not QueueEmpty(queue) do
      coset := QueueFront(queue);
      i := coset.i;
      g := coset.g;
      if i+1 = k then
        b := coset.b;
        z := orbAndStab.z[i];
        #orbAndStab.C[k] := ClosureGroup(orbAndStab.C[k],b^(z^-1));
        if not b^(z^-1) in ladder.chain[k] then
          Error("\nThe Stabilizer is wrong(1)"); 
        fi;
        if not b in ladder.chain[1] then
          Error("\nThe Stabilizer is wrong(2)"); 
        fi;
        #Print("\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
        #Print("\nExtend the stabilizer by element ",b);
        #Print("\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
        orbAndStab.C[k] := ClosureSubgroupNC(orbAndStab.C[k],b^(z^-1));
        QueuePopFront(queue);
      else
        z := orbAndStab.z[k-1];
        intersection := orbAndStab.C[k-1]^(z*g^-1);
        intersection := Intersection(intersection,ladder.chain[i]);
        if coset.stabilizer <> intersection then
          Error("\nThe Stabilizer is wrong(3)"); 
        fi;
        if ladder.isSplitStep[i+1] then
          canonizer := StroLLBreadthSplitOrbit(queue,p,k,orbAndStab,ladder);
          if not canonizer = ladder.one then
            return canonizer; 
          fi;
        else 
          StroLLBreadthFuseOrbit(tree,queue,p,orbAndStab,ladder);
        fi;
      fi;
    od;

    coset := rec( g := p, b := ladder.one, i := k);
    coset.stabilizer := orbAndStab.C[k];
    Print("\n\n\nEnde StroLLBreadthFuseCanonicalDCReps: k := ",k," p := ",p);
    Print("\n\t              \t");
    StroLLPrint(coset);
    Print("\n\n\n\n####################################\n");

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


