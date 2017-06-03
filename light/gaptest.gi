BuildStroLLSubladder := 0;

buildStroLLTransversals := function(groups)
  local ladder, i, index, U ;
  ladder := rec();
  ladder.G := groups[1];
  ladder.chain := [groups[1]]; 
  ladder.subgroupIndex := [1];
  ladder.transversal := [RightTransversal(ladder.G,ladder.G)];
  ladder.rightcosets := [RightCosets(ladder.G,ladder.G)];
  ladder.hom := [];
  for i in [2 .. Size(groups)] do
    if false = IsSubgroup(ladder.G,groups[i]) then
      Error("Entry ",i," in grouplist is not a subgroup of the group on the first position in the grouplist\n");
      return;
    fi;
    U := groups[i];
    index := IndexNC(ladder.G,U);
    ladder.subgroupIndex[i] := index;
    if ladder.subgroupIndex[i-1] > index then
      if false = IsSubgroup(U,ladder.chain[i-1]) then
        Error("Entry ",i," in grouplist is not a group containing the previous group on position ",i-1," in the grouplist\n"); 
        return;
      fi;
      ladder.transversal[i] := RightTransversal(U,ladder.chain[i-1]);
      ## DEBUG
      if not 1 = PositionCanonical(ladder.transversal[i],One(U)) then
        Error("Assumption on the transversal is not fulfilled");
      fi;
      ## DEBUG end
      ladder.rightcosets[i] := RightCosets(U,ladder.chain[i-1]);
      ladder.hom[i] := FactorCosetAction(U,ladder.chain[i-1]);
#     ladder.hom[i] := ActionHomomorphism(U,ladder.transversal[i],OnRight);
    else
      if false = IsSubgroup(ladder.chain[i-1],U) then
        Error("Entry ",i," in list is not a subgroup of the previous group on position ",i-1," in the grouplist\n"); 
        return;
      fi;
      ladder.transversal[i] := RightTransversal(ladder.chain[i-1],U);
      ## DEBUG
      if not 1 = PositionCanonical(ladder.transversal[i],One(U)) then
        Error("Assumption on the transversal is not fulfilled");
      fi;
      ## DEBUG end
      ladder.rightcosets[i] := RightCosets(ladder.chain[i-1],U);
      ladder.hom[i] := FactorCosetAction(ladder.chain[i-1],U);
    fi;
    ladder.chain[i] := U;
  od;
  return ladder;
end;



BuildStroLLPathRepresentativeMapping := function(ladder)
  ladder.PathRepresentative := function(g,k)
    local z, perm, position, canonical, i;
    z := One(ladder.G); 
    for i in [ 2 .. k ] do
      if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
        perm := Image(ladder.hom[i],g);
        position := 1^perm;
#       position := PositionCanonical(ladder.transversal[i],g);
#       if not position = position2 then
#         Error("the positioning via homomorphism is not correct"); 
#       fi;
        canonical := ladder.transversal[i][position];
        g := g*canonical^-1;
        z := canonical*z;
      fi;
    od;
    return z;
  end;
end;



BuildStroLLPathCompare := function(ladder)
  ladder.LowerOrEqualPath := function( a, b, k)
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
end;


BuildStroLLTransversalCompare := function(ladder)
  ladder.LowerOrEqualForLadderGroupCosets := function( a, b, i)
    local perm_a, perm_b, position_a, position_b;
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      if not a in ladder.chain[i-1] then
        Error("a is not in A_{i-1}");
      fi;
      if not b in ladder.chain[i-1] then
        Error("b is not in A_{i-1}");
      fi;
      perm_a := Image(ladder.hom[i],a);
      perm_b := Image(ladder.hom[i],b);
      position_a := 1^perm_a;
      position_b := 1^perm_b;
#     position_a := PositionCanonical(ladder.transversal[i],a);        
#     position_b := PositionCanonical(ladder.transversal[i],b);        
      if  position_a > position_b then
        return false;
      fi;
    fi; 
    return true;
  end;
end;



FindOrbitRep := function( g, k, V, ladder)
  local result, transv, U, H, versionSwitchOrbitAlgorithm, omega, V_Image, gp, tmp, mp, gens, acts, homAct, ug, um;
  result := rec();
  transv := ladder.transversal[k];
  if ladder.subgroupIndex[k-1] < ladder.subgroupIndex[k] then
    U := ladder.chain[k];
    H := ladder.chain[k-1];
  else
    U := ladder.chain[k-1];
    H := ladder.chain[k];
  fi;
  ## DEBUG 
  if  not IsSubgroup(H,V) then
    Error("the operating group V is not a subgroup of k-th ladder group");
  fi;
  if  not g in H then
    Error("g is not in the k-th ladder group");
  fi;
  ## DEBUG end 

  versionSwitchOrbitAlgorithm := 2;

  ## Orbit Algorithm Version five 
  if 5 = versionSwitchOrbitAlgorithm then
    omega := [ 1 .. Size(transv) ];
    homAct := function(o,h)
      o := transv[o];
      o := o*h;
      return PositionCanonical(transv,o);
    end;
    gp := PositionCanonical(transv,g);
    tmp := OrbitStabilizer(V,omega,gp,homAct);
    result.stabilizer := tmp.stabilizer;
    result.orbitPositions := List( tmp.orbit ); 
    result.orbitRepresentatives := List( result.orbitPositions, x -> transv[x] ); 
    result.orbitMinPosition := Minimum(result.orbitPositions);
    result.orbitCanonicalElement := transv[result.orbitMinPosition]; 
    mp := result.orbitMinPosition;
    result.canonizer := RepresentativeAction(V,omega,gp,mp,homAct);


  ## Orbit Algorithm Version four 
  elif 4 = versionSwitchOrbitAlgorithm then
    omega := [ 1 .. Size(transv) ];
    gens := List(GeneratorsOfGroup(V));
    acts := List(gens, x -> Image(ladder.hom[k],x));
    gp := PositionCanonical(transv,g);
    tmp := OrbitStabilizer(V,omega,gp,gens,acts,OnPoints);
    result.stabilizer := tmp.stabilizer;
    result.orbitPositions := List( tmp.orbit ); 
    result.orbitRepresentatives := List( result.orbitPositions, x -> transv[x] ); 
    result.orbitMinPosition := Minimum(result.orbitPositions);
    result.orbitCanonicalElement := transv[result.orbitMinPosition]; 
    mp := result.orbitMinPosition;
    result.canonizer := RepresentativeAction(V,omega,gp,mp,gens,acts,OnPoints);

  ## Orbit Algorithm Version three 
  elif 3 = versionSwitchOrbitAlgorithm then
    omega := [ 1 .. Size(transv) ];
    homAct := function(o,h)
      h := Image(ladder.hom[k],h);
      o := o^h;
      return o;
    end;
    gp := PositionCanonical(transv,g);
    tmp := OrbitStabilizer(V,omega,gp,homAct);
    result.stabilizer := tmp.stabilizer;
    result.orbitPositions := List( tmp.orbit ); 
    result.orbitRepresentatives := List( result.orbitPositions, x -> transv[x] ); 
    result.orbitMinPosition := Minimum(result.orbitPositions);
    result.orbitCanonicalElement := transv[result.orbitMinPosition]; 
    mp := result.orbitMinPosition;
    result.canonizer := RepresentativeAction(V,omega,gp,mp,homAct);

  ## Orbit Algorithm Version two 
  elif 2 = versionSwitchOrbitAlgorithm then
    homAct := function(o,h)
      o := o*h;
      o := PositionCanonical(transv,o);
      return transv[o];
    end;
    ug := transv[PositionCanonical(transv,g)];
    tmp := OrbitStabilizer(V,transv,ug,homAct);
    result.stabilizer := tmp.stabilizer;
    result.orbitRepresentatives := List( tmp.orbit ); 
    result.orbitPositions := List( result.orbitRepresentatives, x -> Position(transv,x) ); 
#   result.orbitRepresentatives := List( result.orbitPositions, x -> transv[x] ); 
    result.orbitMinPosition := Minimum(result.orbitPositions);
    result.orbitCanonicalElement := transv[result.orbitMinPosition]; 
    um := result.orbitCanonicalElement;
    result.canonizer := RepresentativeAction(V,transv,ug,um,homAct);

  ## Orbit Algorithm Version one
  else 
    ug := RightCoset(U,g);
    tmp := OrbitStabilizer(V,ladder.rightcosets[k],ug,OnRight);
    result.stabilizer := tmp.stabilizer;
    result.orbitRepresentatives := List( tmp.orbit, x -> Representative(x) ); 
    result.orbitPositions := List( result.orbitRepresentatives, x -> PositionCanonical(transv,x) ); 
    result.orbitRepresentatives := List( result.orbitPositions, x -> transv[x] ); 
    result.orbitMinPosition := Minimum(result.orbitPositions);
    result.orbitCanonicalElement := transv[result.orbitMinPosition]; 
    ug := RightCoset(U,g);
    um := RightCoset(U,result.orbitCanonicalElement);
    result.canonizer := RepresentativeAction(V,ladder.rightcosets[k],ug,um,OnRight);
  fi;


  ## DEBUG
  if  not IsSubgroup(V,result.stabilizer) then
    Error("stabilizer calculation failed");
  fi;
  if not result.orbitCanonicalElement in H then
    Error("the canonical element is outside of the given range");
  fi;
  if not g in H then
    Error("the given element g has changed unintentionally");
  fi;
  ## DEBUG end 


  ## DEBUG begin
  if not result.canonizer in V then
    Error("canonizer is not in the operating group"); 
  fi;
  ## DEBUG end 
  return result;
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
  local z, U, zi, i, b, stab, tmp, h;
  h := g;
  z := One(ladder.G);
  stab := ConjugateGroup(ladder.chain[k],h);
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      # After step i the first i components of the 
      # smallest path to the coset A_kg are (A_1h*z,...,A_ih*z) 
      # and A_kh*z = A_kg
      # stab^z is the combined stabilizer of
      # the path (A_1h*z,...,A_ih*z) and A_kh*z
      # h is in A_i, thus we can use the order on A_{i+1}\A_i to determine 
      # the (i+1)-th component of the smallest path to A_kg
      tmp := FindOrbitRep(h,i,stab,ladder);
      stab := tmp.stabilizer;
      b := tmp.canonizer; 
      zi := tmp.orbitCanonicalElement;   
      h := h*b;
      stab := ConjugateGroup(stab,b);
      h := h*zi^-1;
      stab := ConjugateGroup(stab,zi^-1);
      z := zi*z;
      # Print("h = ",h,"\n");
      # Print("b = ",b,"\n");
      # Print("zi = ",zi,"\n\n");
      if  not h*z*g^-1 in ladder.chain[k] then
        ## DEBUG !!!
        Error("A_kh*z <> A_kg \nargument g = ",g,"\nargument k = ",k,"\n"); 
      fi;
    fi; 
  od;
  return h*z;
end; 




NextStroLLStep := 0;
SplitOrbit := 0;
FuseOrbit := 0;
CheckCanonicalStroll := 0;



# A_i <= A_{i-1} and g is in the preimage of A_{i-1}p;
SmallestOrbitRepresentativeInStabilizerOf_p := function( g, i, p, ladder )
  local result, z, options, pos, U, gensPreimage, gensImage, isPointStabilizer, orbit, min, pnt, word, j;
  result := rec();
  if IsBound(ladder.orbitrep) then
    z := ladder.PathRepresentative( p, i-1 );
  else
    z := ladder.PathRepresentative( p, i-1 );
    g := g*z^-1;
    if not g in ladder.chain[i-1] then
      Error("the Element g must be in the ladder group A_{i-1}p");
    fi;
    pos := PositionCanonical(ladder.transversal[i],g);
    U := ConjugateGroup( ladder.C[i-1], z^-1 );
    gensPreimage := List(GeneratorsOfGroup(U)); 
    gensImage := List(gensPreimage, x -> Image(ladder.hom[i],x)); 
    isPointStabilizer := true;
    for j in gensImage do
      if not pos^j = pos then
        isPointStabilizer := false; 
        break;
      fi; 
    od;
    result.canonizer := One(p);
    result.canonical := ladder.transversal[i][pos]*z;
    if not isPointStabilizer then
      options := rec();
#     options.orbitgraph := true;
      options.grpsizebound := Size(ladder.C[i-1]);
      options.orbsizebound := Size(ladder.transversal[i]);
      options.schreier := true;
      options.storenumbers := true;
#     options.stabsizebound := Size(ladder.C[i]);
      orbit := Orb(gensImage,pos,OnPoints,options);
      Enumerate(orbit);
      min := pos;
      for j in orbit do
        if  min > j then
          min := j; 
        fi; 
      od;
      if not min = pos then
        pnt := Position(orbit,min);
        word := TraceSchreierTreeForward(orbit,pnt);
        word := List(word, x -> gensPreimage[x]);
        result.canonizer := Product(word)^z;
        result.canonical := ladder.transversal[i][min]*z;
      fi;
    fi;
    if not result.canonizer^(z^-1) in ladder.chain[i-1] then
      Error("the Element canonizer must be in the ladder group A_{i-1}");
    fi;
    if not g*result.canonizer^(z^-1) in ladder.chain[i-1] then
      Error("the Element g*p^-1 must be in the ladder group A_{i-1}");
    fi;
    if pos < PositionCanonical(ladder.transversal[i],g*result.canonizer^(z^-1)) then
      Error("hier passt was nicht\n");
    fi;
  fi;
  return result;
end;


# A_i <= A_{i-1} and a and b are in the preimage of A_{i-1}p;
LowerOrEqualInStabilizerOf_p := function( a, b, i, p, ladder )
  local z, position_a, position_b;
  z := ladder.PathRepresentative(p,i-1);
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
SplitOrbit := function( block, blockStack, p, k, ladder, debug)
  local g, b, i, preimage, c, tmp, newBlock, h;
  g := block.g;
  b := block.b;
  i := block.i;
  # preimage is a transversal of E[k][i+1]\E[k][i];
  preimage := ladder.E_ij_transversal[k][i+1]; 
  for h in preimage do
    ## this optimisation is experimental and must be checked
    ## opimisation begin 
    if Size(ladder.C[i+1]) = Size(ladder.C[i]) then
      c := One(g);
    else
      tmp := SmallestOrbitRepresentativeInStabilizerOf_p( h*g*b, i+1, p, ladder );
      c := tmp.canonizer;
    fi;
    ## opimisation end
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
# FuseOrbit only puts one of these g onto the stack
FuseOrbit := function( block, blockStack, ladder )
  local g, i, b, z, U, tmp;
  g := block.g;
  i := block.i;
  b := block.b;
  ## this optimisation is experimental and must be checked
  ## opimisation begin 
  if Size(ladder.C[i]) = Size(ladder.C[i+1]) then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
    return;
  fi;
  ## opimisation end
  ## TODO is this performance relevant?
  z := SmallestStrongPathToCoset(g,i+1,ladder);
  U := ConjugateGroup(ladder.C[i+1],b^-1*z^-1);
  tmp := FindOrbitRep( g*z^-1, i+1, U, ladder);
  # A_ig*z^-1 = A_i*tmp.orbitCanonicalElement ?
  if g*z^-1*tmp.orbitCanonicalElement^-1 in ladder.chain[i] then
    block := rec( g := g, b := b, i := i+1 );
    StackPush(blockStack,block);
    # Print "newBlock ", block, "\n" );
  fi;
end;


# k, p - check wether A_kp is the smallest coset in A_kpB
# this function checks the orbits of all paths to the A_kp coset
# for a smaller path.
# If it finds a smaller path it returns a c with A_kpc < A_kp
# It also calculates the stabilizer of A_kp in B.
CheckSmallestInDoubleCosetFuse := function( k, p, ladder)
  local counter, block, i, blockStack, b, isSplitStep, canonizer;
  # Print"\n");
  # Print" ---- ---- ---- ", k, " ---- ---- ----\n");
  # Print" ---- ---- ---- ", k, " ---- ---- ----\n");
  # Print" ---- ---- ---- ", k, " ---- ---- ----\n");
  # Print"\n");
  counter := 0;
  ladder.C[k] := ladder.C[k-1];
  block := rec( g := p, b := One(p), i := 1);
  blockStack := StackCreate(100);
  StackPush( blockStack, block);
  while not StackIsEmpty(blockStack) do
    counter := counter + 1;
    # Print "----------- counter = ", counter, "-----------\n" );
    block := StackPop(blockStack);
    # Print "Pop: ", block, "\n" );
    i := block.i;
    b := block.b;
    if i+1 = k then
      # Print"Stabilizer size before: ", Size(ladder.C[i+1]), "\n");
      ladder.C[i+1] := ClosureGroup(ladder.C[i+1],b);
      # Print"After: ", Size(ladder.C[i+1]), "\n");
      continue;
    fi;
    isSplitStep := ladder.subgroupIndex[i] < ladder.subgroupIndex[i+1];
    if isSplitStep then
      ## DEBUG 
      if  counter = 1000 and k = 8 then
        canonizer := SplitOrbit(block,blockStack,p,k,ladder,true);
        Error("break");
      else
        canonizer := SplitOrbit(block,blockStack,p,k,ladder,false);
      fi;
      if not canonizer = One(p) then
        return canonizer; 
      fi;
    else
      FuseOrbit(block,blockStack,ladder);
    fi;
  od;
  return One(p);
end;



CheckSmallestInDoubleCosetSplit := function( i, p, ladder) 
  local z, U, tmp, c;
  # A_ipz^-1c is smallest in its C_{i-1} orbit
  z := ladder.PathRepresentative(p,i-1);
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




constructStrongLadder := function(groups)
  local ladder;
  ladder := buildStroLLTransversals(groups);
  BuildStroLLPathRepresentativeMapping(ladder);
  BuildStroLLPathCompare(ladder);
  BuildStroLLTransversalCompare(ladder);
  BuildStroLLSubladder(ladder);
  return ladder;
end;





BuildStroLLSubladder := function(ladder)
  local i, j, c;
  ladder.E := [];
  ladder.E_ij_transversal := [];
  for i in [ 2 .. Size(ladder.chain)-1 ] do
    ladder.E[i] := [ladder.chain[i]];
    ladder.E_ij_transversal[i] := [];
    for j in [ 2 .. i ] do
      if ladder.subgroupIndex[j-1] < ladder.subgroupIndex[j] then
        ladder.E[i][j] := Intersection(ladder.chain[i],ladder.chain[j]); 
        # E_ij_transversal = E_[i][j]/E[i][j-1];
        ladder.E_ij_transversal[i][j] := RightTransversal(ladder.E[i][j-1],ladder.E[i][j]);
      else
        ladder.E[i][j] := Intersection(ladder.chain[i],ladder.chain[j]); 
        # E_ij_transversal = E_[i][j-1]/E[i][j];
        ladder.E_ij_transversal[i][j] := RightTransversal(ladder.E[i][j],ladder.E[i][j-1]);
      fi;
    od;
  od;
end;
