

PathRepresentative := function(g,k,ladder)
  local z, perm, position, canonical, i;
  z := One(g); 
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
#     perm := Image(ladder.hom[i],g);
#     position := 1^perm;
      position := PositionCanonical(ladder.transversal[i],g);
#     if not position = position2 then
#       Error("the positioning via homomorphism is not correct"); 
#     fi;
      canonical := ladder.transversal[i][position];
      g := g*canonical^-1;
      z := canonical*z;
    fi;
  od;
  return z;
end;





# A_i <= A_{i-1} and a and b are in the preimage of A_{i-1}p;
LowerOrEqualInStabilizerOf_p := function( a, b, i, orbAndStab, ladder )
  local U, z, position_a, position_b;
  z := orbAndStab.z[i];
  position_a := PositionCanonical(ladder.transversal[i],a*z^-1);        
  position_b := PositionCanonical(ladder.transversal[i],b*z^-1);        
  if position_a <= position_b then
    return true; 
  fi;
  return false;
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



ReinitializeOrbitAndStabilizerStorage := function(p,n,orbAndStab,ladder)
  local U, permlist, i;
  # initialize data storage
  if not IsBound(orbAndStab.p) then
    orbAndStab.p := [];
    orbAndStab.z := [];
    orbAndStab.orbits := [];
    orbAndStab.min := [];
    orbAndStab.gensOfStab := [];
    orbAndStab.homImageGensOfStab := [];
  fi;
    
  for i in [ 2 .. n ] do
    # if p has changed, delete old data storage
    if ladder.subgroupIndex[i-1] <= ladder.subgroupIndex[i] then
      if false = IsBound(orbAndStab.p[i]) or not orbAndStab.p[i]*p^-1 in ladder.chain[i-1] then
        orbAndStab.p[i] := p;
        orbAndStab.z[i] := PathRepresentative( p, i-1, ladder ); 
        orbAndStab.orbits[i] := [];
        orbAndStab.min[i] := [];
        U := ConjugateGroup( orbAndStab.C[i-1], orbAndStab.z[i]^-1 );
        orbAndStab.gensOfStab[i] := List(GeneratorsOfGroup(U)); 
        permlist := List(orbAndStab.gensOfStab[i], x -> Image(ladder.hom[i],x));
        orbAndStab.homImageGensOfStab[i] := permlist; 
      fi;
    else
      if false = IsBound(orbAndStab.p[i]) or not orbAndStab.p[i]*p^-1 in ladder.chain[i] then
        orbAndStab.p[i] := p;
        orbAndStab.z[i] := PathRepresentative( p, i, ladder ); 
        orbAndStab.orbits[i] := [];
        orbAndStab.min[i] := [];
        U := ConjugateGroup( orbAndStab.C[i], orbAndStab.z[i]^-1 );
        orbAndStab.gensOfStab[i] := List(GeneratorsOfGroup(U)); 
        permlist := List(orbAndStab.gensOfStab[i], x -> Image(ladder.hom[i],x));
        orbAndStab.homImageGensOfStab[i] := permlist; 
      fi;
    fi;
  od;
end;



# A_i <= A_{i-1} and g is in the preimage of A_{i-1}p;
SmallestOrbitRepresentativeInStabilizerOf_p := function( g, i, p, orbAndStab, ladder )
  local z, pos, isInOrbit, min, U, gensPreimage, gensImage, isPointStabilizer, canonizer, options, orbit, pnt, word, j;
  if i = 1 then
    return One(g); 
  fi;


  # initialize g and pos 
  z := orbAndStab.z[i];
  g := g*z^-1;
  pos := PositionCanonical(ladder.transversal[i],g);

  # check, if pos is in one of the known orbits
  isInOrbit := false;
  for j in [ 1 .. Size(orbAndStab.orbits[i]) ] do
    orbit := orbAndStab.orbits[i][j];
    if pos in orbit then
      isInOrbit := true;
      min := orbAndStab.min[i][j];
      break;
    fi;
  od;   

  # element is not in one of the known orbits
  if not isInOrbit then
    # build up new orbit
    gensImage := orbAndStab.homImageGensOfStab[i]; 
    isPointStabilizer := true;
    for j in gensImage do
      if not pos^j = pos then
        isPointStabilizer := false; 
        break;
      fi; 
    od;
    if not isPointStabilizer then
      options := rec();
      if ladder.subgroupIndex[i-1] <= ladder.subgroupIndex[i] then
        options.grpsizebound := Size(orbAndStab.C[i-1]);
      else
        options.grpsizebound := Size(orbAndStab.C[i]);
      fi;
      options.orbsizebound := Size(ladder.transversal[i]);
      options.schreier := true;
      options.storenumbers := true;
      orbit := Orb(gensImage,pos,OnPoints,options);
      Enumerate(orbit);
      min := pos;
      for j in orbit do
        if  min > j then
          min := j; 
        fi; 
      od;
      Add(orbAndStab.orbits[i],orbit);
      Add(orbAndStab.min[i],min);
    else
      min := pos;
      orbit := [pos];
      Add(orbAndStab.orbits[i],orbit);
      Add(orbAndStab.min[i],pos);
    fi;
  fi;

  # find canonizing element
  canonizer := One(g);
  gensPreimage := orbAndStab.gensOfStab[i]; 
  if not orbit[1] = pos then
    # find mapping of pos on orbit[1] 
    pnt := Position(orbit,pos);
    word := TraceSchreierTreeForward(orbit,pnt);
    word := List(word, x -> gensPreimage[x]);
    word := Product(word)^-1;
    canonizer := word^z;
  fi;
  if not min = orbit[1] then
    # find mapping of orbit[1] on min 
    pnt := Position(orbit,min);
    word := TraceSchreierTreeForward(orbit,pnt);
    word := List(word, x -> gensPreimage[x]);
    canonizer := canonizer*Product(word)^z;
  fi;
  return canonizer;
end;

