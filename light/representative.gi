

PathRepresentative := function(g,k,ladder)
  local z, position, canonical, i;
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




BlockStabilizerReinitialize := function(p,i,orbAndStab,ladder)
  local U, permlist, x;
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
end;


BlockStabilizerPosition := function(g,i,orbAndStab,ladder)
  local z, pos;
  z := orbAndStab.z[i];
  pos := PositionCanonical(ladder.transversal[i],g*z^-1);
  return pos;
end;


BlockStabilizerOrbitFromGenerators := function(pos,gensImage,options)
  local isPointStabilizer, orbit, min, j;
  # element is not in one of the known orbits
  options.schreier := true;
  options.storenumbers := true;
  isPointStabilizer := true;
  for j in gensImage do
    if not pos^j = pos then
      isPointStabilizer := false; 
      break;
    fi; 
  od;
  if isPointStabilizer then
    min := pos;
    orbit := [pos];
  else
    orbit := Orb(gensImage,pos,OnPoints,options);
    Enumerate(orbit);
    min := pos;
    for j in orbit do
      if  min > j then
        min := j; 
      fi; 
    od;
  fi;
  return rec(orbit := orbit, min := min);
end;


# A_i <= A_{i-1} and g is in the preimage of A_{i-1}p;
BlockStabilizerOrbit := function( pos, i, orbAndStab, ladder )
  local isInOrbit, orbit, min, gensImage, options, tmp, orbitInfo, j;
  if i = 1 then
    return One(ladder.chain[1]); 
  fi;

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

  if not isInOrbit then
    # build up new orbit
    gensImage := orbAndStab.homImageGensOfStab[i]; 
    options := rec();
    options.orbsizebound := Size(ladder.transversal[i]);
    tmp := BlockStabilizerOrbitFromGenerators(pos,gensImage,options);
    orbit := tmp.orbit;
    min := tmp.min;
    Add(orbAndStab.orbits[i],orbit);
    Add(orbAndStab.min[i],min);
  fi;

  orbitInfo := rec(min := min, orbit := orbit);
  return orbitInfo;
end;




BlockStabilizerCanElmntFromGenerators := function( orbit, pos, min, gensPreimage, z )
  local canonizer, pnt, word;
  # find canonizing element
  canonizer := One(z);
  if not orbit[1] = pos then
    # find mapping of pos on orbit[1] 
    pnt := Position(orbit,pos);
    word := TraceSchreierTreeForward(orbit,pnt);
    word := List(word, x -> gensPreimage[x]);
    word := Product(word)^-1;
    canonizer := word;
  fi;
  if not min = orbit[1] then
    # find mapping of orbit[1] on min 
    pnt := Position(orbit,min);
    word := TraceSchreierTreeForward(orbit,pnt);
    word := List(word, x -> gensPreimage[x]);
    canonizer := canonizer*Product(word);
  fi;
  return canonizer^z;
end;


BlockStabilizerCanonizingElmnt := function( i, orbit, pos, min, orbAndStab )
  local z, generators;
  z := orbAndStab.z[i];
  generators := orbAndStab.gensOfStab[i]; 
  return BlockStabilizerCanElmntFromGenerators(orbit,pos,min,generators,z);
end;


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



