

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


BlockStabilizerPosition := function(g,i,orbAndStab,ladder)
  local z, pos;
  z := orbAndStab.z[i];
  pos := PositionCanonical(ladder.transversal[i],g*z^-1);
  return pos;
end;



# A_i <= A_{i-1} and g is in the preimage of A_{i-1}p;
BlockStabilizerOrbit := function( pos, i, orbAndStab, ladder )
  local z, g, isInOrbit, orbit, min, gensImage, isPointStabilizer, options, orbitInfo, j;

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
  orbitInfo := rec(min := min, orbit := orbit);
  return orbitInfo;
end;





BlockStabilizerCanonizingElmnt := function( i, orbit, pos, min, orbAndStab )
  local gensPreimage, canonizer, z, pnt, word;
  # find canonizing element
  gensPreimage := orbAndStab.gensOfStab[i]; 
  z := orbAndStab.z[i];
  canonizer := One(z);
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

