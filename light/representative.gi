# for every path [A_1g,..,A_kg] there exists a canonical h in G
# so that [A_1h,..,A_kh] = [A_1g,..,A_kg]
PathRepresentative := function(g,k,ladder)
  local z, pos, map, canon, i;
  z := One(g); 
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      pos := PositionCanonical(ladder.pathTransversal[i],g);
      canon := ladder.pathTransversal[i][pos];
      g := g*canon^-1;
      z := canon*z;
    fi;
  od;
  return z;
end;




BlockStabilizerReinitialize := function(p,n,orbAndStab,ladder)
  local z, pos, canon, U, permlist, i;
  # initialize data storage
  if not IsBound(orbAndStab.p) then
    orbAndStab.p := [];
    orbAndStab.z := [One(p)];
    orbAndStab.orbits := [];
    orbAndStab.min := [];
    orbAndStab.gensOfStab := [];
    orbAndStab.small := [];
    orbAndStab.homImageGensOfStab := [];
  fi;
    
  for i in [ 2 .. n ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      # if p has changed, delete old data storage
      if false = IsBound(orbAndStab.p[i]) or not orbAndStab.p[i]*p^-1 in ladder.chain[i] then
        z := orbAndStab.z[i-1];
        pos := PositionCanonical(ladder.pathTransversal[i],p*z^-1);
        canon := ladder.pathTransversal[i][pos];
        orbAndStab.z[i] := canon*z;
        orbAndStab.p[i] := p;
        orbAndStab.orbits[i] := [];
        orbAndStab.min[i] := [];
        U := ConjugateGroup( orbAndStab.C[i-1], orbAndStab.z[i-1]^-1 );
        orbAndStab.gensOfStab[i] := List(GeneratorsOfGroup(U)); 
        permlist := List(orbAndStab.gensOfStab[i], x -> Image(ladder.hom[i],x));
        orbAndStab.homImageGensOfStab[i] := permlist; 
      fi;
    else
      # if p has changed, delete old data storage
      if false = IsBound(orbAndStab.p[i]) or not orbAndStab.p[i]*p^-1 in ladder.chain[i-1] then
        orbAndStab.z[i] := orbAndStab.z[i-1];
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


BlockPosition := function(g,i,orbAndStab,ladder)
  local z, pos;
  if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
    z := orbAndStab.z[i-1];
  else
    z := orbAndStab.z[i];
  fi;
  pos := PositionCanonical(ladder.transversal[i],g*z^-1);
  return pos;
end;


OrbitFromGenerators := function(pos,gensImage,options)
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
    tmp := OrbitFromGenerators(pos,gensImage,options);
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
  z := orbAndStab.z[i-1];
  generators := orbAndStab.gensOfStab[i]; 
  return BlockStabilizerCanElmntFromGenerators(orbit,pos,min,generators,z);
end;




# A subgroup ladder [A_1,..,A_k] is strong, if A_1 acts transitively on
# the set of all pathes of length k.
#
# This function needs a strong ladder [A_1,..,A_k] and for all i<k
# a total order on the cosets A_i\A_i+1 must be defined. 
#
# The given total order allows it to define a lexicographic ordering
# on the set of pathes of length up to k.
# 
# Let [A_1,...,A_k] be an strong ladder and g an element in A_1. 
# Then this function calculates min_{a \in A_k}([A_1ag,..,A_kag]).
# This is the smallest strong path of length k, 
# whose last component is the coset A_kg.
#
StroLLSmallestPathToCoset := function( g, k, ladder )
  local one, z, pos, stab, gens, gensIm, options, tmp, orbit, min, c, i;
  one := One(ladder.G);
  z := one;
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      # Print("\nStep ",i,"\n");
      # Print("g = ",g,"\n");
      pos := PositionCanonical(ladder.transversal[i],g);
      # Print("transversal = ",List(ladder.transversal[i]),"\n");
      # Print("pos = ",pos,"\n");
      # Print("transversal[",pos,"] = ",ladder.transversal[i][pos],"\n");
      stab := ladder.cut1toJplusI[k][i-1]^g; 
      # Print("gens = ",List(GeneratorsOfGroup(ladder.cut1toJplusI[k][i-1])),"\n");
      gens := List(GeneratorsOfGroup(stab)); 
      # Print("gens^g = ",gens,"\n");
      gensIm := List(gens, x -> Image(ladder.hom[i],x));
      options := rec();
      options.orbsizebound := Size(ladder.transversal[i]);
      tmp := OrbitFromGenerators(pos,gensIm,options);
      orbit := tmp.orbit;
      # Print("orbit = ",orbit,"\n");
      # if i = 2 then
      #   Print("apply orbit to ",i," ",List(orbit, x -> 1^(ladder.transversal[i][x])),"\n");
      # else
      #   Print("apply orbit to ",(i+1)/2);
      #   Print(List(orbit, x -> ((i+1)/2)^(ladder.transversal[i][x])),"\n");
      # fi;
      min := tmp.min;
      g := g*BlockStabilizerCanElmntFromGenerators(orbit,pos,min,gens,one); 
      # Print("g = ",g,"\tafter orbit calculations\n");
      min := ladder.representativeMap[i][min];
      c := ladder.pathTransversal[i][min];
      g := g*c^-1;
      # Print("g = ",g," after transposition\n");
      z := c*z;
      # Print("z = ",z,"\n");
    fi; 
  od;
  return z;
end; 

