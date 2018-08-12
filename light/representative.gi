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
  local z, pos, canon, gens, permlist, i;
  # initialize data storage
  if not IsBound(orbAndStab.p) then
    orbAndStab.p := [];
    orbAndStab.z := [One(p)];
    orbAndStab.orbits := [];
    orbAndStab.gensOfStab := [];
    orbAndStab.small := [];
    orbAndStab.homImageGensOfStab := [];
    orbAndStab.small := [1];
    orbAndStab.orbitMap := [[1]];
    orbAndStab.canon := [];
  fi;
    
  for i in [ 2 .. n ] do
    if ladder.subgroupIndex[i-1] <= ladder.subgroupIndex[i] then
      # if p has changed, delete old data storage
      if not IsBound(orbAndStab.p[i]) or not orbAndStab.p[i]*p^-1 in ladder.chain[i] then
        orbAndStab.p[i] := p;
        z := orbAndStab.z[i-1];
        pos := PositionCanonical(ladder.pathTransversal[i],p*z^-1);
        orbAndStab.small[i] := PositionCanonical(ladder.transversal[i],p*z^-1);
        canon := ladder.pathTransversal[i][pos];
        orbAndStab.z[i] := canon*z;
        orbAndStab.orbits[i] := [];
        orbAndStab.orbitMap[i] := [];
        orbAndStab.canon[i] := [];
        gens := List(GeneratorsOfGroup(orbAndStab.C[i-1])); 
        orbAndStab.gensOfStab[i] := List(gens, x -> x^(z^-1)); 
        permlist := List(orbAndStab.gensOfStab[i], x -> Image(ladder.hom[i],x));
        orbAndStab.homImageGensOfStab[i] := permlist; 
      fi;
    else
      # if p has changed, delete old data storage
      if not IsBound(orbAndStab.p[i]) or not orbAndStab.p[i]*p^-1 in ladder.chain[i] then
        orbAndStab.p[i] := p;
        z := orbAndStab.z[i-1];
        pos := PositionCanonical(ladder.pathTransversal[i],p*z^-1);
        orbAndStab.small[i] := PositionCanonical(ladder.transversal[i],p*z^-1);
        orbAndStab.z[i] := z;
        orbAndStab.orbits[i] := [];
        orbAndStab.orbitMap[i] := [];
        orbAndStab.canon[i] := [];
        gens := List(GeneratorsOfGroup(orbAndStab.C[i])); 
        orbAndStab.gensOfStab[i] := List(gens, x -> x^(z^-1)); 
        permlist := List(orbAndStab.gensOfStab[i], x -> Image(ladder.hom[i],x));
        orbAndStab.homImageGensOfStab[i] := permlist; 
      fi;
    fi;
  od;
end;


BlockPosition := function(g,i,orbAndStab,ladder)
  return PositionCanonical(ladder.transversal[i],g*(orbAndStab.z[i-1])^-1);
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
    return ladder.one; 
  fi;

  if IsBound(orbAndStab.orbitMap[i][pos]) then
    min := orbAndStab.orbitMap[i][pos]; 
    orbit := orbAndStab.orbits[i][min];
  else
    # build up new orbit
    gensImage := orbAndStab.homImageGensOfStab[i]; 
    options := rec();
    options.orbsizebound := Size(ladder.transversal[i]);
    tmp := OrbitFromGenerators(pos,gensImage,options);
    orbAndStab.orbits[i][tmp.min] := tmp.orbit;
    for j in tmp.orbit do
      orbAndStab.orbitMap[i][j] := tmp.min; 
    od;
    return tmp;
    #Perform(orbit,function(x) orbAndStab.orbitMap[i][x]:=min; end);
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
  local z, gens, c;
  if IsBound(orbAndStab.canon[i][pos]) then
    return orbAndStab.canon[i][pos]; 
  fi;
  z := orbAndStab.z[i-1];
  gens := orbAndStab.gensOfStab[i]; 
  c := BlockStabilizerCanElmntFromGenerators(orbit,pos,min,gens,z);
  orbAndStab.canon[i][pos] := c;
  return c;
end;


StroLLSmallestPathHelper := function( k, ladder )
  local one, stab, gens, pos, gensIm, options, orbit, min, c, i, j;
  one := ladder.one;
  if not IsBound(ladder.SmallestPathToCoset[k]) then
    ladder.SmallestPathToCoset[k] := rec();
    ladder.SmallestPathToCoset[k].orbList := [];
    ladder.SmallestPathToCoset[k].posList := [];
    ladder.SmallestPathToCoset[k].canon := [];
  fi;
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      if not IsBound(ladder.SmallestPathToCoset[k].orbList[i]) then
        stab := ladder.cut1toJplusI[k][i-1]; 
        gens := List(GeneratorsOfGroup(stab)); 
        pos := PositionCanonical(ladder.transversal[i],one);
        gensIm := List(gens, x -> Image(ladder.hom[i],x));
        options := rec();
        options.orbsizebound := Size(ladder.transversal[i]);
        orbit := OrbitFromGenerators(pos,gensIm,options).orbit;
        ladder.SmallestPathToCoset[k].orbList[i] := orbit;
        ladder.SmallestPathToCoset[k].posList[i] := pos;
        ladder.SmallestPathToCoset[k].canon[i] := [];
        for j in [1..Size(orbit)] do
          min := orbit[j];
          c := BlockStabilizerCanElmntFromGenerators(orbit,pos,min,gens,one);
          ladder.SmallestPathToCoset[k].canon[i][min] := c;
        od;
      fi;
    fi; 
  od;
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
  local z, perm, orbit, min, pos, c, i;
  if not IsBound(ladder.SmallestPathToCoset[k]) then
    StroLLSmallestPathHelper(k,ladder);
  fi;
  z := ladder.one;
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      perm := Image(ladder.hom[i],g);
      orbit := ladder.SmallestPathToCoset[k].orbList[i];
      min := Minimum(List(orbit,x -> x^perm));
      pos := min^(perm^-1);
      g := ladder.SmallestPathToCoset[k].canon[i][pos]*g; 
      min := ladder.representativeMap[i][min];
      c := ladder.pathTransversal[i][min];
      g := g*c^-1;
      z := c*z;
    fi; 
  od;
  return z;
end; 

IsSmallestPathToCoset := function( g, k, ladder )
  local z, perm, orbit, min, pos, c, i;
  if not IsBound(ladder.SmallestPathToCoset[k]) then
    StroLLSmallestPathHelper(k,ladder);
  fi;
  z := ladder.one;
  for i in [ 2 .. k ] do
    if ladder.subgroupIndex[i-1] < ladder.subgroupIndex[i] then
      perm := Image(ladder.hom[i],g);
      orbit := ladder.SmallestPathToCoset[k].orbList[i];
      min := Minimum(List(orbit,x -> x^perm));
      pos := ladder.transvOnePos[i]^perm;
      if pos <> min then
        return false; 
      fi;
      min := ladder.representativeMap[i][min];
      c := ladder.pathTransversal[i][min];
      g := g*c^-1;
      z := c*z;
    fi; 
  od;
  return true;
end; 

