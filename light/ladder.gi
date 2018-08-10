
# Definition subgroup ladder:
# Let G denote a group and U_1,...,U_n a set of subgroups of G.
# The tupel (G,U_1,...,U_n) is a subgroup ladder if for all  
# i < n at least one of the following two statements holds:
#     U_i is a subgroup of U_{i+1}. 
#     U_{i+1} is a subgroup of U_i.

# Definition strong subgroup ladder:
# Let (G,U_1,...,U_n) be a subgroup ladder and for all i <= n 
# let V_i denote the intersection of the groups U_1 to U_i. 
# (G,U_1,...,U_n) is a strong subgroup ladder, if the subgroup
# index |V_n:G| is finite and for all i < n the following
# statement is fulfilled:
#     If U_{i+1} is a subgroup of U_i, then the group indices 
#     |U_i:U_{i+1}| and |V_i:V_{i+1}| are equal.




StrongLadderInit := function(groups,ladder)
  ladder.one := One(groups[1]);
  ladder.subgroupIndex := [1];
  ladder.hom := [];
  ladder.pathTransversal := [];
  ladder.SmallestPathToCoset := [];
  return ladder;
end;



StroLLCheckSubgroupChain := function(ladder,subgroup,i)
  if not IsBound(subgroup[i]) then
    Error("Entry ",i," in ladder is not bound.");
  fi;
  if not IsGroup(subgroup[i]) then
    Error("Entry ",i," in ladder isn't a group.");
  fi;
  if i = 1 then
    ladder.G := subgroup[1];
    ladder.chain := [subgroup[1]];
    ladder.isSplitStep := [false];
    ladder.isFuseStep := [false];
  else
    if not IsSubset(ladder.chain[1],subgroup[i-1]) then
      Error("Entry ",i," in the ladder is not a subgroup of the first group");
    fi;
    if IsSubset(subgroup[i-1],subgroup[i]) then
      ladder.chain[i] := AsSubgroup(ladder.chain[1],subgroup[i]);
      ladder.isSplitStep[i] := true;
      ladder.isFuseStep[i] := false;
    elif IsSubset(subgroup[i],subgroup[i-1]) then
      ladder.chain[i] := AsSubgroup(ladder.chain[1],subgroup[i]);
      ladder.isSplitStep[i] := false;
      ladder.isFuseStep[i] := true;
    else
      Error("Entry ",i," in the grouplist is neither a subgroup of the group on position ",i-1,", nor the other way round\n"); 
    fi;
  fi;
end;



StroLLBuildIntersectionChain := function(ladder,i)
  local intersection, U, transv, homAct, pos, V;
  if i = 1 then
    ladder.intersectionChain := [ladder.chain[1]];
  else
    intersection := ladder.intersectionChain;
    if ladder.isFuseStep[i] then
      # group[i-1] is a subgroup of group[i]
      intersection[i] := intersection[i-1];
      U := intersection[i];
      ladder.pathTransversal[i] := RightTransversal(U,U);   
    else
      # group[i] is a subgroup of group[i-1];
      transv := RightTransversal(ladder.chain[i-1],ladder.chain[i]);
      homAct := function(x,h)
        return PositionCanonical(transv,transv[x]*h);
      end;
      pos := PositionCanonical(transv,ladder.one);
      intersection[i] := Stabilizer(intersection[i-1],pos,homAct);
      U := intersection[i-1];
      V := intersection[i];
      ladder.pathTransversal[i] := RightTransversal(U,V);   
    fi;
  fi;
end;


StroLLIntersectionMatrix := function(ladder,i)
  local chain, one, intersection, p, transv, homAct, pos, group, j;
  chain := ladder.chain;
  if i = 1 then
    ladder.intersection := [[chain[1]]];
  else
    one := ladder.one;
    intersection := ladder.intersection;
    intersection[i] := [];
    intersection[i][i] := chain[i];
    intersection[1][i] := chain[i];
    intersection[i][1] := chain[i];
    for j in [2 .. i-1] do
      if ladder.isFuseStep[j] and ladder.isFuseStep[i] then
        # group[i-1] is a subgroup of group[i] and 
        # group[j-1] is a subgroup of group[j]
        # intersection[i][j] := intersection[i][j-1];
        # p := StroLLSmallestPathToCoset(one,j,ladder);
        # Print("\nIn StrollIntersectionMatrix FuseStep ",i," ",j);
        # orbAndStab := rec(C := intersection[i]);
        # BlockStabilizerReinitialize(p,j,orbAndStab,ladder);
        # StroLLLightFuseCanonicalDCReps(j, p, orbAndStab, ladder);
        # group := intersection[i][j];
        intersection[i][j] := Intersection(chain[j],chain[i]);
        intersection[j][i] := intersection[i][j];
        # if group <> intersection[i][j] then
        #   Print("\nStroLLLightFuseCanonicalDCReps(j-1):\n",intersection[i][j-1]);
        #   Print("\nStroLLLightFuseCanonicalDCReps(j):\n",intersection[i][j]);
        #   Print("\nIntersection:\n",group);
        #   Error("\nhier in StroLLIntersectionMatrix passt doch was nicht\n");
        # fi;
      elif ladder.isSplitStep[i] then
        # group[i] is a subgroup of group[i-1];
        transv := RightTransversal(ladder.chain[i-1],ladder.chain[i]);
        homAct := function(x,h)
          return PositionCanonical(transv,transv[x]*h);
        end;
        pos := PositionCanonical(transv,one);
        group := intersection[i-1][j];
        intersection[i][j] := Stabilizer(group,pos,homAct);
        intersection[j][i] := intersection[i][j];
      else
        # group[j] is a subgroup of group[j-1]
        transv := RightTransversal(ladder.chain[j-1],ladder.chain[j]);
        homAct := function(x,h)
          return PositionCanonical(transv,transv[x]*h);
        end;
        pos := PositionCanonical(transv,one);
        group := intersection[i][j-1];
        intersection[i][j] := Stabilizer(group,pos,homAct);
        intersection[j][i] := intersection[i][j];
      fi;
    od;
  fi;
end;


# Given a strong subgroupladder (U_1,...,U_n) a record of several 
# structures related to this subgroupladder is returned. 
# The components of the record are:
#   G:
#     record.G is equal to U_1, the first group in the subgroup ladder.
#   chain:
#     record.chain is a list of size n: For all i<=n chain[i] is
#     equal to U_i, the i-th group in the subgroup ladder.
#   transversal:
#     record.transversal is a list of size n: Each entry of this list
#     is itself a list of coset representatives. 
#     If A_i <= A_{i-1} then transversal[i] is a list of representatives 
#     for the set A_i/A_{i-1} of right cosets;
#     If A_i >= A_{i-1} then transversal[i] is a list of representatives 
#     for the set U_i/U_{i-1} of right cosets;
#   subgroupIndex:
#     record.subgroupIndex is a list of size n:
#     For all i<n subgroupIndex[i] is equal to the subgroup index |G:A_i| 
#   intersection:
##  #     record.intersection is a square matrix of size n:
#     For all i,j intersection[i][j] is equal to the intersection of the
#     groups U_i and U_j.
#   homomorphism:
#     If A_i <= A_{i-1} then hom[i] is the action of the group A[i-1] on the
#     cosets of group A_i
#     If A_{i-1} <= A_i then hom[i] is the action of the group A[i] on the
#     cosets of group A_{i-1}
#   rightcosets:
#     If A_i <= A_{i-1} then rightcosets[i] stores the rightcosets 
#     of A_i in A_{i-1} 
#     If A_{i-1} <= A_i then rightcosets[i] stores the rightcosets 
#     of A_{i-1} in A_i 
StroLLBuildTransversal := function(ladder,i)
  local chain, U, V, tmp, pos, j;
  chain := ladder.chain;
  if i = 1 then
    ladder.transversal := [RightTransversal(ladder.G,ladder.G)];
    ladder.rightcosets := [RightCosets(ladder.G,ladder.G)];
    ladder.representativeMap := [];
    ladder.transvOnePos := [1];
  else
    if ladder.isFuseStep[i] then
      # group[i-1] is a subgroup of group[i]
      U := chain[i];
      V := chain[i-1];
      ladder.subgroupIndex[i] := ladder.subgroupIndex[i-1]/IndexNC(U,V);
      ladder.transversal[i] := RightTransversal(U,V);
    else
      # group[i] is a subgroup of group[i-1];
      U := chain[i-1];
      V := chain[i];
      ladder.subgroupIndex[i] := ladder.subgroupIndex[i-1]*IndexNC(U,V);
      ladder.transversal[i] := RightTransversal(U,V);
      ladder.representativeMap[i] := [];
      for j in [1..Size(ladder.pathTransversal[i])] do
        tmp := ladder.pathTransversal[i][j];
        pos := PositionCanonical(ladder.transversal[i],tmp); 
        ladder.representativeMap[i][pos] := j;
      od;
    fi;
    ladder.rightcosets[i] := RightCosets(U,V);
    ladder.hom[i] := FactorCosetAction(U,V);
    ladder.transvOnePos[i] := PositionCanonical(ladder.transversal[i],ladder.one);
  fi;
end;


StroLLBuildSubladder := function(ladder,i)
  local cut, split, pos, h, j, U, V;
  if i = 1 then
    ladder.cut1toI := [ladder.chain[1]];
    ladder.cut1toJplusI := [[ladder.chain[1]]];
    ladder.splitTransversal := [];
    ladder.preimage := [];
  else
    # cut1tojplusi[i][j] = A_1 \cap .. \cap A_j \cap A_i;
    cut := [ladder.chain[i]];
    split := []; 
    ladder.preimage[i] := [];
    for j in [ 2 .. i ] do
      ladder.preimage[i][j] := [];
      if ladder.subgroupIndex[j-1] < ladder.subgroupIndex[j] then
        cut[j] := Intersection(ladder.chain[j],cut[j-1]);
        U := ladder.intersection[i][j-1];
        V := ladder.intersection[i][j];
        split[j] := RightTransversal(U,V);
        for h in split[j] do
          pos := PositionCanonical(ladder.transversal[j],h);
          Append(ladder.preimage[i][j],[pos]);
        od;
      else
        cut[j] := cut[j-1];
        U := ladder.intersection[i][j];
        V := ladder.intersection[i][j-1];
        split[j] := RightTransversal(U,V);
        for h in split[j] do
          pos := PositionCanonical(ladder.transversal[j],h);
          Append(ladder.preimage[i][j],[pos]);
        od;
      fi;
    od;
    ladder.cut1toI[i] := cut[i];
    ladder.cut1toJplusI[i] := cut; 
    ladder.splitTransversal[i] := split;
  fi;
end;


StroLLBuildLadder := function(groups)
  local n, ladder, i;
  n := Size(groups);
  ladder := rec();
  StrongLadderInit(groups,ladder);
  for i in [ 1 .. n ] do
    StroLLCheckSubgroupChain(ladder,groups,i);
    StroLLIntersectionMatrix(ladder,i);
    StroLLBuildIntersectionChain(ladder,i);
    StroLLBuildTransversal(ladder,i);
    StroLLBuildSubladder(ladder,i);
  od;
  Print("\nLadder is now ready!\n");
  return ladder;
end;








