
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
    if IsSubset(subgroup[i],subgroup[i-1]) then
      ladder.chain[i] := AsSubgroup(ladder.chain[1],subgroup[i]);
      ladder.isSplitStep[i] := false;
      ladder.isFuseStep[i] := true;
    elif IsSubset(subgroup[i-1],subgroup[i]) then
      ladder.chain[i] := AsSubgroup(ladder.chain[1],subgroup[i]);
      ladder.isSplitStep[i] := true;
      ladder.isFuseStep[i] := false;
    else
      Error("Entry ",i," in the grouplist is neither a subgroup of the group on position ",i-1,", nor the other way round\n"); 
    fi;
  fi;
end;



StroLLBuildIntersectionChain := function(ladder,i)
  local intersection, U, V;
  if i = 1 then
    ladder.intersectionChain := [ladder.chain[1]];
  else
    intersection := ladder.intersectionChain;
    if ladder.isFuseStep[i] then
      # group[i-1] is a subgroup of group[i]
      intersection[i] := intersection[i-1];
      U := intersection[i];
      V := intersection[i-1];
    else
      # group[i] is a subgroup of group[i-1];
      intersection[i] := Intersection(intersection[i-1],ladder.chain[i]);
      U := intersection[i-1];
      V := intersection[i];
    fi;
    ladder.pathTransversal[i] := RightTransversal(U,V);   
  fi;
end;


StroLLIntersectionMatrix := function(ladder,i)
  local chain, tmp, j;
  chain := ladder.chain;
  if i = 1 then
    ladder.intersection := [[chain[1]]];
  else
    ladder.intersection[i] := [];
    ladder.intersection[i][i] := chain[i];
    ladder.intersection[1][i] := chain[i];
    ladder.intersection[i][1] := chain[i];
    for j in [2 .. i-1] do
      if true = IsSubgroup(chain[i],chain[i-1]) then
        # group[i-1] is a subgroup of group[i]
        ladder.intersection[i][j] := Intersection(chain[j],chain[i]);
        ladder.intersection[j][i] := ladder.intersection[i][j];
      elif true = IsSubgroup(chain[i-1],chain[i]) then
        # group[i] is a subgroup of group[i-1];
        tmp := ladder.intersection[i-1][j];
        ladder.intersection[i][j] := Intersection(tmp,chain[i]);
        ladder.intersection[j][i] := ladder.intersection[i][j];
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
  local U, V, tmp, pos, j;
  if i = 1 then
    ladder.transversal := [];
    ladder.transversal[1] := RightTransversal(ladder.G,ladder.G);
    ladder.rightcosets := [];
    ladder.rightcosets[1] := RightCosets(ladder.G,ladder.G);
    ladder.representativeMap := [];
  else
    if ladder.isFuseStep[i] then
      # group[i-1] is a subgroup of group[i]
      U := ladder.chain[i];
      V := ladder.chain[i-1];
      ladder.subgroupIndex[i] := ladder.subgroupIndex[i-1]/IndexNC(U,V);
      ladder.transversal[i] := RightTransversal(U,V);
    else
      # group[i] is a subgroup of group[i-1];
      U := ladder.chain[i-1];
      V := ladder.chain[i];
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
    if not 1 = PositionCanonical(ladder.transversal[i],ladder.one) then
      Error("Assumption on the transversal is not fulfilled");
    fi;
  fi;
end;


StroLLBuildSubladder := function(ladder)
  local cut, split, pos, h, i, j, U, V;
  ladder.cut1toI := [ladder.chain[1]];
  ladder.cut1toJplusI := [[ladder.chain[1]]];
  ladder.splitTransversal := [];
  ladder.preimage := [];
  for i in [ 2 .. Size(ladder.chain) ] do
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
  od;
end;


StroLLBuildLadder := function(groups)
  local n, ladder;
  n := Size(groups);
  ladder := rec();
  StrongLadderInit(groups,ladder);
  for i in [ 1 .. n ] do
    StroLLCheckSubgroupChain(ladder,groups,i);
    StroLLIntersectionMatrix(ladder,i);
    StroLLBuildIntersectionChain(ladder,i);
    StroLLBuildTransversal(ladder,i);
  od;
  # BuildStroLLTransversalCompare(ladder);
  StroLLBuildSubladder(ladder);
  ladder.SmallestPathToCoset := [];
  return ladder;
end;








