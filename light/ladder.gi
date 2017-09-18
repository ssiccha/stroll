
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
#     For all i < n let V_i denote the intersection of the groups A_1 to A_i.
#     If A_i <= A_{i+1} then transversal[i] is a list of representatives 
#     for the set A_i/A_{i+1} of right cosets;
#     If A_i >= A_{i+1} then transversal[i] is a list of representatives 
#     for the set U_i/U_{i+1} of right cosets;
#   subgroupIndex:
#     record.subgroupIndex is a list of size n:
#     For all i<n subgroupIndex[i] is equal to the subgroup index |G:A_i| 
#   intersection:
#     record.intersection is a list of size n:
#     For all i<n intersection[i] is equal to the intersection of the
#     groups U_1 to U_i.
StroLLBuildTransversal := function(subgroup)
  local one, ladder, U, V, i;
  one := One(subgroup[1]);
  ladder := rec();
  ladder.G := subgroup[1];
  ladder.chain := [subgroup[1]]; 
  ladder.subgroupIndex := [1];
  ladder.transversal := [RightTransversal(ladder.G,ladder.G)];
  ladder.rightcosets := [RightCosets(ladder.G,ladder.G)];
  ladder.hom := [];
  for i in [2 .. Size(subgroup)] do
    ladder.chain[i] := subgroup[i];
    if true = IsSubgroup(subgroup[i],subgroup[i-1]) then
      # group[i-1] is a subgroup of group[i]
      U := subgroup[i];
      V := subgroup[i-1];
      ladder.subgroupIndex[i] := ladder.subgroupIndex[i-1]/IndexNC(U,V);
    elif true = IsSubgroup(subgroup[i-1],subgroup[i]) then
      # group[i] is a subgroup of group[i-1];
      U := subgroup[i-1];
      V := subgroup[i];
      ladder.subgroupIndex[i] := ladder.subgroupIndex[i-1]*IndexNC(U,V);
    else
      Error("Entry ",i," in the grouplist is neither a subgroup of the group on position ",i-1,", nor the other way round\n"); 
      return;
    fi;
    ladder.rightcosets[i] := RightCosets(U,V);
    ladder.hom[i] := FactorCosetAction(U,V);
    ladder.transversal[i] := RightTransversal(U,V);
    if not 1 = PositionCanonical(ladder.transversal[i],one) then
      Error("Assumption on the transversal is not fulfilled");
    fi;
  od;
  return ladder;
end;




StroLLBuildSubladder := function(ladder)
  local cut, split, i, j;
  ladder.cut1toI := [ladder.chain[1]];
  ladder.cut1toJplusI := [[ladder.chain[1]]];
  ladder.splitTransversal := [];
  for i in [ 2 .. Size(ladder.chain) ] do
    # cut1tojplusi[i][j] = A_1 \cap .. \cap A_j \cap A_i;
    cut := [ladder.chain[i]];
    split := []; 
    for j in [ 2 .. i ] do
      if ladder.subgroupIndex[j-1] < ladder.subgroupIndex[j] then
        cut[j] := Intersection(ladder.chain[j],cut[j-1]);
        split[j] := RightTransversal(cut[j-1],cut[j]);
      else
        cut[j] := cut[j-1];
      fi;
    od;
    ladder.cut1toI[i] := cut[i];
    ladder.cut1toJplusI[i] := cut; 
    ladder.splitTransversal[i] := split;
  od;
end;


StroLLBuildLadder := function(groups)
  local ladder;
  ladder := StroLLBuildTransversal(groups);
  # BuildStroLLTransversalCompare(ladder);
  StroLLBuildSubladder(ladder);
  return ladder;
end;








