youngGroup := function( partition )
  local groups, generators;
  partition := List( partition, Set );
  groups := List( partition, SymmetricGroup );
  generators := List( groups, GeneratorsOfGroup );
  return Group( Concatenation( generators ) );
end;
