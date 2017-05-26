ladderTransversals := "";

smallerOrEqual := function( a, b )
  for i in [ 2 .. Length(ladderTransversals) ] do
    positionA := PositionCanonical( ladderTransversals[i], a );
    positionB := PositionCanonical( ladderTransversals[i], b );
    if positionA < positionB then
      return true;
    elif positionB < positionA then
      return false;
    fi;
  od;
  return true;
end;

smaller := function( a, b )
  for i in [ 2 .. Length(ladderTransversals) ] do
    positionA := PositionCanonical( ladderTransversals[i], a );
    positionB := PositionCanonical( ladderTransversals[i], b );
    if positionA < positionB then
      return true;
    elif positionB < positionA then
      return false;
    fi;
  od;
  return false;
end;
