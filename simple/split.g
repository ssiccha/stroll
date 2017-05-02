## TODO definiere Funktionen
Read("toDeclare.g");

## leiterspiel-light, fuse: vgl S.133
## SPLIT: A_i => A_i+1
##  E_i  :=  A_i intersect A_k
## E_i+1 := A_i+1 intersect A_k
##
##                \varphi
##      E_i+1 \ G   ------>   E_i \ G
##
##          |                   |  
##          |                   |  
##       \psi_i+1             \psi_i
##          |                   |  
##          V                   V
##                 \nu
##      A_i+1 \ G  ------->   A_i \ G                

## e_i is a representative of a coset E_i*e_i in E_i \ G
## b maps E_i*e_i to the canonical E_i-coset E_i*e_i*b of its B-orbit
## C1 stabilizer of A_i+1*e_i*b
## C2 stabilizer of A_i*e_i*b
splitLight := function( e_i, p, b, C1, C2 )
  local c, e;
  ## TODO how?
  ## iterate over all preimages of E_i*e
  for e in phiInverse( e_i ) do
      # splitting step is trivial
      if C1 = C2 then
        c := ();
      else
        c := FindOrbitRep(e*b,C2);
      fi;
      # If A_i*p < A_i*e*b*c, this branch can be pruned
      # TODO changes from E_i cosets to A_i cosets
      if Smaller( p, e*b*c ) then
          continue;
      elif Smaller( e*b*c, p ) then
          foundSmaller( e, b*c );
# place where optimizations and/or extensions can be defined
#      elif not mysteriousTest( e, b*c ) then
#          continue;
      else
          NextStep( e, b*c );
      fi;
  od;
end;
