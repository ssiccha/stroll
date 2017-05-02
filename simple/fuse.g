## leiterspiel-light, fuse: vgl S.133
## FUSE: A_i <= A_i+1
##  E_i  :=  A_i intersect A_k
## E_i+1 := A_i+1 intersect A_k
##
##                \varphi
##      E_i \ G   ------>   E_i+1 \ G
##
##          |                   |  
##          |                   |  
##       \psi_i               \psi_i+1
##          |                   |  
##          V                   V
##                 \nu
##      A_i \ G  ------->   A_i+1 \ G                

## cosetRep is a representative of a coset E_i*e in E_i \ G
## oldCanonizer maps A_i*e to the canonical A_i-coset A_i*e*b of its B-orbit
## oldC is the stabilizer of the canonical A_i-coset A_i*e*b in B
## C is the stabilizer of the canonical A_i+1-coset A_i+1*e*b in B,
##   operating on the preimages of A_i+1*e*b
## Calls NextStep, if the coset E_i*e is the canonical representative of its C^(b^-1)-orbit
fuseLight := function( cosetRep, oldCanonizer, oldC, C )
  local minimalPreimageRep;
  # fusing step is trivial
  if oldC = C then
    NextStep(cosetRep,oldCanonizer);
  else
    # check, whether cosetRep is the minimal representative in its C^(b^-1)-orbit
    minimalPreimageRep := cosetRep * FindOrbitRepConjugate(cosetRep, C, oldCanonizer);
    if cosetRep = minimalPreimageRep then
        NextStep(cosetRep, oldCanonizer);
    fi;
  fi;
end;
