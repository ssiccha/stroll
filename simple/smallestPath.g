# computes the smallest path (A_1*p, ..., A_k*p) with A_k*p = A_k*g;
# k, index
# g, group element
smallestPath := function( k, g )
    # Orbit of A_2*g under Stab( A_k*g )
    coset := RightCoset( A[2], g );
    tmp := OrbitStabilizer( A[k]^g, coset, OnRight );
    stabilizer := tmp.stabilizer;
    orbit := tmp.orbit;
    orbitReps := List(
        orbit,
        x -> CanonicalRightCosetElement( x!.ActingDomain, x!.Representative )
    );
end;
