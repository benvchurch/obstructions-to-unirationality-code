/*******************************************************************************
 * Q2_general_search.m
 *
 * Search for rational decompositions F = Q1*Q3 - Q2^2 of x^4+y^4+z^4
 * by trying general Q2 with small rational coefficients and factoring
 * G = F + Q2^2 over Q.
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

mons := [x^2, y^2, z^2, x*y, x*z, y*z];
mon_names := ["x^2", "y^2", "z^2", "xy", "xz", "yz"];

printf "=== GENERAL Q2 SEARCH: F + Q2^2 FACTORS INTO TWO QUADRICS? ===\n\n";

bnd := 3;
found := 0;
tested := 0;

// Search over all Q2 = sum a_i * m_i with |a_i| <= bnd
// Use symmetry: can assume first nonzero coefficient is positive
for a1 in [0..bnd] do
for a2 in [-bnd..bnd] do
for a3 in [-bnd..bnd] do
for a4 in [-bnd..bnd] do
for a5 in [-bnd..bnd] do
for a6 in [-bnd..bnd] do
    coeffs := [a1, a2, a3, a4, a5, a6];
    if coeffs eq [0,0,0,0,0,0] then continue; end if;

    // Symmetry: first nonzero coeff positive
    first_nz := 0;
    for k in [1..6] do
        if coeffs[k] ne 0 then first_nz := k; break; end if;
    end for;
    if coeffs[first_nz] lt 0 then continue; end if;

    Q2 := &+[coeffs[k] * mons[k] : k in [1..6]];
    G := F + Q2^2;

    tested +:= 1;

    fac := Factorization(G);

    // Check for factorization into two quadrics (possibly with multiplicity)
    has_decomp := false;
    for k in [1..#fac] do
        if TotalDegree(fac[k][1]) eq 2 then
            has_decomp := true;
            Q1 := fac[k][1];
            Q3_full := G div (Q1^fac[k][2]);
            // Check remaining factor
            if fac[k][2] eq 1 then
                // Q1 * (remaining) = G, remaining should be degree 2
                remaining := G div Q1;
                if TotalDegree(remaining) eq 2 then
                    found +:= 1;
                    printf "FOUND #%o: Q2 = %o\n", found, Q2;
                    printf "  G = Q1 * Q3 with Q1 = %o, Q3 = %o\n", Q1, remaining;
                    printf "  Verify: Q1*Q3 - Q2^2 = F? %o\n\n", Q1*remaining - Q2^2 eq F;
                end if;
            elif fac[k][2] eq 2 then
                // Perfect square: G = c*(Q1)^2
                found +:= 1;
                printf "FOUND #%o: Q2 = %o\n", found, Q2;
                printf "  G = (%o)^2\n", Q1;
                printf "  F = Q1^2 - Q2^2 = (Q1-Q2)(Q1+Q2)\n\n";
            end if;
            break;
        end if;
    end for;
end for;
end for;
end for;
end for;
end for;
end for;

printf "Tested %o forms, found %o decompositions (bound %o)\n\n", tested, found, bnd;

// =========================================================================
// Also try Q2 = a/b * monomial with small denominators
// =========================================================================
printf "=== HALF-INTEGER COEFFICIENTS ===\n";
found2 := 0;
for a1 in [-4..4] do
for a2 in [-4..4] do
for a3 in [-4..4] do
    Q2 := (a1/2)*x^2 + (a2/2)*y^2 + (a3/2)*z^2;
    if Q2 eq 0 then continue; end if;
    G := F + Q2^2;
    fac := Factorization(G);
    for k in [1..#fac] do
        if TotalDegree(fac[k][1]) eq 2 and fac[k][2] eq 1 then
            remaining := G div fac[k][1];
            if TotalDegree(remaining) eq 2 then
                found2 +:= 1;
                printf "FOUND: Q2 = %o, Q1 = %o, Q3 = %o\n", Q2, fac[k][1], remaining;
                printf "  Verify: %o\n", fac[k][1]*remaining - Q2^2 eq F;
            end if;
        end if;
    end for;
end for;
end for;
end for;
printf "Half-integer diagonal: %o found\n", found2;

quit;
