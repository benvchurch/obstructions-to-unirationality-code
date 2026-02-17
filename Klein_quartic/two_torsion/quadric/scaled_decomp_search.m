/*******************************************************************************
 * scaled_decomp_search.m
 *
 * Search for F = lambda * (Q1*Q3 - Q2^2) with rational Q1,Q2,Q3 and lambda.
 * Equivalently: Q1*Q3 = Q2^2 + c*F  for rational c = 1/lambda.
 * Factor Q2^2 + c*F over Q for various Q2 and c.
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

mons2 := [x^2, y^2, z^2, x*y, x*z, y*z];

printf "=== SCALED DECOMPOSITION SEARCH ===\n";
printf "Looking for Q1*Q3 = Q2^2 + c*F with rational Q1,Q2,Q3,c\n\n";

found := 0;

// Rational c values to try: n/d for small n,d
c_vals := [];
for d in [1..6] do
for n in [-12..12] do
    if n eq 0 then continue; end if;
    if GCD(Abs(n), d) ne 1 then continue; end if;
    Append(~c_vals, n/d);
end for;
end for;
printf "Testing %o values of c\n\n", #c_vals;

// =========================================================================
// Phase 1: Q2 with coefficients in {-2..2} on all 6 monomials
// =========================================================================
printf "--- Phase 1: General Q2, bound 2 ---\n";
count := 0;
for a1 in [-2..2] do
for a2 in [a1..2] do  // use a1<=a2 by x<->y symmetry when a4=0
for a3 in [-2..2] do
for a4 in [-2..2] do
for a5 in [-2..2] do
for a6 in [-2..2] do
    coeffs := [a1,a2,a3,a4,a5,a6];
    if coeffs eq [0,0,0,0,0,0] then continue; end if;

    // Skip if first nonzero coeff is negative (overall sign doesn't matter for Q2^2)
    first_nz := 0;
    for k in [1..6] do
        if coeffs[k] ne 0 then first_nz := k; break; end if;
    end for;
    if coeffs[first_nz] lt 0 then continue; end if;

    Q2 := &+[coeffs[k] * mons2[k] : k in [1..6]];
    Q2sq := Q2^2;

    for c in c_vals do
        G := Q2sq + c * F;
        fac := Factorization(G);

        // Check: does G factor into exactly two quadrics?
        if #fac ge 2 then
            degs := [TotalDegree(fac[k][1]) : k in [1..#fac]];
            mults := [fac[k][2] : k in [1..#fac]];
            if #fac eq 2 and degs[1] eq 2 and degs[2] eq 2
               and mults[1] eq 1 and mults[2] eq 1 then
                found +:= 1;
                Q1 := fac[1][1]; Q3 := fac[2][1];
                printf "FOUND #%o: c = %o, Q2 = %o\n", found, c, Q2;
                printf "  Q1 = %o\n  Q3 = %o\n", Q1, Q3;
                printf "  Verify: Q1*Q3 - Q2^2 = %o * F? %o\n\n",
                    c, Q1*Q3 - Q2^2 eq c*F;
            end if;
        end if;
        // Also check perfect square
        if #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
            found +:= 1;
            Q1 := fac[1][1];
            printf "FOUND #%o (square): c = %o, Q2 = %o\n", found, c, Q2;
            printf "  Q1 = Q3 = %o\n", Q1;
            printf "  Verify: Q1^2 - Q2^2 = %o * F? %o\n\n",
                c, Q1^2 - Q2^2 eq c*F;
        end if;
    end for;

    count +:= 1;
end for;
end for;
end for;
end for;
end for;
end for;
printf "Phase 1: tested %o Q2 forms, found %o decompositions\n\n", count, found;

// =========================================================================
// Phase 2: Diagonal Q2 with larger bound, more c values
// =========================================================================
printf "--- Phase 2: Diagonal Q2, bound 5 ---\n";
found2 := 0;
count2 := 0;
for a in [0..5] do
for b in [a..5] do  // a<=b by symmetry
for d in [-5..5] do
    if [a,b,d] eq [0,0,0] then continue; end if;
    Q2 := a*x^2 + b*y^2 + d*z^2;
    Q2sq := Q2^2;

    for c in c_vals do
        G := Q2sq + c * F;
        fac := Factorization(G);
        if #fac ge 2 then
            degs := [TotalDegree(fac[k][1]) : k in [1..#fac]];
            mults := [fac[k][2] : k in [1..#fac]];
            if #fac eq 2 and degs[1] eq 2 and degs[2] eq 2
               and mults[1] eq 1 and mults[2] eq 1 then
                found2 +:= 1;
                Q1 := fac[1][1]; Q3 := fac[2][1];
                printf "FOUND #%o: c=%o, Q2=%o, Q1=%o, Q3=%o\n",
                    found2, c, Q2, Q1, Q3;
                printf "  Verify: %o\n", Q1*Q3-Q2^2 eq c*F;
            end if;
        end if;
        if #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
            found2 +:= 1;
            printf "FOUND #%o (sq): c=%o, Q2=%o, Q1=Q3=%o\n",
                found2, c, Q2, fac[1][1];
        end if;
    end for;
    count2 +:= 1;
end for;
end for;
end for;
printf "Phase 2: tested %o diagonal Q2, found %o\n\n", count2, found2;

printf "=== TOTAL: %o decompositions found ===\n", found + found2;

quit;
