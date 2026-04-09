/*******************************************************************************
 * search_over_Qi.m
 *
 * Search for quadric decompositions of X^4+Y^4+Z^4 = Q1*Q3 - Q2^2
 * over Q(i).  The Brauer obstruction has invariants at (inf, 2), so
 * Q(i) should kill it — meaning decompositions MUST exist here.
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

print "=== SEARCH FOR QUADRIC DECOMPOSITIONS OVER Q(i) ===";
print "F = X^4 + Y^4 + Z^4";
print "";

// Q2 = c1*X^2 + c2*Y^2 + c3*Z^2 + c4*XY + c5*XZ + c6*YZ
// with c_j = a_j + b_j*i, a_j,b_j in [-bnd..bnd]
// Check if F + Q2^2 factors into two quadrics over K

bnd := 1;
found := 0;
total := 0;

// To avoid duplicates from Q2 and -Q2, normalize:
// require first nonzero coefficient to have positive real part,
// or if real part 0, positive imaginary part

for a1 in [-bnd..bnd] do for b1 in [-bnd..bnd] do
for a2 in [-bnd..bnd] do for b2 in [-bnd..bnd] do
for a3 in [-bnd..bnd] do for b3 in [-bnd..bnd] do
for a4 in [-bnd..bnd] do for b4 in [-bnd..bnd] do
for a5 in [-bnd..bnd] do for b5 in [-bnd..bnd] do
for a6 in [-bnd..bnd] do for b6 in [-bnd..bnd] do
    c1 := a1 + b1*i; c2 := a2 + b2*i; c3 := a3 + b3*i;
    c4 := a4 + b4*i; c5 := a5 + b5*i; c6 := a6 + b6*i;
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2 + c4*X*Y + c5*X*Z + c6*Y*Z;
    if Q2 eq 0 then continue; end if;

    G := FK + Q2^2;
    total +:= 1;
    fac := Factorization(G);

    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;

    if has_quad then
        found +:= 1;
        if found le 30 then
            printf "FOUND #%o: Q2 = %o\n", found, Q2;
            for pair in fac do
                Q1 := pair[1]; exp := pair[2];
                printf "  factor: (%o)^%o\n", Q1, exp;
            end for;
            // Verify
            if #fac eq 2 then
                Q1 := fac[1][1]; Q3 := fac[2][1];
                lc := LeadingCoefficient(G) / LeadingCoefficient(Q1*Q3);
                Q1s := lc * Q1;
                if Q1s*Q3 - Q2^2 eq FK then
                    printf "  VERIFIED: F = Q1*Q3 - Q2^2\n";
                    printf "  Q1 = %o\n  Q3 = %o\n", Q1s, Q3;
                end if;
            end if;
            printf "\n";
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;

printf "\nTotal Q2 tested: %o, decompositions found: %o (bound=%o)\n", total, found, bnd;

quit;
