/*******************************************************************************
 * search_rational_decomp.m
 *
 * Search for RATIONAL quadric decompositions F = Q1*Q3 - Q2^2 of
 * F = X^4+Y^4+Z^4, and classify the J[2] class of each.
 *
 * Key question: do decompositions over Q exist? Over Q, F is positive
 * definite (on R^3), so Q1*Q3 = F+Q2^2 > 0 generically, constraining Q1,Q3.
 ******************************************************************************/

R<X,Y,Z> := PolynomialRing(Rationals(), 3);
FK := X^4 + Y^4 + Z^4;

printf "=== SEARCH FOR RATIONAL QUADRIC DECOMPOSITIONS ===\n";
printf "F = X^4 + Y^4 + Z^4\n\n";

// Q2 = c1*X^2 + c2*Y^2 + c3*Z^2 + c4*XY + c5*XZ + c6*YZ
// with c_j in [-bnd..bnd]
bnd := 3;
found := 0;

for c1 in [-bnd..bnd] do
for c2 in [-bnd..bnd] do
for c3 in [-bnd..bnd] do
for c4 in [-bnd..bnd] do
for c5 in [-bnd..bnd] do
for c6 in [-bnd..bnd] do
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2 + c4*X*Y + c5*X*Z + c6*Y*Z;
    if Q2 eq 0 then continue; end if;
    // Normalize: skip Q2 and -Q2 duplicates
    coeffs := [c1,c2,c3,c4,c5,c6];
    first_nonzero := 0;
    for j in [1..6] do
        if coeffs[j] ne 0 then first_nonzero := coeffs[j]; break; end if;
    end for;
    if first_nonzero lt 0 then continue; end if;

    G := FK + Q2^2;
    fac := Factorization(G);

    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;

    if has_quad then
        found +:= 1;
        printf "FOUND #%o: Q2 = %o\n", found, Q2;
        for pair in fac do
            printf "  factor: (%o)^%o\n", pair[1], pair[2];
        end for;
        // Check rank of Q1
        if #fac ge 1 then
            Q1 := fac[1][1];
            // Represent Q1 as symmetric matrix
            cQ1 := [MonomialCoefficient(Q1, X^2),
                     MonomialCoefficient(Q1, Y^2),
                     MonomialCoefficient(Q1, Z^2),
                     MonomialCoefficient(Q1, X*Y),
                     MonomialCoefficient(Q1, X*Z),
                     MonomialCoefficient(Q1, Y*Z)];
            M := Matrix(Rationals(), 3, 3,
                [cQ1[1], cQ1[4]/2, cQ1[5]/2,
                 cQ1[4]/2, cQ1[2], cQ1[6]/2,
                 cQ1[5]/2, cQ1[6]/2, cQ1[3]]);
            printf "  Q1 matrix rank = %o, det = %o\n", Rank(M), Determinant(M);
        end if;
        printf "\n";
    end if;
end for;
end for;
end for;
end for;
end for;
end for;

printf "Total decompositions found: %o (Q bound=%o)\n\n", found, bnd;

if found eq 0 then
    printf "No rational decomposition found!\n";
    printf "This is consistent with F being positive-definite over R:\n";
    printf "  Q1*Q3 = F + Q2^2 > 0, constraining Q1,Q3 severely.\n\n";
end if;

// =========================================================================
// Now check: on the variety Q1=0 (a conic), what is F?
// For bitangent product Q1 = (x+y+z)(x+y-z) = (x+y)^2-z^2:
//   F|_{Q1=0} = 2(x^2+xy+y^2)^2 > 0 for real (x,y) != 0
// So F+Q2^2 > 0 on Q1=0, but Q1*Q3 = 0 on Q1=0. Contradiction!
// =========================================================================
printf "=== WHY BITANGENT-BASED DECOMPOSITIONS FAIL OVER Q ===\n\n";
printf "For Q1 = (x+y+z)(x+y-z) = (x+y)^2-z^2:\n";
printf "  On Q1=0: z^2=(x+y)^2, so F = x^4+y^4+(x+y)^4 = 2(x^2+xy+y^2)^2\n";
printf "  F+Q2^2 >= F = 2(x^2+xy+y^2)^2 > 0 on Q1=0 (for real (x,y)!=0)\n";
printf "  But Q1*Q3 = 0 on Q1=0.\n";
printf "  So F+Q2^2 != Q1*Q3 on this locus. IMPOSSIBLE over R.\n\n";

printf "Same argument for ANY indefinite Q1:\n";
printf "  On Q1=0 (a real conic), F+Q2^2 > 0 but Q1*Q3 = 0.\n";
printf "  So Q1 must be definite (no real zeros except 0).\n";
printf "  Products of bitangent lines are indefinite => cannot occur.\n";

quit;
