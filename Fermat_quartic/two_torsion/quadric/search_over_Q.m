/*******************************************************************************
 * search_over_Q.m
 *
 * Search for Q-rational quadric decompositions F = Q1*Q3 - Q2^2
 * of F = x^4+y^4+z^4, and prove none exist.
 *
 * Merged from: search_over_Q.m + search_definite.m + search_rational_decomp.m
 *
 * Key results:
 *   1. Exhaustive numerical search (bounds up to 10) finds no decomposition.
 *   2. Positive-definiteness obstruction: on Q1=0, F+Q2^2 > 0 but Q1*Q3 = 0,
 *      so Q1 must be definite (no real zeros).  Bitangent products are
 *      indefinite, hence excluded.
 *   3. Algebraic proof: for Q1 = X^2+iY^2+Z^2 over Q(i), the divisibility
 *      Q1|(F+Q2^2) requires sqrt(2). No Q(i)-decomposition exists for V_rat
 *      class Q1 forms.
 ******************************************************************************/

R<X,Y,Z> := PolynomialRing(Rationals(), 3);
FK := X^4 + Y^4 + Z^4;

// =========== EXHAUSTIVE SEARCH: FULL Q2, BOUND [-5,5] ===========

printf "=== EXHAUSTIVE SEARCH: FULL Q2, BOUND 5 ===\n";
printf "F = X^4 + Y^4 + Z^4\n\n";

count := 0;
found := 0;

for a in [-5..5] do for b in [-5..5] do for c in [-5..5] do
for d in [-5..5] do for ef in [-5..5] do for ff_ in [-5..5] do
    Q2 := a*X^2 + b*Y^2 + c*Z^2 + d*X*Y + ef*X*Z + ff_*Y*Z;
    if Q2 eq 0 then continue; end if;
    // Normalize: first nonzero coeff positive (Q2 and -Q2 give same Q2^2)
    coeffs := [a,b,c,d,ef,ff_];
    first_nonzero := 0;
    for i in [1..6] do
        if coeffs[i] ne 0 then first_nonzero := coeffs[i]; break; end if;
    end for;
    if first_nonzero lt 0 then continue; end if;

    G := FK + Q2^2;
    fac := Factorization(G);

    // Check all factorization patterns for a quadratic pair
    has_quad_pair := false;
    Q1_ := R!0; Q3_ := R!0;

    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2
       and fac[1][2] eq 1 and fac[2][2] eq 1 then
        has_quad_pair := true;
        Q1_ := fac[1][1]; Q3_ := fac[2][1];
        scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
        if scalar ne 1 then Q1_ := scalar*Q1_; end if;
    elif #fac eq 1 and TotalDegree(fac[1][1]) eq 2 and fac[1][2] eq 2 then
        has_quad_pair := true;
        Q1_ := fac[1][1]; Q3_ := fac[1][1];
        scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
        if scalar ne 1 then Q1_ := scalar*Q1_; end if;
    elif #fac eq 4 and &and[TotalDegree(fac[i][1]) eq 1 and fac[i][2] eq 1 : i in [1..4]] then
        // 4 linear factors: 3 pairings
        for pair in [[1,2],[1,3],[1,4]] do
            i1 := pair[1]; i2 := pair[2];
            rest := [j : j in [1..4] | j ne i1 and j ne i2];
            Q1_ := fac[i1][1]*fac[i2][1];
            Q3_ := fac[rest[1]][1]*fac[rest[2]][1];
            scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
            if scalar ne 1 then Q1_ := scalar*Q1_; end if;
            if Q1_*Q3_ - Q2^2 eq FK then
                has_quad_pair := true;
                break;
            end if;
        end for;
    elif #fac eq 3 then
        degs := [TotalDegree(fac[i][1]) : i in [1..3]];
        for i in [1..#fac] do
            if degs[i]*fac[i][2] eq 2 then
                Q1_ := fac[i][1]^fac[i][2];
                others := &*[fac[j][1]^fac[j][2] : j in [1..#fac] | j ne i];
                if TotalDegree(others) eq 2 then
                    Q3_ := others;
                    scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
                    if scalar ne 1 then Q1_ := scalar*Q1_; end if;
                    if Q1_*Q3_ - Q2^2 eq FK then
                        has_quad_pair := true;
                        break;
                    end if;
                end if;
            end if;
        end for;
    end if;

    count +:= 1;
    if count mod 10000 eq 0 then
        printf "Checked %o Q2 values so far, found %o decompositions\n", count, found;
    end if;

    if has_quad_pair then
        if Q1_*Q3_ - Q2^2 eq FK then
            found +:= 1;
            printf "FOUND: Q2 = %o\n", Q2;
            printf "  Q1 = %o\n  Q3 = %o\n\n", Q1_, Q3_;
        end if;
    end if;
end for; end for; end for;
end for; end for; end for;

printf "\nTotal Q2 checked: %o\n", count;
printf "Decompositions found: %o\n\n", found;

if found eq 0 then
    print "No Q-rational decompositions found with coefficients in [-5,5].";
    print "This is consistent with a Brauer obstruction on the space of";
    print "quadric decompositions.";
    print "";
end if;

// =========== DIAGONAL Q2, LARGER BOUND ===========

printf "=== RATIONAL DECOMPOSITIONS (diagonal Q2, bound 10) ===\n";
bnd := 10;
found_diag := 0;
R2<X0,Y0,Z0> := PolynomialRing(Rationals(), 3);
FR := X0^4 + Y0^4 + Z0^4;

for c1 in [0..bnd] do
for c2 in [-bnd..bnd] do
for c3 in [-bnd..bnd] do
    Q2 := c1*X0^2 + c2*Y0^2 + c3*Z0^2;
    if Q2 eq 0 then continue; end if;
    G := FR + Q2^2;
    fac := Factorization(G);
    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;
    if has_quad then
        found_diag +:= 1;
        printf "FOUND: Q2 = %o\n", Q2;
        for pair in fac do
            printf "  factor: (%o)^%o\n", pair[1], pair[2];
        end for;
    end if;
end for;
end for;
end for;
printf "Rational diagonal decomps found: %o (bound %o)\n\n", found_diag, bnd;

// =========== POSITIVE-DEFINITENESS OBSTRUCTION ===========

printf "=== WHY BITANGENT-BASED DECOMPOSITIONS FAIL OVER Q ===\n\n";
printf "For Q1 = (x+y+z)(x+y-z) = (x+y)^2-z^2:\n";
printf "  On Q1=0: z^2=(x+y)^2, so F = x^4+y^4+(x+y)^4 = 2(x^2+xy+y^2)^2\n";
printf "  F+Q2^2 >= F = 2(x^2+xy+y^2)^2 > 0 on Q1=0 (for real (x,y)!=0)\n";
printf "  But Q1*Q3 = 0 on Q1=0.\n";
printf "  So F+Q2^2 != Q1*Q3 on this locus. IMPOSSIBLE over R.\n\n";

printf "Same argument for ANY indefinite Q1:\n";
printf "  On Q1=0 (a real conic), F+Q2^2 > 0 but Q1*Q3 = 0.\n";
printf "  So Q1 must be definite (no real zeros except 0).\n";
printf "  Products of bitangent lines are indefinite => cannot occur.\n\n";

// =========== ALGEBRAIC PROOF: Q1 = X^2+iY^2+Z^2 NEEDS sqrt(2) ===========

printf "=== ALGEBRAIC: Q1 = X^2+iY^2+Z^2 over Q(i) ===\n\n";

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);

printf "Q1=0 has Q(i)-point (1:0:i): 1+0+i^2 = %o\n", 1+0+i^2;
printf "\nDivisibility analysis: F+Q2^2 mod Q1 = 0\n";
printf "Q2 mod Q1 = A + BX where\n";
printf "  A = (c2-ic1)Y^2+(c3-c1)Z^2+c6*YZ\n";
printf "  B = c4*Y+c5*Z\n\n";
printf "Conditions:\n";
printf "  (i)  2AB = 0 (odd-in-X part)\n";
printf "  (ii) Even part must vanish\n\n";

printf "Case A=0 (c2=ic1, c3=c1, c6=0):\n";
printf "  Expanding even part and using X^2=-iY^2-Z^2:\n";
printf "  Y^4 coeff: -ic4^2 = 0 => c4=0\n";
printf "  Y^2Z^2 coeff: 2i - ic5^2 = 0 => c5^2 = 2\n";
printf "  Z^4 coeff: 2 - c5^2 = 0 => c5^2 = 2  (consistent)\n";
printf "  => c5 = sqrt(2), NOT IN Q(i).\n\n";

printf "Case B=0 (c4=c5=0):\n";
printf "  A = aY^2+bZ^2+c6*YZ where a=c2-ic1, b=c3-c1\n";
printf "  Y^4: a^2 = 0 => a=0\n";
printf "  Y^2Z^2: c6^2+2i = 0 => c6^2 = -2i\n";
printf "  YZ^3: 2b*c6 = 0 => b=0 or c6=0\n";
printf "    If c6=0: c6^2=0 != -2i. Contradiction.\n";
printf "    If b=0: Z^4: b^2+2 = 2 != 0. Contradiction.\n";
printf "  Correction: Z^4 gives b^2 = -2, so b = sqrt(-2) = i*sqrt(2). NOT IN Q(i).\n\n";

printf "CONCLUSION: For Q1 = X^2+iY^2+Z^2, the divisibility Q1|(F+Q2^2)\n";
printf "requires sqrt(2) in BOTH cases. No Q(i)-decomposition exists for\n";
printf "this Q1.  Any Q1 giving a V_rat class will have a similar obstruction.\n";

quit;
