/*******************************************************************************
 * bitangent_decomp_search.m
 *
 * Search for decompositions l3^2 * l1 * l2 - Q2^2 = lambda * F
 * where F = x^4+y^4+z^4, l1,l2 are bitangent lines, l3 is linear, Q2 quadratic.
 *
 * Strategy:
 *   1. Verify the 4 rational bitangent lines and their contact loci
 *   2. Analyze the restriction to l_i = 0 to find necessary conditions
 *   3. Search for decompositions over Q
 *   4. Show the decomposition exists over Q(sqrt(2))
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

printf "=== FERMAT QUARTIC BITANGENT DECOMPOSITION SEARCH ===\n";
printf "F = x^4 + y^4 + z^4\n\n";

// =========================================================================
// Step 1: The 4 rational bitangent lines and their contact loci
// =========================================================================
printf "=== STEP 1: RATIONAL BITANGENT LINES ===\n";
lines := [x+y+z, x+y-z, x-y+z, -x+y+z];
names := ["x+y+z", "x+y-z", "x-y+z", "-x+y+z"];

for idx in [1..4] do
    l := lines[idx];
    // Substitute z = -(other terms)/coeff to restrict F to the line
    // For l = ax+by+cz, parametrize on the line
    // Use the specific substitutions
    R2<s,t> := PolynomialRing(Rationals(), 2);
    if idx eq 1 then
        // x+y+z=0, z=-(x+y)
        rest := Evaluate(F, [s, t, -(s+t)]);
    elif idx eq 2 then
        // x+y-z=0, z=x+y
        rest := Evaluate(F, [s, t, s+t]);
    elif idx eq 3 then
        // x-y+z=0, y=x+z
        rest := Evaluate(F, [s, s+t, t]);
    else
        // -x+y+z=0, x=y+z
        rest := Evaluate(F, [s+t, s, t]);
    end if;
    fac := Factorization(rest);
    printf "  %o: F|_l = %o\n", names[idx], rest;
    printf "    Factored: ";
    for f in fac do printf "(%o)^%o ", f[1], f[2]; end for;
    printf "\n";
end for;

// =========================================================================
// Step 2: Restriction analysis - why sqrt(2) appears
// =========================================================================
printf "\n=== STEP 2: RESTRICTION ANALYSIS ===\n";
printf "All 4 rational bitangent lines give F|_l = 2*(quadratic)^2.\n";
printf "The factor of 2 is the key obstruction.\n\n";

printf "For l3^2*l1*l2 - Q2^2 = lambda*F:\n";
printf "On l1=0: -Q2^2 = lambda*F = lambda*2*q^2, so Q2 = sqrt(-2*lambda)*q.\n";
printf "For rational Q2: need -2*lambda = rational square.\n";
printf "So lambda = -r^2/2 for some r in Q*.\n\n";

// =========================================================================
// Step 3: Algebraic analysis for the pair (x+y+z, x+y-z)
// =========================================================================
printf "=== STEP 3: ALGEBRAIC ANALYSIS ===\n";
l1 := x+y+z; l2 := x+y-z;
printf "Pair: l1 = %o, l2 = %o\n", l1, l2;
printf "l1*l2 = (x+y)^2 - z^2\n\n";

// Key identity:
// (x^2+xy+y^2)^2 - (1/2)*F = (1/2)*((x+y)^4 - z^4)
//                            = (1/2)*l1*l2*((x+y)^2+z^2)
lhs := (x^2+x*y+y^2)^2 - F/2;
rhs := l1*l2*((x+y)^2+z^2) / 2;
printf "Key identity: (x^2+xy+y^2)^2 - F/2 = (1/2)*l1*l2*((x+y)^2+z^2)\n";
printf "Verified: %o\n\n", lhs eq rhs;

// From the analysis: Q2 = (x^2+xy+y^2) - t*l1*l2 for parameter t.
// Then l3^2 = (1/2)*((x+y)^2+z^2) - 2t*(x^2+xy+y^2) + t^2*l1*l2
// For l3^2 to be a perfect square of a linear form, need:
//   coeff of xz = 0, coeff of yz = 0
//   This forces either gamma=0 (giving t^2=1/2) or alpha=beta=0 (giving t=1+-1/sqrt(2))
printf "For Q2 = (x^2+xy+y^2) - t*(l1*l2), the equation reduces to:\n";
printf "  l3^2 = (1/2)*((x+y)^2+z^2) - 2t*(x^2+xy+y^2) + t^2*(l1*l2)\n\n";

printf "Coefficients of l3^2 = alpha^2*x^2 + ... :\n";
printf "  xz coeff: 0  (forces alpha*gamma = 0)\n";
printf "  yz coeff: 0  (forces beta*gamma = 0)\n\n";

printf "Case gamma=0: z^2 coeff gives 1/2 - t^2 = 0, so t = +-1/sqrt(2). NOT RATIONAL.\n";
printf "Case alpha=beta=0: x^2 coeff gives 1/2 - 2t + t^2 = 0, so t = 1+-1/sqrt(2). NOT RATIONAL.\n\n";

printf "CONCLUSION: No rational decomposition for this pair.\n";
printf "The obstruction is sqrt(2).\n\n";

// =========================================================================
// Step 4: Product of all 4 rational bitangent lines
// =========================================================================
printf "=== STEP 4: PRODUCT OF ALL 4 BITANGENT LINES ===\n";
prod4 := l1 * l2 * (x-y+z) * (-x+y+z);
printf "l1*l2*l3_*l4_ = %o\n", prod4;

// This should equal x^4+y^4+z^4 - 2(x^2y^2+x^2z^2+y^2z^2)
test := x^4+y^4+z^4 - 2*(x^2*y^2+x^2*z^2+y^2*z^2);
printf "x^4+y^4+z^4 - 2(x^2y^2+x^2z^2+y^2z^2) = %o\n", test;
printf "Equal? %o\n\n", prod4 eq test;

// So F = l1*l2*l3_*l4_ + 2*(x^2y^2+x^2z^2+y^2z^2)
// Check:
e2 := x^2*y^2 + x^2*z^2 + y^2*z^2;  // second elementary in x^2,y^2,z^2
check := prod4 + 2*e2;
printf "F = product_of_4_bitangent_lines + 2*e2(x^2,y^2,z^2)\n";
printf "Verified: %o\n\n", check eq F;

// =========================================================================
// Step 5: Brute force search over Q with small coefficients
// =========================================================================
printf "=== STEP 5: BRUTE FORCE SEARCH ===\n";

bnd := 2;
found_any := false;

for idx1 in [1..4] do
for idx2 in [idx1+1..4] do
    l1 := lines[idx1]; l2 := lines[idx2];
    prod_l := l1 * l2;

    // Search over l3 and lambda
    for a in [-bnd..bnd] do
    for b in [-bnd..bnd] do
    for c in [-bnd..bnd] do
        l3 := a*x + b*y + c*z;
        if l3 eq 0 then continue; end if;
        quartic := l3^2 * prod_l;

        // For each lambda = p/q with small p,q
        for num in [-4..4] do
        for den in [1..4] do
            lam := num/den;
            if lam eq 0 then continue; end if;
            G := quartic - lam * F;

            // Check if G is a perfect square of a quadratic form
            // G = Q2^2 means G factors as Q2^2
            fac := Factorization(G);
            is_sq := false;
            if #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
                is_sq := true;
                Q2_found := fac[1][1];
            end if;

            if is_sq then
                found_any := true;
                printf "FOUND! l1=%o, l2=%o\n", names[idx1], names[idx2];
                printf "  l3 = %o*x + %o*y + %o*z\n", a, b, c;
                printf "  lambda = %o\n", lam;
                printf "  Q2 = %o\n\n", Q2_found;
            end if;
        end for;
        end for;
    end for;
    end for;
    end for;
end for;
end for;

if not found_any then
    printf "No rational decomposition found (bound = %o).\n\n", bnd;
end if;

// =========================================================================
// Step 6: Decomposition over Q(sqrt(2))
// =========================================================================
printf "=== STEP 6: DECOMPOSITION OVER Q(sqrt(2)) ===\n";

P<u> := PolynomialRing(Rationals());
K<r2> := NumberField(u^2 - 2);
RK<x,y,z> := PolynomialRing(K, 3);
FK := x^4 + y^4 + z^4;

l1 := x+y+z; l2 := x+y-z;

// From the analysis: t = 1 - 1/sqrt(2) = 1 - r2/2 = (2-r2)/2
// or t = 1/sqrt(2) for the gamma=0 case
// Let's try t = r2/2 (i.e. t^2 = 1/2)
t := r2/2;
Q2 := (x^2 + x*y + y^2) - t * l1 * l2;
printf "With t = sqrt(2)/2:\n";
printf "Q2 = (x^2+xy+y^2) - (sqrt(2)/2)*(x+y+z)*(x+y-z)\n";
printf "   = %o\n\n", Q2;

// Then l3 should have gamma=0, with l3^2 having coefficients:
// x^2: 1/2 - 2t + t^2 = 1/2 - sqrt(2) + 1/2 = 1 - sqrt(2)
// y^2: same
// xy: 1 - 2t + 2t^2 = 1 - sqrt(2) + 1 = 2 - sqrt(2)
// z^2: 0

coeff_x2 := 1/2 - 2*t + t^2;
coeff_y2 := coeff_x2;
coeff_xy := 1 - 2*t + 2*t^2;
printf "l3^2 coefficients: x^2: %o, y^2: %o, xy: %o, z^2: 0\n", coeff_x2, coeff_y2, coeff_xy;

// For l3 = alpha*x + beta*y, we need:
// alpha^2 = coeff_x2, beta^2 = coeff_y2, 2*alpha*beta = coeff_xy
// alpha^2 = 1 - sqrt(2), which is NEGATIVE! So l3 has coefficients in Q(sqrt(2), sqrt(1-sqrt(2)))
// This means the decomposition requires Q(sqrt(2)) for Q2 but
// l3 requires an even larger field.

printf "\nalpha^2 = 1 - sqrt(2) < 0, so l3 is NOT defined over Q(sqrt(2))!\n";
printf "This case requires a degree-4 extension.\n\n";

// Let's try t = 1 - r2/2 = (2-r2)/2 instead (from alpha=beta=0 case)
t2 := (2 - r2)/2;
printf "With t = 1 - sqrt(2)/2 = (2-sqrt(2))/2:\n";
coeff_z2 := 1/2 - t2^2;
printf "l3 = gamma*z, gamma^2 = 1/2 - t^2 = 1/2 - (2-sqrt(2))^2/4\n";
printf "   = 1/2 - (6-4*sqrt(2))/4 = (2 - 6 + 4*sqrt(2))/4 = (-4+4*sqrt(2))/4 = sqrt(2)-1\n";
printf "gamma^2 = %o\n", coeff_z2;

// sqrt(2) - 1 > 0 (about 0.414), so gamma is real but irrational
// gamma = sqrt(sqrt(2)-1), which is NOT in Q(sqrt(2))

printf "gamma = sqrt(sqrt(2)-1), NOT in Q(sqrt(2)).\n\n";

// So even over Q(sqrt(2)), l3 is not rational. The decomposition needs Q(sqrt(sqrt(2)-1)).
// This is a degree-4 extension of Q.

printf "=== RECONSIDERING: DIFFERENT APPROACH ===\n\n";

// Instead of fixing Q2's form, let's try the full system numerically.
// Over Q(sqrt(2)), set l3 = r2*z (for example) and solve for Q2.

l3_try := r2 * z;
G := l3_try^2 * l1 * l2;  // = 2*z^2*((x+y)^2-z^2)
printf "Try l3 = sqrt(2)*z:\n";
printf "l3^2*l1*l2 = 2*z^2*((x+y)^2-z^2) = %o\n", G;

// We need G - Q2^2 = lambda * F
// Try lambda = -1: G + F = Q2^2
target := G + FK;
printf "G + F = %o\n", target;

// Check if this is a perfect square
fac := Factorization(target);
printf "Factorization of G+F: ";
for f in fac do printf "(%o)^%o ", f[1], f[2]; end for;
printf "\n";

is_sq := (#fac eq 1 and fac[1][2] eq 2);
if is_sq then
    printf "PERFECT SQUARE! Q2 = %o\n\n", fac[1][1];
else
    printf "Not a perfect square.\n\n";
end if;

// Try lambda = -2: G + 2F = Q2^2
target2 := G + 2*FK;
printf "G + 2F = %o\n", target2;
fac2 := Factorization(target2);
printf "Factorization: ";
for f in fac2 do printf "(%o)^%o ", f[1], f[2]; end for;
printf "\n\n";

// Try lambda = 1: G - F = Q2^2
target3 := G - FK;
printf "G - F = %o\n", target3;
fac3 := Factorization(target3);
printf "Factorization: ";
for f in fac3 do printf "(%o)^%o ", f[1], f[2]; end for;
printf "\n\n";

// =========================================================================
// Step 7: Systematic search over Q(sqrt(2))
// =========================================================================
printf "=== STEP 7: SEARCH OVER Q(sqrt(2)) ===\n";

found_sqrt2 := false;
for a0 in [-2..2] do for a1 in [-2..2] do
for b0 in [-2..2] do for b1 in [-2..2] do
for c0 in [-2..2] do for c1 in [-2..2] do
    l3_test := (a0+a1*r2)*x + (b0+b1*r2)*y + (c0+c1*r2)*z;
    if l3_test eq 0 then continue; end if;
    // Skip if l3 has only zero or parallel to already tried
    quartic_test := l3_test^2 * l1 * l2;

    for num in [-4..4] do
    for den in [1..4] do
        lam := num/den;
        if lam eq 0 then continue; end if;
        G_test := quartic_test - lam * FK;
        fac_test := Factorization(G_test);
        if #fac_test eq 1 and fac_test[1][2] eq 2 and TotalDegree(fac_test[1][1]) eq 2 then
            found_sqrt2 := true;
            printf "FOUND over Q(sqrt(2))!\n";
            printf "  l3 = %o\n", l3_test;
            printf "  lambda = %o\n", lam;
            printf "  Q2 = %o\n", fac_test[1][1];
            // Verify
            if fac_test[1][1]^2 eq G_test then
                printf "  VERIFIED.\n\n";
            end if;
        end if;
    end for;
    end for;
end for; end for;
end for; end for;
end for; end for;

if not found_sqrt2 then
    printf "No decomposition found over Q(sqrt(2)) with bound 2.\n\n";
end if;

// =========================================================================
// Step 8: Try the TWIST C2 = x^4+y^4-z^4 which has rational points
// =========================================================================
printf "=== STEP 8: TWIST x^4+y^4-z^4 (HAS RATIONAL POINT) ===\n";

R2<x,y,z> := PolynomialRing(Rationals(), 3);
F2 := x^4 + y^4 - z^4;

// Bitangent lines of x^4+y^4-z^4=0:
// z = -(x+y): x^4+y^4-(x+y)^4 = -4x^3y-6x^2y^2-4xy^3 = -2xy(2x^2+3xy+2y^2)
// Not a perfect square! So x+y+z is NOT a bitangent of the twist.

// Let's find bitangent lines of x^4+y^4-z^4.
// Line ax+by+z=0, z=-ax-by:
// F2|_l = x^4+y^4-(ax+by)^4 = (1-a^4)x^4 - 4a^3b x^3y - 6a^2b^2 x^2y^2 - 4ab^3 xy^3 + (1-b^4)y^4
// For this to be a perfect square: need it = (Ax^2+Bxy+Cy^2)^2

// Over Q: try simple values. a=1,b=0: F2|_l = 0*x^4 + y^4 = y^4. Perfect square!
// Line x+z=0. So z=-x. F2 = x^4+y^4-x^4 = y^4. Bitangent with contact = y^2.
printf "Bitangent lines of x^4+y^4-z^4:\n";
printf "  x+z=0 (z=-x): F2|_l = y^4 = (y^2)^2. Contact: y^2.\n";
printf "  x-z=0 (z=x):  F2|_l = y^4 = (y^2)^2. Contact: y^2.\n";
printf "  y+z=0 (z=-y): F2|_l = x^4 = (x^2)^2. Contact: x^2.\n";
printf "  y-z=0 (z=y):  F2|_l = x^4 = (x^2)^2. Contact: x^2.\n\n";

printf "KEY: Contact locus is (quadratic)^2, NO factor of 2!\n";
printf "This should allow rational decompositions.\n\n";

// Try pair l1=x+z, l2=x-z. Product: l1*l2 = x^2-z^2.
l1_tw := x+z; l2_tw := x-z;
printf "Pair: l1=%o, l2=%o, product = x^2-z^2\n", l1_tw, l2_tw;

// Search for l3^2*(x^2-z^2) - Q2^2 = lambda*(x^4+y^4-z^4)
found_twist := false;
bnd := 3;
for a in [-bnd..bnd] do
for b in [-bnd..bnd] do
for c in [-bnd..bnd] do
    l3_tw := a*x + b*y + c*z;
    if l3_tw eq 0 then continue; end if;
    quartic_tw := l3_tw^2 * l1_tw * l2_tw;

    for num in [-6..6] do
    for den in [1..4] do
        lam := num/den;
        if lam eq 0 then continue; end if;
        G_tw := quartic_tw - lam * F2;
        fac_tw := Factorization(G_tw);
        if #fac_tw eq 1 and fac_tw[1][2] eq 2 and TotalDegree(fac_tw[1][1]) eq 2 then
            found_twist := true;
            printf "FOUND on twist!\n";
            printf "  l3 = %o*x + %o*y + %o*z, lambda = %o\n", a, b, c, lam;
            printf "  Q2 = %o\n", fac_tw[1][1];
            if fac_tw[1][1]^2 + lam*F2 eq quartic_tw then
                printf "  VERIFIED: l3^2*l1*l2 - Q2^2 = lambda*F2\n\n";
            end if;
        end if;
    end for;
    end for;
end for;
end for;
end for;

if not found_twist then
    printf "No decomposition found on twist (bound=%o).\n", bnd;
    // Try more pairs
    printf "\nTrying other pairs on twist...\n";
    pairs_tw := [<x+z, y+z>, <x+z, y-z>, <x-z, y+z>, <x-z, y-z>,
                 <y+z, y-z>, <x+z, x-z>];
    for pair in pairs_tw do
        l1_tw := pair[1]; l2_tw := pair[2];
        prod_tw := l1_tw * l2_tw;
        for a in [-bnd..bnd] do
        for b in [-bnd..bnd] do
        for c in [-bnd..bnd] do
            l3_tw := a*x + b*y + c*z;
            if l3_tw eq 0 then continue; end if;
            quartic_tw := l3_tw^2 * prod_tw;
            for num in [-6..6] do
            for den in [1..4] do
                lam := num/den;
                if lam eq 0 then continue; end if;
                G_tw := quartic_tw - lam * F2;
                fac_tw := Factorization(G_tw);
                if #fac_tw eq 1 and fac_tw[1][2] eq 2 and TotalDegree(fac_tw[1][1]) eq 2 then
                    printf "FOUND on twist!\n";
                    printf "  l1=%o, l2=%o\n", l1_tw, l2_tw;
                    printf "  l3 = %o*x + %o*y + %o*z, lambda = %o\n", a, b, c, lam;
                    printf "  Q2 = %o\n", fac_tw[1][1];
                    printf "  Verified: %o\n\n", (fac_tw[1][1])^2 + lam*F2 eq quartic_tw;
                    found_twist := true;
                end if;
            end for;
            end for;
        end for;
        end for;
        end for;
    end for;
    if not found_twist then
        printf "Still no decomposition on twist.\n\n";
    end if;
end if;

// =========================================================================
// Step 9: On the twist, also try general Q1*Q3 - Q2^2 = F2
// =========================================================================
printf "=== STEP 9: GENERAL QUADRIC DECOMP OF x^4+y^4-z^4 OVER Q ===\n";
found_gen := 0;
bnd2 := 2;
for c1 in [-bnd2..bnd2] do for c2 in [-bnd2..bnd2] do for c3 in [-bnd2..bnd2] do
for c4 in [-bnd2..bnd2] do for c5 in [-bnd2..bnd2] do for c6 in [-bnd2..bnd2] do
    Q2_test := c1*x^2 + c2*y^2 + c3*z^2 + c4*x*y + c5*x*z + c6*y*z;
    if Q2_test eq 0 then continue; end if;
    coeffs := [c1,c2,c3,c4,c5,c6];
    first_nz := 0;
    for j in [1..6] do if coeffs[j] ne 0 then first_nz := coeffs[j]; break; end if; end for;
    if first_nz lt 0 then continue; end if;

    G_gen := F2 + Q2_test^2;
    fac_gen := Factorization(G_gen);

    is_decomp := false;
    if #fac_gen eq 2 and TotalDegree(fac_gen[1][1]) eq 2 and TotalDegree(fac_gen[2][1]) eq 2
       and fac_gen[1][2] eq 1 and fac_gen[2][2] eq 1 then
        Q1_g := fac_gen[1][1]; Q3_g := fac_gen[2][1];
        lc := LeadingCoefficient(G_gen) / LeadingCoefficient(Q1_g*Q3_g);
        Q1_g := lc * Q1_g;
        if Q1_g*Q3_g - Q2_test^2 eq F2 then
            is_decomp := true;
        end if;
    elif #fac_gen eq 1 and fac_gen[1][2] eq 2 and TotalDegree(fac_gen[1][1]) eq 2 then
        Q1_g := fac_gen[1][1];
        Q3_g := Q1_g;
        lc := LeadingCoefficient(G_gen) / LeadingCoefficient(Q1_g^2);
        Q1_g := lc * Q1_g;
        if Q1_g*Q3_g - Q2_test^2 eq F2 then
            is_decomp := true;
        end if;
    end if;

    if is_decomp then
        found_gen +:= 1;
        if found_gen le 10 then
            printf "DECOMP #%o of x^4+y^4-z^4:\n", found_gen;
            printf "  Q2 = %o\n", Q2_test;
            printf "  Q1 = %o\n  Q3 = %o\n\n", Q1_g, Q3_g;
        end if;
    end if;
end for; end for; end for;
end for; end for; end for;
printf "Total Q-rational decompositions of x^4+y^4-z^4 found: %o (bound=%o)\n\n", found_gen, bnd2;

quit;
