/*******************************************************************************
 * bitangent_decomps.m
 *
 * Bitangent-based quadric decomposition analysis for the Fermat quartic
 * x^4+y^4+z^4.  Three complementary approaches:
 *
 * Merged from: bitangent_decomp_search.m + Q2_bitangent.m + bitangent_pair_decomp.m
 *
 * Part 1 (from bitangent_decomp_search.m):
 *   Search for l3^2*l1*l2 - Q2^2 = lambda*F over Q and Q(sqrt(2)).
 *   Also tests the twist x^4+y^4-z^4.
 *
 * Part 2 (from Q2_bitangent.m):
 *   Set Q2 = product of two bitangent lines, factor F+Q2^2.
 *
 * Part 3 (from bitangent_pair_decomp.m):
 *   Set Q1 = product of two bitangent lines, parametrize Q2 through
 *   tangency points, find algebraic obstruction (-2 not a square).
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

lines := [x+y+z, x+y-z, x-y+z, x-y-z];
names := ["x+y+z", "x+y-z", "x-y+z", "x-y-z"];

// =========== PART 1: BITANGENT-PAIR SEARCH (l3^2 * l1 * l2 - Q2^2 = lambda*F) ===========

printf "=== PART 1: BITANGENT-PAIR DECOMPOSITION SEARCH ===\n";
printf "F = x^4 + y^4 + z^4\n\n";

// Step 1: Rational bitangent lines and their contact loci
printf "--- Rational bitangent lines ---\n";
for idx in [1..4] do
    l := lines[idx];
    R2<s,t> := PolynomialRing(Rationals(), 2);
    if idx eq 1 then rest := Evaluate(F, [s, t, -(s+t)]);
    elif idx eq 2 then rest := Evaluate(F, [s, t, s+t]);
    elif idx eq 3 then rest := Evaluate(F, [s, s+t, t]);
    else rest := Evaluate(F, [s+t, s, t]);
    end if;
    fac := Factorization(rest);
    printf "  %o: F|_l = ", names[idx];
    for f in fac do printf "(%o)^%o ", f[1], f[2]; end for;
    printf "\n";
end for;

printf "\nAll 4 rational bitangent lines give F|_l = 2*(quadratic)^2.\n";
printf "The factor of 2 is the key obstruction.\n\n";

// Step 2: Algebraic analysis for pair (x+y+z, x+y-z)
printf "--- Algebraic analysis for (x+y+z, x+y-z) ---\n";
l1 := x+y+z; l2 := x+y-z;

// Key identity: (x^2+xy+y^2)^2 - F/2 = (1/2)*l1*l2*((x+y)^2+z^2)
lhs := (x^2+x*y+y^2)^2 - F/2;
rhs := l1*l2*((x+y)^2+z^2) / 2;
printf "Key identity: (x^2+xy+y^2)^2 - F/2 = (1/2)*l1*l2*((x+y)^2+z^2)\n";
printf "Verified: %o\n\n", lhs eq rhs;

printf "For Q2 = (x^2+xy+y^2) - t*(l1*l2), the equation reduces to:\n";
printf "  l3 = gamma*z: gamma^2 = 1/2 - t^2, so t = +-1/sqrt(2). NOT RATIONAL.\n";
printf "  l3 = alpha*x+beta*y: (1/2-2t+t^2)=0 => t = 1+-1/sqrt(2). NOT RATIONAL.\n";
printf "CONCLUSION: sqrt(2) obstruction for this pair.\n\n";

// Step 3: Product of all 4 bitangent lines
printf "--- Product of all 4 bitangent lines ---\n";
prod4 := l1 * l2 * (x-y+z) * (-x+y+z);
e2sym := x^2*y^2 + x^2*z^2 + y^2*z^2;
printf "l1*l2*l3*l4 = F - 2*e2(x^2,y^2,z^2)\n";
printf "Verified: %o\n\n", prod4 + 2*e2sym eq F;

// Step 4: Brute force search over Q
printf "--- Brute force Q-rational search ---\n";
bnd := 2;
found_any := false;

for idx1 in [1..4] do for idx2 in [idx1+1..4] do
    l1 := lines[idx1]; l2 := lines[idx2];
    prod_l := l1 * l2;
    for a in [-bnd..bnd] do for b in [-bnd..bnd] do for c in [-bnd..bnd] do
        l3 := a*x + b*y + c*z;
        if l3 eq 0 then continue; end if;
        quartic := l3^2 * prod_l;
        for num in [-4..4] do for den in [1..4] do
            lam := num/den;
            if lam eq 0 then continue; end if;
            G := quartic - lam * F;
            fac := Factorization(G);
            if #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
                found_any := true;
                printf "FOUND! l1=%o, l2=%o, l3=%ox+%oy+%oz, lambda=%o\n",
                    names[idx1], names[idx2], a, b, c, lam;
                printf "  Q2 = %o\n\n", fac[1][1];
            end if;
        end for; end for;
    end for; end for; end for;
end for; end for;

if not found_any then
    printf "No rational decomposition found (bound = %o).\n\n", bnd;
end if;

// Step 5: Search over Q(sqrt(2))
printf "--- Search over Q(sqrt(2)) ---\n";
PP<u> := PolynomialRing(Rationals());
K<r2> := NumberField(u^2 - 2);
RK<x,y,z> := PolynomialRing(K, 3);
FK := x^4 + y^4 + z^4;
l1k := x+y+z; l2k := x+y-z;

found_sqrt2 := false;
for a0 in [-2..2] do for a1 in [-2..2] do
for b0 in [-2..2] do for b1 in [-2..2] do
for c0 in [-2..2] do for c1 in [-2..2] do
    l3_test := (a0+a1*r2)*x + (b0+b1*r2)*y + (c0+c1*r2)*z;
    if l3_test eq 0 then continue; end if;
    quartic_test := l3_test^2 * l1k * l2k;
    for num in [-4..4] do for den in [1..4] do
        lam := num/den;
        if lam eq 0 then continue; end if;
        G_test := quartic_test - lam * FK;
        fac_test := Factorization(G_test);
        if #fac_test eq 1 and fac_test[1][2] eq 2 and TotalDegree(fac_test[1][1]) eq 2 then
            found_sqrt2 := true;
            printf "FOUND over Q(sqrt(2))!\n";
            printf "  l3 = %o, lambda = %o\n", l3_test, lam;
            printf "  Q2 = %o\n", fac_test[1][1];
            printf "  VERIFIED: %o\n\n", fac_test[1][1]^2 eq G_test;
        end if;
    end for; end for;
end for; end for;
end for; end for;
end for; end for;

if not found_sqrt2 then
    printf "No decomposition found over Q(sqrt(2)) with bound 2.\n\n";
end if;

// Step 6: Twist x^4+y^4-z^4
printf "--- Twist x^4+y^4-z^4 ---\n";
R2<x,y,z> := PolynomialRing(Rationals(), 3);
F2 := x^4 + y^4 - z^4;

printf "Bitangent lines of x^4+y^4-z^4:\n";
printf "  x+z=0: F2|_l = y^4 (no factor of 2!)\n";
printf "  x-z=0: F2|_l = y^4\n";
printf "  y+z=0: F2|_l = x^4\n";
printf "  y-z=0: F2|_l = x^4\n\n";

// General quadric decomp of twist
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
    Q1_g := R2!0; Q3_g := R2!0;
    if #fac_gen eq 2 and TotalDegree(fac_gen[1][1]) eq 2 and TotalDegree(fac_gen[2][1]) eq 2
       and fac_gen[1][2] eq 1 and fac_gen[2][2] eq 1 then
        Q1_g := fac_gen[1][1]; Q3_g := fac_gen[2][1];
        lc := LeadingCoefficient(G_gen) / LeadingCoefficient(Q1_g*Q3_g);
        Q1_g := lc * Q1_g;
        if Q1_g*Q3_g - Q2_test^2 eq F2 then is_decomp := true; end if;
    elif #fac_gen eq 1 and fac_gen[1][2] eq 2 and TotalDegree(fac_gen[1][1]) eq 2 then
        Q1_g := fac_gen[1][1]; Q3_g := Q1_g;
        lc := LeadingCoefficient(G_gen) / LeadingCoefficient(Q1_g^2);
        Q1_g := lc * Q1_g;
        if Q1_g*Q3_g - Q2_test^2 eq F2 then is_decomp := true; end if;
    end if;

    if is_decomp then
        found_gen +:= 1;
        if found_gen le 10 then
            printf "DECOMP #%o of x^4+y^4-z^4:\n", found_gen;
            printf "  Q2 = %o\n  Q1 = %o\n  Q3 = %o\n\n", Q2_test, Q1_g, Q3_g;
        end if;
    end if;
end for; end for; end for;
end for; end for; end for;
printf "Total Q-rational decomps of x^4+y^4-z^4: %o (bound=%o)\n\n", found_gen, bnd2;

// =========== PART 2: Q2 = BITANGENT PRODUCT, FACTOR F + Q2^2 ===========

printf "\n=== PART 2: Q2 = BITANGENT PRODUCT ===\n\n";

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;
lines := [x+y+z, x+y-z, x-y+z, x-y-z];
names := ["x+y+z", "x+y-z", "x-y+z", "x-y-z"];

for i in [1..4] do for j in [i+1..4] do
    Q2 := lines[i] * lines[j];
    printf "--- Q2 = (%o)(%o) ---\n", names[i], names[j];
    G := F + Q2^2;
    fac := Factorization(G);
    printf "  Factorization of F+Q2^2:\n";
    for pair in fac do
        printf "    (%o)^%o   [degree %o]\n", pair[1], pair[2], TotalDegree(pair[1]);
    end for;

    has_quad := false;
    for pair in fac do
        if TotalDegree(pair[1]) eq 2 then
            has_quad := true;
            Q1 := pair[1];
            Q3 := G div Q1;
            if TotalDegree(Q3) eq 2 then
                printf "  DECOMPOSITION FOUND: F = Q1*Q3 - Q2^2\n";
                printf "    Q1 = %o\n    Q3 = %o\n", Q1, Q3;
                printf "    Verify: %o\n", Q1*Q3 - Q2^2 eq F;
            end if;
        end if;
    end for;
    if not has_quad then printf "  No quadratic factor over Q.\n"; end if;
    printf "\n";
end for; end for;

// Linear combinations of bitangent products
printf "--- Q2 = linear combinations of bitangent products ---\n";
products := [];
prod_names := [];
for i in [1..4] do for j in [i+1..4] do
    Append(~products, lines[i]*lines[j]);
    Append(~prod_names, Sprintf("(%o)(%o)", names[i], names[j]));
end for; end for;

bnd := 5;
found := 0;
for i in [1..#products] do
for j in [i..#products] do
for a in [1..bnd] do
for b in [-bnd..bnd] do
    if i eq j and b ne 0 then continue; end if;
    Q2 := a*products[i] + b*products[j];
    if Q2 eq 0 then continue; end if;
    G := F + Q2^2;
    fac := Factorization(G);
    has_decomp := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2
       and fac[1][2] eq 1 and fac[2][2] eq 1 then
        has_decomp := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_decomp := true;
    end if;
    if has_decomp then
        found +:= 1;
        printf "FOUND #%o: Q2 = %o*%o + %o*%o\n", found, a, prod_names[i], b, prod_names[j];
        printf "  Q1 = %o\n  Q3 = %o\n\n", fac[1][1], fac[2][1];
    end if;
end for;
end for;
end for;
end for;
printf "Bitangent-product combinations: %o decompositions found (bound %o)\n\n", found, bnd;

// =========== PART 3: Q1 = BITANGENT PRODUCT, TANGENCY POINT ANALYSIS ===========

printf "\n=== PART 3: Q1 = BITANGENT PRODUCT, TANGENCY ANALYSIS ===\n\n";

// Helper: restrict polynomial to a line l=0
function RestrictToLine(poly, lin)
    cx := MonomialCoefficient(lin, x);
    cy := MonomialCoefficient(lin, y);
    cz := MonomialCoefficient(lin, z);
    if cz ne 0 then
        return Evaluate(poly, [x, y, -(cx*x + cy*y)/cz]);
    elif cy ne 0 then
        return Evaluate(poly, [x, -(cx*x + cz*z)/cy, z]);
    else
        return Evaluate(poly, [-(cy*y + cz*z)/cx, y, z]);
    end if;
end function;

for i in [1..4] do for j in [i+1..4] do
    l1 := lines[i]; l2 := lines[j];
    Q1 := l1 * l2;
    printf "--- Pair (%o, %o) ---\n", names[i], names[j];
    printf "Q1 = %o\n", Q1;

    F_on_l1 := RestrictToLine(F, l1);
    F_on_l2 := RestrictToLine(F, l2);

    // Factor to find tangency quadratics and the scalar factor
    fac1 := Factorization(F_on_l1);
    t1 := R!0; c1 := Rationals()!1;
    for pair in fac1 do
        if TotalDegree(pair[1]) eq 2 and pair[2] eq 2 then
            t1 := pair[1];
            c1 := LeadingCoefficient(F_on_l1) / LeadingCoefficient(t1^2);
        end if;
    end for;
    printf "  F|_{l_%o=0} = %o * (%o)^2\n", i, c1, t1;

    fac2 := Factorization(F_on_l2);
    t2 := R!0; c2 := Rationals()!1;
    for pair in fac2 do
        if TotalDegree(pair[1]) eq 2 and pair[2] eq 2 then
            t2 := pair[1];
            c2 := LeadingCoefficient(F_on_l2) / LeadingCoefficient(t2^2);
        end if;
    end for;
    printf "  F|_{l_%o=0} = %o * (%o)^2\n", j, c2, t2;

    // Find 2-dim space of quadrics through all 4 tangency points
    mons := [x^2, y^2, z^2, x*y, x*z, y*z];
    gens1 := [x*l1, y*l1, z*l1, t1];
    gens2 := [x*l2, y*l2, z*l2, t2];

    V := VectorSpace(Rationals(), 6);
    S1 := sub<V | [V![MonomialCoefficient(g, m) : m in mons] : g in gens1]>;
    S2 := sub<V | [V![MonomialCoefficient(g, m) : m in mons] : g in gens2]>;
    S := S1 meet S2;
    printf "  Quadric space dim = %o\n", Dimension(S);

    basis_quads := [];
    for k in [1..Dimension(S)] do
        v := Basis(S)[k];
        q := &+[v[m] * mons[m] : m in [1..6]];
        Append(~basis_quads, q);
        printf "    q_%o = %o\n", k, q;
    end for;

    // On l_k=0: Q2|_{l_k} = (alpha*r1+beta*r2)*t_k
    // Divisibility requires (alpha*r1+beta*r2)^2 = -c_k
    rr := [];
    for k in [1..#basis_quads] do
        q := basis_quads[k];
        q_on_l1 := RestrictToLine(q, l1);
        t1_on_l1 := RestrictToLine(t1, l1);
        r1k := LeadingCoefficient(q_on_l1) / LeadingCoefficient(t1_on_l1);
        Append(~rr, r1k);
    end for;

    printf "  Condition on l_%o: (", i;
    for k in [1..#rr] do
        if k gt 1 then printf " + "; end if;
        if rr[k] eq 1 then printf "alpha_%o", k;
        else printf "%o*alpha_%o", rr[k], k; end if;
    end for;
    printf ")^2 = %o\n", -c1;

    is_sq := IsSquare(Rationals()!(-c1));
    printf "  Is %o a rational square? %o\n\n", -c1, is_sq;
end for; end for;

// Summary
printf "=== SUMMARY ===\n";
printf "For ALL pairs of Q-rational bitangent lines of x^4+y^4+z^4:\n";
printf "  F|_{l=0} = 2*(tangency)^2 for every bitangent line l.\n";
printf "  The divisibility condition requires (linear combo)^2 = -2.\n";
printf "  -2 is NOT a rational square => no rational decomposition exists\n";
printf "  with Q1 = product of two rational bitangent lines.\n";

quit;
