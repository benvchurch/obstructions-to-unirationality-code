/*******************************************************************************
 * Q2_bitangent.m
 *
 * Set Q2 = l_i * l_j (product of two rational bitangent lines).
 * Compute G = F + Q2^2 and try to factor G into two quadrics over Q.
 * If G = Q1 * Q3, then F = Q1*Q3 - Q2^2 is a rational decomposition.
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

lines := [x+y+z, x+y-z, x-y+z, x-y-z];
names := ["x+y+z", "x+y-z", "x-y+z", "x-y-z"];

printf "=== Q2 = BITANGENT PRODUCT, FACTOR F + Q2^2 ===\n\n";

for i in [1..4] do for j in [i+1..4] do
    Q2 := lines[i] * lines[j];
    printf "--- Q2 = (%o)(%o) = %o ---\n", names[i], names[j], Q2;

    G := F + Q2^2;
    printf "  G = F + Q2^2 = %o\n", G;

    fac := Factorization(G);
    printf "  Factorization of G:\n";
    for pair in fac do
        printf "    (%o)^%o   [degree %o]\n", pair[1], pair[2], TotalDegree(pair[1]);
    end for;

    // Check if G has a quadratic factor
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
    if not has_quad then
        printf "  No quadratic factor over Q.\n";
    end if;

    printf "\n";
end for; end for;

// =========================================================================
// Also try Q2 = a*l_i*l_j + b*l_k*l_m (linear combinations of products)
// =========================================================================
printf "=== Q2 = LINEAR COMBINATIONS OF BITANGENT PRODUCTS ===\n\n";

products := [];
prod_names := [];
for i in [1..4] do for j in [i+1..4] do
    Append(~products, lines[i]*lines[j]);
    Append(~prod_names, Sprintf("(%o)(%o)", names[i], names[j]));
end for; end for;

printf "Products: %o\n\n", prod_names;

// Search over integer combinations
bnd := 5;
found := 0;
for i in [1..#products] do
for j in [i..#products] do
for a in [1..bnd] do  // a > 0 by symmetry
for b in [-bnd..bnd] do
    if i eq j and b ne 0 then continue; end if;  // just scalar multiple
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
        Q1 := fac[1][1];
        Q3 := G div Q1;
        // Adjust for leading coefficients
        lc := LeadingCoefficient(G) / (LeadingCoefficient(Q1) * LeadingCoefficient(Q3));
        if lc ne 1 then Q1 := lc * Q1; end if;
        printf "FOUND #%o: Q2 = %o*%o + %o*%o\n", found, a, prod_names[i], b, prod_names[j];
        printf "  Q1 = %o\n  Q3 = %o\n", fac[1][1], fac[2][1];
        if Q1*Q3 - Q2^2 eq F then
            printf "  VERIFIED: F = Q1*Q3 - Q2^2\n";
        end if;
        printf "\n";
    end if;
end for;
end for;
end for;
end for;

printf "Total decompositions found: %o (bound %o)\n\n", found, bnd;

// =========================================================================
// Also try: Q2 with general small rational coefficients
// Since the previous approach is still 2 parameters, try a broader search
// =========================================================================
printf "=== GENERAL Q2, LARGER SEARCH (diagonal, bound 10) ===\n";
found2 := 0;
for a in [0..10] do
for b in [-10..10] do
for c in [-10..10] do
    Q2 := a*x^2 + b*y^2 + c*z^2;
    if Q2 eq 0 then continue; end if;
    G := F + Q2^2;
    fac := Factorization(G);
    has_decomp := false;
    if #fac ge 2 then
        for k in [1..#fac] do
            if TotalDegree(fac[k][1]) eq 2 then
                rem := G div (fac[k][1]^fac[k][2]);
                if TotalDegree(rem) le 2 then
                    has_decomp := true;
                    printf "FOUND: Q2 = %o, factor = (%o)^%o, rem = %o\n",
                        Q2, fac[k][1], fac[k][2], rem;
                    found2 +:= 1;
                end if;
            end if;
        end for;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_decomp := true;
        printf "FOUND: Q2 = %o, perfect square = (%o)^2\n", Q2, fac[1][1];
        found2 +:= 1;
    end if;
end for;
end for;
end for;
printf "Diagonal Q2, bound 10: %o decompositions found\n", found2;

quit;
