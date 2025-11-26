/*******************************************************************************
 * quadric_sqrt3.m
 *
 * Search for quadric decompositions of X^4+Y^4+Z^4 = Q1*Q3 - Q2^2
 * over Q(sqrt(-3)).
 *
 * Step 1: Find the explicit F_3 factorization for Q2=Y^2+Z^2
 * Step 2: Try to lift it to characteristic 0
 * Step 3: Exhaustive search over Q(sqrt(-3)) with small coefficients
 ******************************************************************************/

// =========================================================================
// STEP 1: Explicit F_3 factorization
// =========================================================================
print "=== STEP 1: FACTORIZATION OVER F_3 ===";
R3<X,Y,Z> := PolynomialRing(GF(3), 3);
F3 := X^4 + Y^4 + Z^4;

// All four Q2 values that gave decompositions
for Q2_data in [
    <Y^2 + Z^2, "Y^2+Z^2 (non-V_rat class)">,
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := F3 + Q2^2;
    fac := Factorization(G);
    printf "Q2 = %o:\n", name;
    printf "  F+Q2^2 = %o\n", G;
    printf "  Factorization: ";
    for pair in fac do
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    printf "\n";
    if #fac ge 2 or (#fac eq 1 and fac[1][2] ge 2) then
        if #fac ge 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
            Q1 := fac[1][1]; Q3 := fac[2][1];
            scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1*Q3);
            Q1 := scalar * Q1;
            printf "  Q1 = %o\n  Q3 = %o\n", Q1, Q3;
            assert Q1*Q3 - Q2^2 eq F3;
        end if;
    end if;
    printf "\n";
end for;

// =========================================================================
// STEP 2: Try factoring over Q(sqrt(-3))
// =========================================================================
print "=== STEP 2: FACTORING OVER Q(sqrt(-3)) ===";
P<x> := PolynomialRing(Rationals());
K<w> := NumberField(x^2 + 3);  // w = sqrt(-3)
OK := Integers(K);
printf "K = Q(sqrt(-3)), w = %o, w^2 = %o\n\n", w, w^2;

RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

// Try the four Q2 from F_3 (with integer coefficients)
for Q2_data in [
    <Y^2 + Z^2, "Y^2+Z^2">,
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := FK + Q2^2;
    fac := Factorization(G);
    printf "Q2 = %o over K: ", name;
    irred := true;
    for pair in fac do
        if pair[2] gt 1 or #fac gt 1 then irred := false; end if;
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    if irred then printf " [IRREDUCIBLE]"; else printf " [FACTORS!]"; end if;
    printf "\n";
end for;
printf "\n";

// =========================================================================
// STEP 3: Try Q2 with sqrt(-3) coefficients
// =========================================================================
print "=== STEP 3: Q2 WITH sqrt(-3) COEFFICIENTS ===";

// Try Q2 = alpha * (simple form) for alpha involving w
// Key idea: need F + Q2^2 to factor, so need Q2^2 to make F+Q2^2 reducible
// Q2 = a*w * (some integer form) gives Q2^2 = -3*a^2 * (form)^2

// Special case: Q2 = w * Q2', so Q2^2 = -3 * Q2'^2
// Then F + Q2^2 = F - 3*Q2'^2 = X^4+Y^4+Z^4 - 3*(Q2')^2
printf "Trying Q2 = w * Q2' (giving F - 3*Q2'^2):\n";
for Q2p_data in [
    <X*Y, "XY">,
    <X*Z, "XZ">,
    <Y*Z, "YZ">,
    <X^2, "X^2">,
    <Y^2, "Y^2">,
    <Z^2, "Z^2">,
    <X^2+Y^2, "X^2+Y^2">,
    <X^2+Z^2, "X^2+Z^2">,
    <Y^2+Z^2, "Y^2+Z^2">,
    <X*Y+Z^2, "XY+Z^2">,
    <X*Z+Y^2, "XZ+Y^2">,
    <X^2+Y*Z, "X^2+YZ">,
    <X*Y+X*Z, "XY+XZ">,
    <X*Y+Y*Z, "XY+YZ">,
    <X*Z+Y*Z, "XZ+YZ">,
    <X^2+Y^2+Z^2, "X^2+Y^2+Z^2">,
    <X*Y+X*Z+Y*Z, "XY+XZ+YZ">
] do
    Q2p := Q2p_data[1];
    name := Q2p_data[2];
    Q2 := w * Q2p;
    G := FK + Q2^2;  // = F - 3*Q2'^2
    fac := Factorization(G);
    irred := (#fac eq 1 and fac[1][2] eq 1);
    if not irred then
        printf "  Q2' = %o: FACTORS! ", name;
        for pair in fac do
            printf "(%o)^%o ", pair[1], pair[2];
        end for;
        printf "\n";
    end if;
end for;
printf "\n";

// Also try Q2 = integer + w*(something)
printf "Trying Q2 = integer_part + w*irrational_part:\n";
found_any := false;
int_forms := [0*X^2, X^2, Y^2, Z^2, X*Y, X*Z, Y*Z,
              X^2+Y^2, X^2+Z^2, Y^2+Z^2, X*Y+Z^2, X*Z+Y^2, X^2+Y*Z];
irr_forms := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z,
              X^2+Y^2, X^2+Z^2, Y^2+Z^2, X*Y+Z^2, X*Z+Y^2, X^2+Y*Z];

for i in [1..#int_forms] do
    for j in [1..#irr_forms] do
        Q2 := int_forms[i] + w * irr_forms[j];
        if Q2 eq 0 then continue; end if;
        G := FK + Q2^2;
        fac := Factorization(G);
        irred := (#fac eq 1 and fac[1][2] eq 1);
        if not irred then
            found_any := true;
            printf "  Q2 = (%o) + w*(%o): FACTORS!\n", int_forms[i], irr_forms[j];
            for pair in fac do
                printf "    (%o)^%o\n", pair[1], pair[2];
            end for;
            // Verify
            if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
                Q1 := fac[1][1]; Q3 := fac[2][1];
                scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1*Q3);
                Q1 := scalar * Q1;
                if Q1*Q3 - Q2^2 eq FK then
                    printf "    VERIFIED: F = Q1*Q3 - Q2^2\n";
                    printf "    Q1 = %o\n    Q3 = %o\n", Q1, Q3;
                end if;
            end if;
            printf "\n";
        end if;
    end for;
end for;

if not found_any then
    print "No factorizations found with this search.";
    print "";
end if;

// =========================================================================
// STEP 4: Broader search with general Z[w] coefficients
// =========================================================================
print "=== STEP 4: GENERAL SEARCH ===";
found := 0;
total := 0;
bnd := 1;

for a1 in [-bnd..bnd] do for b1 in [-bnd..bnd] do
for a2 in [-bnd..bnd] do for b2 in [-bnd..bnd] do
for a3 in [-bnd..bnd] do for b3 in [-bnd..bnd] do
for a4 in [-bnd..bnd] do for b4 in [-bnd..bnd] do
for a5 in [-bnd..bnd] do for b5 in [-bnd..bnd] do
for a6 in [-bnd..bnd] do for b6 in [-bnd..bnd] do
    c1 := a1 + b1*w; c2 := a2 + b2*w; c3 := a3 + b3*w;
    c4 := a4 + b4*w; c5 := a5 + b5*w; c6 := a6 + b6*w;
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2 + c4*X*Y + c5*X*Z + c6*Y*Z;
    if Q2 eq 0 then continue; end if;
    // Normalize: skip if -Q2 was already seen (Q2^2 = (-Q2)^2)
    // Simple normalization: require first nonzero real part positive,
    // or if zero, first nonzero imaginary part positive
    // (skip this for now, just search everything)

    G := FK + Q2^2;
    total +:= 1;
    fac := Factorization(G);
    irred := (#fac eq 1 and fac[1][2] eq 1);
    if not irred then
        // Check if it gives two quadratic factors
        has_quad := false;
        if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
            has_quad := true;
        elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
            has_quad := true;
        end if;
        if has_quad then
            found +:= 1;
            if found le 20 then
                printf "FOUND #%o: Q2 = %o\n", found, Q2;
                for pair in fac do
                    printf "  factor: (%o)^%o\n", pair[1], pair[2];
                end for;
            end if;
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;

printf "\nGeneral search: %o Q2 tested, %o decompositions found (bound=%o)\n", total, found, bnd;

quit;
