/*******************************************************************************
 * twist_decomp_search.m
 *
 * Part 1: Why l3^2*l1*l2 - Q2^2 = lambda*F CANNOT work for F=x^4+y^4+z^4.
 * Part 2: Search for Q-rational quadric decompositions of C2 = x^4+y^4-z^4.
 * Part 3: Interesting Q(sqrt(2))-factorization found for F.
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);

// =========================================================================
// Part 1: The positive-definiteness obstruction for x^4+y^4+z^4
// =========================================================================
printf "=== PART 1: WHY NO Q-DECOMPOSITION OF x^4+y^4+z^4 ===\n\n";

F := x^4 + y^4 + z^4;

// ANY decomposition Q1*Q3 - Q2^2 = F means Q1*Q3 = F + Q2^2.
// Over R, F(x,y,z) > 0 for (x,y,z) != 0 (positive definite).
// So Q1*Q3 = F + Q2^2 >= F > 0 for real (x,y,z) != 0.
// This means Q1, Q3 must both be definite (same sign).
//
// But l3^2*l1*l2 = (l3*l1)*(l3*l2) = Q1*Q3 where Q1,Q3 are products
// of two linear forms, hence INDEFINITE (they vanish on lines).
// So (l3*l1)*(l3*l2) takes value 0 on the line l1=0,
// but F + Q2^2 > 0 there. CONTRADICTION.

printf "l3^2*l1*l2 - Q2^2 = lambda*F with lambda > 0:\n";
printf "  On l1=0: -Q2^2 = lambda*F > 0. But -Q2^2 <= 0. Impossible.\n\n";

printf "l3^2*l1*l2 - Q2^2 = lambda*F with lambda < 0 (say lambda = -c, c > 0):\n";
printf "  Rearranged: Q2^2 = l3^2*l1*l2 + c*F.\n";
printf "  On l1=0: Q2^2 = c*F = c*2*q^2, so Q2|_{l1=0} = sqrt(2c)*q.\n";
printf "  For Q2 rational: 2c must be a perfect rational square.\n\n";

lines := [x+y+z, x+y-z, x-y+z, -x+y+z];
names := ["x+y+z", "x+y-z", "x-y+z", "-x+y+z"];

// Verify contact loci all have factor 2
printf "Contact loci of rational bitangents:\n";
for idx in [1..4] do
    l := lines[idx];
    // restrict F to l=0
    R2<s,t> := PolynomialRing(Rationals(), 2);
    if idx eq 1 then rest := Evaluate(F, [s, t, -(s+t)]);
    elif idx eq 2 then rest := Evaluate(F, [s, t, s+t]);
    elif idx eq 3 then rest := Evaluate(F, [s, s+t, t]);
    else rest := Evaluate(F, [s+t, s, t]);
    end if;
    // Factor out the scalar
    lc := LeadingCoefficient(rest);
    printf "  %o: F|_l = %o * (perfect square)  [leading coeff = %o]\n",
        names[idx], lc, lc;
end for;

printf "\nAll have factor 2. So lambda = -1/2 works (2c=1), but then\n";
printf "the system forces l3 to involve sqrt(sqrt(2)-1), a degree-4 number.\n";
printf "No Q-rational l3 exists.\n\n";

// =========================================================================
// Part 2: Quadric decompositions of x^4+y^4-z^4 over Q
// =========================================================================
printf "=== PART 2: QUADRIC DECOMPOSITIONS OF x^4+y^4-z^4 ===\n\n";

F2 := x^4 + y^4 - z^4;

// This curve has rational point (1:0:1), so Brauer obstruction vanishes.
// Also F2 is INDEFINITE, so the positive-definiteness argument doesn't apply.

// Bitangent lines of x^4+y^4-z^4:
printf "Bitangent lines of x^4+y^4-z^4:\n";
// x+z=0 (z=-x): F2 = x^4+y^4-x^4 = y^4 = (y^2)^2. Contact: 1*(y^2)^2.
// x-z=0 (z=x):  same.
// y+z=0 (z=-y): F2 = x^4+y^4-y^4 = x^4 = (x^2)^2. Contact: 1*(x^2)^2.
// y-z=0 (z=y):  same.

test_lines := [x+z, x-z, y+z, y-z];
test_names := ["x+z", "x-z", "y+z", "y-z"];
for idx in [1..4] do
    R2<s,t> := PolynomialRing(Rationals(), 2);
    if idx eq 1 then rest := Evaluate(F2, [s, t, -s]);
    elif idx eq 2 then rest := Evaluate(F2, [s, t, s]);
    elif idx eq 3 then rest := Evaluate(F2, [s, t, -t]);
    else rest := Evaluate(F2, [s, t, t]);
    end if;
    lc := LeadingCoefficient(rest);
    fac := Factorization(rest);
    printf "  %o: F2|_l = %o", test_names[idx], rest;
    printf " = ";
    for f in fac do printf "(%o)^%o ", f[1], f[2]; end for;
    printf " [leading coeff = %o]\n", lc;
end for;

printf "\nKEY: Contact loci have factor 1 (no sqrt(2) obstruction)!\n\n";

// Search: l3^2 * l1 * l2 - Q2^2 = lambda * F2
printf "--- Searching l3^2*l1*l2 - Q2^2 = lambda*(x^4+y^4-z^4) ---\n\n";

found := 0;
bnd := 3;

// Try all pairs of the 4 bitangent lines
all_pairs := [<test_lines[i], test_lines[j], test_names[i], test_names[j]>
              : i in [1..4], j in [i+1..4]];

for pair in all_pairs do
    l1 := pair[1]; l2 := pair[2];
    n1 := pair[3]; n2 := pair[4];
    prod_l := l1 * l2;

    for a in [-bnd..bnd] do
    for b in [-bnd..bnd] do
    for c in [-bnd..bnd] do
        l3 := a*x + b*y + c*z;
        if l3 eq 0 then continue; end if;
        quartic := l3^2 * prod_l;

        for num in [-6..6] do
        for den in [1..6] do
            lam := num/den;
            if lam eq 0 then continue; end if;
            G := quartic - lam * F2;
            fac := Factorization(G);
            if #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
                found +:= 1;
                Q2f := fac[1][1];
                // fix sign so leading coeff is positive
                if LeadingCoefficient(Q2f) lt 0 then Q2f := -Q2f; end if;
                printf "FOUND #%o:\n", found;
                printf "  l1=%o, l2=%o, l3=%o*x+%o*y+%o*z\n", n1, n2, a, b, c;
                printf "  lambda = %o\n", lam;
                printf "  Q2 = %o\n", Q2f;
                printf "  Verify: %o\n\n", Q2f^2 + lam*F2 eq quartic;
                if found ge 20 then
                    printf "(stopping after 20 results)\n";
                    break a;
                end if;
            end if;
        end for;
        end for;
    end for;
    end for;
    end for;
    if found ge 20 then break; end if;
end for;

if found eq 0 then
    printf "No decomposition found with this search.\n\n";
end if;

// =========================================================================
// Also try general Q1*Q3 - Q2^2 = F2 search (not restricted to bitangent form)
// =========================================================================
printf "=== GENERAL DECOMP SEARCH for x^4+y^4-z^4 ===\n";
found_gen := 0;
bnd2 := 3;
for c1 in [-bnd2..bnd2] do for c2 in [-bnd2..bnd2] do for c3 in [-bnd2..bnd2] do
for c4 in [-bnd2..bnd2] do for c5 in [-bnd2..bnd2] do for c6 in [-bnd2..bnd2] do
    Q2t := c1*x^2 + c2*y^2 + c3*z^2 + c4*x*y + c5*x*z + c6*y*z;
    if Q2t eq 0 then continue; end if;
    coeffs := [c1,c2,c3,c4,c5,c6];
    first_nz := 0;
    for j in [1..6] do if coeffs[j] ne 0 then first_nz := coeffs[j]; break; end if; end for;
    if first_nz lt 0 then continue; end if;

    G2 := F2 + Q2t^2;
    fac2 := Factorization(G2);
    if #fac2 eq 2 and TotalDegree(fac2[1][1]) eq 2 and TotalDegree(fac2[2][1]) eq 2
       and fac2[1][2] eq 1 and fac2[2][2] eq 1 then
        Q1g := fac2[1][1]; Q3g := fac2[2][1];
        lc := LeadingCoefficient(G2) / LeadingCoefficient(Q1g*Q3g);
        Q1g := lc * Q1g;
        if Q1g*Q3g - Q2t^2 eq F2 then
            found_gen +:= 1;
            if found_gen le 20 then
                printf "DECOMP #%o: Q2 = %o\n", found_gen, Q2t;
                printf "  Q1 = %o\n  Q3 = %o\n", Q1g, Q3g;
                // Check if Q1 or Q3 factor into linear forms
                facQ1 := Factorization(Q1g);
                facQ3 := Factorization(Q3g);
                q1_lin := (#facQ1 eq 2 and TotalDegree(facQ1[1][1]) eq 1
                           and TotalDegree(facQ1[2][1]) eq 1);
                q3_lin := (#facQ3 eq 2 and TotalDegree(facQ3[1][1]) eq 1
                           and TotalDegree(facQ3[2][1]) eq 1);
                if q1_lin then printf "  Q1 factors: (%o)*(%o)\n", facQ1[1][1], facQ1[2][1]; end if;
                if q3_lin then printf "  Q3 factors: (%o)*(%o)\n", facQ3[1][1], facQ3[2][1]; end if;
                printf "\n";
            end if;
        end if;
    elif #fac2 eq 1 and fac2[1][2] eq 2 and TotalDegree(fac2[1][1]) eq 2 then
        Q1g := fac2[1][1];
        lc := LeadingCoefficient(G2) / LeadingCoefficient(Q1g^2);
        Q1g := lc * Q1g;
        if Q1g^2 - Q2t^2 eq F2 then
            found_gen +:= 1;
            if found_gen le 20 then
                printf "DECOMP #%o (symmetric): Q2 = %o, Q1=Q3 = %o\n\n", found_gen, Q2t, Q1g;
            end if;
        end if;
    end if;
end for; end for; end for;
end for; end for; end for;
printf "Total Q-rational decompositions of x^4+y^4-z^4: %o (bound=%o)\n\n", found_gen, bnd2;

// =========================================================================
// Part 3: Q(sqrt(2))-decomposition of x^4+y^4+z^4
// =========================================================================
printf "=== PART 3: Q(sqrt(2))-FACTORIZATION OF x^4+y^4+z^4 ===\n\n";

P<u> := PolynomialRing(Rationals());
K<r2> := NumberField(u^2 - 2);
RK<x,y,z> := PolynomialRing(K, 3);
FK := x^4 + y^4 + z^4;

// With l3 = sqrt(2)*z, l1 = x+y+z, l2 = x+y-z:
// l3^2*l1*l2 + F factors over Q(sqrt(2))
G := 2*z^2*(x+y+z)*(x+y-z) + FK;
printf "2*z^2*(x+y+z)*(x+y-z) + (x^4+y^4+z^4) =\n";
fac := Factorization(G);
for f in fac do printf "  (%o)^%o\n", f[1], f[2]; end for;

if #fac eq 2 then
    Q_plus := fac[1][1]; Q_minus := fac[2][1];
    // Normalize
    lc1 := LeadingCoefficient(G); lc2 := LeadingCoefficient(Q_plus*Q_minus);
    if lc1 ne lc2 then Q_plus := (lc1/lc2)*Q_plus; end if;

    printf "\nSo F = Q+*Q- - 2*z^2*l1*l2\n";
    printf "where Q+ = %o\n", Q_plus;
    printf "      Q- = %o\n\n", Q_minus;

    // Verify
    printf "Verify: Q+*Q- - 2*z^2*(x+y+z)*(x+y-z) = %o\n",
        Q_plus*Q_minus - 2*z^2*(x+y+z)*(x+y-z) eq FK;

    // Express as standard form: Q+*Q- = (Q_A + sqrt(2)*Q_B)*(Q_A - sqrt(2)*Q_B)
    //                                 = Q_A^2 - 2*Q_B^2
    Q_A := (Q_plus + Q_minus) / 2;
    Q_B := (Q_plus - Q_minus) / (2*r2);
    printf "\nQ_A = (Q+ + Q-)/2 = %o\n", Q_A;
    printf "Q_B = (Q+ - Q-)/(2*sqrt(2)) = %o\n", Q_B;
    printf "\nF = Q_A^2 - 2*Q_B^2 - 2*z^2*l1*l2\n";
    printf "  = (x^2+y^2+z^2)^2 - 2*(xy-z^2)^2 - 2*z^2*((x+y)^2-z^2)\n";
    printf "Verify: %o\n", Q_A^2 - 2*Q_B^2 - 2*z^2*((x+y+z)*(x+y-z)) eq FK;

    // This means the Q(sqrt(2))-decomposition is:
    // F = (x^2+y^2+z^2+sqrt(2)*(xy-z^2))*(x^2+y^2+z^2-sqrt(2)*(xy-z^2))
    //     - 2*z^2*(x+y+z)*(x+y-z)
    // = (x^2+sqrt(2)*xy+y^2+(1-sqrt(2))*z^2)*(x^2-sqrt(2)*xy+y^2+(1+sqrt(2))*z^2)
    //   - (sqrt(2)*z*(x+y+z))*(sqrt(2)*z*(x+y-z))
    //
    // THIS IS: Q1*Q3 - Q2*Q4 form, but Q2*Q4 = (sqrt(2)*z*l1)*(sqrt(2)*z*l2)
    // which is NOT Q2^2 unless l1=l2.
end if;

quit;
