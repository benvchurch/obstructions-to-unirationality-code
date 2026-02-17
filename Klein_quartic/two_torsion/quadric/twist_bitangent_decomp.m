/*******************************************************************************
 * twist_bitangent_decomp.m
 *
 * For C2: x^4+y^4-z^4=0 (the twist with rational point (1:0:1)):
 * 1. Find bitangent-based decompositions l3^2*l1*l2 - Q2^2 = lambda*F2
 * 2. Check which of the 24 general decompositions involve bitangent lines
 * 3. Check l1,l2 pairs from ALL rational bitangent lines (not just obvious ones)
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F2 := x^4 + y^4 - z^4;

printf "=== BITANGENT DECOMPOSITIONS OF x^4+y^4-z^4 ===\n\n";

// =========================================================================
// Step 1: Find ALL rational bitangent lines of x^4+y^4-z^4
// =========================================================================
printf "--- Step 1: Rational bitangent lines ---\n";

// A line L is bitangent iff F2|_L = c*(quadratic)^2
// Obvious ones: x+z, x-z, y+z, y-z (contact = y^2 or x^2, factor 1)
// Are there others?

// Check lines ax+by+z=0 (z = -ax-by) for a,b in [-3..3]:
bnd := 3;
printf "Searching lines ax+by+z=0 (a,b in [-%o..%o]):\n", bnd, bnd;
R2<s,t> := PolynomialRing(Rationals(), 2);
bitangent_lines := [];
bitangent_names := [];

for a in [-bnd..bnd] do
for b in [-bnd..bnd] do
    rest := Evaluate(F2, [s, t, -a*s - b*t]);
    fac := Factorization(rest);
    is_bt := false;
    if #fac eq 1 and fac[1][2] eq 2 then
        is_bt := true;
    elif #fac eq 1 and fac[1][2] eq 4 and TotalDegree(fac[1][1]) eq 1 then
        is_bt := true;  // hyperflex
    elif #fac eq 2 then
        // check if it's c * q^2 form
        if fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 1
           and fac[2][2] eq 2 and TotalDegree(fac[2][1]) eq 1 then
            is_bt := true; // Two tangent points (both linear factors squared)
        elif fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2
             and fac[2][2] eq 0 then
            is_bt := true;
        end if;
    end if;
    // More general: check if rest is a perfect square times a constant
    if rest ne 0 and not is_bt then
        lc := LeadingCoefficient(rest);
        if lc ne 0 then
            test := rest / lc;
            is_sq := IsSquare(test);
            if is_sq then is_bt := true; end if;
        end if;
    end if;

    if is_bt then
        l := a*x + b*y + z;
        name := Sprintf("%o*x+%o*y+z", a, b);
        printf "  Bitangent: %o  (F2|_l = %o)\n", name, rest;
        Append(~bitangent_lines, l);
        Append(~bitangent_names, name);
    end if;
end for;
end for;

// Also check lines ax+by (z coefficient = 0)
printf "\nSearching lines ax+y+0*z (x,z plane lines):\n";
for a in [-bnd..bnd] do
for c in [-bnd..bnd] do
    if a eq 0 and c eq 0 then continue; end if;
    rest := Evaluate(F2, [s, -a*s - c*t, t]);  // y = -ax-cz
    if rest eq 0 then continue; end if;
    lc := LeadingCoefficient(rest);
    if lc eq 0 then continue; end if;
    test := rest / lc;
    is_sq, _ := IsSquare(test);
    if is_sq then
        l := a*x + y + c*z;
        name := Sprintf("%o*x+y+%o*z", a, c);
        // Check not already found
        already := false;
        for ll in bitangent_lines do
            if l eq ll or l eq -ll then already := true; break; end if;
        end for;
        if not already then
            printf "  Bitangent: %o  (F2|_l = %o)\n", name, rest;
            Append(~bitangent_lines, l);
            Append(~bitangent_names, name);
        end if;
    end if;
end for;
end for;

// Lines x+ay+cz
printf "\nSearching lines x+ay+cz:\n";
for a in [-bnd..bnd] do
for c in [-bnd..bnd] do
    if a eq 0 and c eq 0 then continue; end if;
    rest := Evaluate(F2, [-a*t - c*s, t, s]);  // x = -ay-cz
    if rest eq 0 then continue; end if;
    lc := LeadingCoefficient(rest);
    if lc eq 0 then continue; end if;
    test := rest / lc;
    is_sq, _ := IsSquare(test);
    if is_sq then
        l := x + a*y + c*z;
        name := Sprintf("x+%o*y+%o*z", a, c);
        already := false;
        for ll in bitangent_lines do
            if l eq ll or l eq -ll then already := true; break; end if;
        end for;
        if not already then
            printf "  Bitangent: %o  (F2|_l = %o)\n", name, rest;
            Append(~bitangent_lines, l);
            Append(~bitangent_names, name);
        end if;
    end if;
end for;
end for;

printf "\nTotal rational bitangent lines found: %o\n\n", #bitangent_lines;

// =========================================================================
// Step 2: For each pair, search l3^2*l1*l2 - Q2^2 = lambda*F2
// =========================================================================
printf "--- Step 2: Bitangent pair decomposition search ---\n\n";

found := 0;
bnd3 := 3;

for i := 1 to #bitangent_lines do
for j := i+1 to #bitangent_lines do
    l1 := bitangent_lines[i]; l2 := bitangent_lines[j];
    prod_l := l1 * l2;

    for a in [-bnd3..bnd3] do
    for b in [-bnd3..bnd3] do
    for c in [-bnd3..bnd3] do
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
                if LeadingCoefficient(Q2f) lt 0 then Q2f := -Q2f; end if;
                printf "FOUND #%o:\n", found;
                printf "  l1=%o, l2=%o\n", bitangent_names[i], bitangent_names[j];
                printf "  l3 = %o*x+%o*y+%o*z, lambda = %o\n", a, b, c, lam;
                printf "  Q2 = %o\n", Q2f;
                printf "  Verify: %o\n\n", Q2f^2 + lam*F2 eq quartic;
                if found ge 30 then break a; end if;
            end if;
        end for;
        end for;
    end for;
    end for;
    end for;
    if found ge 30 then break; end if;
end for;
if found ge 30 then printf "(stopping early)\n"; end if;
end for;

printf "\nTotal bitangent-based decompositions found: %o\n\n", found;

// =========================================================================
// Step 3: Check which of the 24 general decomps have factoring Q1 or Q3
// =========================================================================
printf "--- Step 3: General decomps - do any Q1,Q3 factor? ---\n\n";

found_gen := 0;
found_factoring := 0;
bnd2 := 3;
for c1 in [-bnd2..bnd2] do for c2 in [-bnd2..bnd2] do for c3 in [-bnd2..bnd2] do
for c4 in [-bnd2..bnd2] do for c5 in [-bnd2..bnd2] do for c6 in [-bnd2..bnd2] do
    Q2t := c1*x^2 + c2*y^2 + c3*z^2 + c4*x*y + c5*x*z + c6*y*z;
    if Q2t eq 0 then continue; end if;
    coeffs := [c1,c2,c3,c4,c5,c6];
    first_nz := 0;
    for jj in [1..6] do if coeffs[jj] ne 0 then first_nz := coeffs[jj]; break; end if; end for;
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
            // Check if Q1 or Q3 factor
            facQ1 := Factorization(Q1g);
            facQ3 := Factorization(Q3g);
            q1_fac := (#facQ1 ge 2);
            q3_fac := (#facQ3 ge 2);
            if q1_fac or q3_fac then
                found_factoring +:= 1;
                printf "FACTORING DECOMP #%o:\n", found_factoring;
                printf "  Q2 = %o\n", Q2t;
                printf "  Q1 = %o", Q1g;
                if q1_fac then
                    printf " = ";
                    for f in facQ1 do printf "(%o)^%o", f[1], f[2]; end for;
                end if;
                printf "\n  Q3 = %o", Q3g;
                if q3_fac then
                    printf " = ";
                    for f in facQ3 do printf "(%o)^%o", f[1], f[2]; end for;
                end if;
                printf "\n\n";
            end if;
        end if;
    end if;
end for; end for; end for;
end for; end for; end for;
printf "General decomps: %o total, %o with factoring Q1 or Q3\n\n", found_gen, found_factoring;

// =========================================================================
// Step 4: The identity F = (x^2+y^2+z^2)^2 - 2*e2
// and what it means for x^4+y^4-z^4
// =========================================================================
printf "--- Step 4: Structure of x^4+y^4-z^4 ---\n\n";

// x^4+y^4-z^4 = (x^2+y^2)^2 - 2*x^2*y^2 - z^4
//             = (x^2+y^2-z^2)(x^2+y^2+z^2) - 2*x^2*y^2
// Actually: x^4+y^4-z^4 = (x^2-z^2)(x^2+z^2) + y^4
//                        = (x-z)(x+z)(x^2+z^2) + y^4

// The simplest factoring decomp uses Q1 = (x-z)(x+z) = x^2-z^2:
// F2 = (x^2-z^2)*(?) - Q2^2
// (x^2-z^2)*Q3 = F2 + Q2^2 = x^4+y^4-z^4 + Q2^2

// Try Q2 = y^2: F2 + y^4 = x^4+2*y^4-z^4.
// Is x^4+2*y^4-z^4 divisible by x^2-z^2?
// At x=z: z^4+2*y^4-z^4 = 2*y^4 (nonzero). NO.

// Try Q2 = xy: F2 + x^2*y^2 = x^4+x^2*y^2+y^4-z^4.
// At x=z: z^4+z^2*y^2+y^4-z^4 = y^2*(z^2+y^2). Not 0. NO.

// From decomp #1: Q2 = -xy-xz-yz+z^2.
// Q1 = x^2-xy+xz+y^2+yz+2*z^2, Q3 = x^2+xy-xz+y^2-yz
// Check: det of Q3's matrix
MQ3 := Matrix(Rationals(), 3, 3,
    [1, 1/2, -1/2,
     1/2, 1, -1/2,
     -1/2, -1/2, 0]);
printf "Decomp #1 Q3 = x^2+xy-xz+y^2-yz, det = %o, rank = %o\n",
    Determinant(MQ3), Rank(MQ3);

// Try: can we write Q3 = l_a * l_b?
// det = 0 means Q3 is degenerate (factors)!
if Determinant(MQ3) eq 0 then
    // Q3 is degenerate, find its factorization
    printf "Q3 is DEGENERATE! Factoring...\n";
    fQ3 := Factorization(x^2+x*y-x*z+y^2-y*z);
    for f in fQ3 do printf "  (%o)^%o\n", f[1], f[2]; end for;
end if;

// Also check Q3 from decomp #6:
fQ3_6 := Factorization(x^2+x*y+x*z+y^2+y*z);
printf "\nDecomp #6 Q3 = x^2+xy+xz+y^2+yz: factors = ";
for f in fQ3_6 do printf "(%o)^%o ", f[1], f[2]; end for;
MQ3_6 := Matrix(Rationals(), 3, 3,
    [1, 1/2, 1/2,
     1/2, 1, 1/2,
     1/2, 1/2, 0]);
printf "\n  det = %o, rank = %o\n", Determinant(MQ3_6), Rank(MQ3_6);

// Check all first 12 decomps
printf "\n--- Checking all first decomps for degenerate Q1 or Q3 ---\n";
decomps := [
    <-x*y - x*z - y*z + z^2, x^2 - x*y + x*z + y^2 + y*z + 2*z^2, x^2 + x*y - x*z + y^2 - y*z>,
    <-x*y + x*z + y*z + z^2, x^2 - x*y - x*z + y^2 - y*z + 2*z^2, x^2 + x*y + x*z + y^2 + y*z>,
    <x*y - x*z + y*z + z^2, x^2 - x*y - x*z + y^2 + y*z, x^2 + x*y + x*z + y^2 - y*z + 2*z^2>,
    <x*y + x*z - y*z + z^2, x^2 - x*y + x*z + y^2 - y*z, x^2 + x*y - x*z + y^2 + y*z + 2*z^2>,
    <x^2 - 2*x*y + y^2 - z^2, 2*x^2 - 2*x*y - 2*x*z + 2*y^2 + 2*y*z, x^2 - x*y + x*z + y^2 - y*z>,
    <x^2 + 2*x*y + y^2 - z^2, 2*x^2 + 2*x*y - 2*x*z + 2*y^2 - 2*y*z, x^2 + x*y + x*z + y^2 + y*z>
];

for idx in [1..#decomps] do
    Q2d := decomps[idx][1]; Q1d := decomps[idx][2]; Q3d := decomps[idx][3];
    // Verify
    ver := Q1d*Q3d - Q2d^2 eq F2;
    // Check if Q1 or Q3 degenerate
    for label in ["Q1", "Q3"] do
        Qtest := label eq "Q1" select Q1d else Q3d;
        cfs := [MonomialCoefficient(Qtest, x^2),
                MonomialCoefficient(Qtest, y^2),
                MonomialCoefficient(Qtest, z^2),
                MonomialCoefficient(Qtest, x*y),
                MonomialCoefficient(Qtest, x*z),
                MonomialCoefficient(Qtest, y*z)];
        M := Matrix(Rationals(), 3, 3,
            [cfs[1], cfs[4]/2, cfs[5]/2,
             cfs[4]/2, cfs[2], cfs[6]/2,
             cfs[5]/2, cfs[6]/2, cfs[3]]);
        if Rank(M) le 2 then
            printf "Decomp #%o: %o = %o is DEGENERATE (rank %o)\n",
                idx, label, Qtest, Rank(M);
            facQ := Factorization(Qtest);
            printf "  Factors: ";
            for f in facQ do printf "(%o)^%o ", f[1], f[2]; end for;
            printf "\n";
        end if;
    end for;
end for;

printf "\nDone.\n";
quit;
