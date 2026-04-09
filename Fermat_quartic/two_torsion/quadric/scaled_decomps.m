/*******************************************************************************
 * scaled_decomps.m
 *
 * Search for and verify scaled quadric decompositions of F = x^4+y^4+z^4.
 *
 * Merged from: scaled_decomp_search.m, verify_scaled.m
 *
 * Contents:
 *   Part 1: Search for cF = Q1*Q3 + Q2^2 with various c values
 *   Part 2: Verify c=-2 decomposition, S3 orbits, and c=-9/2 decomposition
 *   Part 3: 2-torsion class computation (mod p)
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

mons2 := [x^2, y^2, z^2, x*y, x*z, y*z];

// =========== PART 1: SCALED DECOMPOSITION SEARCH ===========
printf "=== PART 1: SCALED DECOMPOSITION SEARCH ===\n";
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

// --- Phase 1: General Q2, bound 2 ---
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

// --- Phase 2: Diagonal Q2 with larger bound ---
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

printf "=== SEARCH TOTAL: %o decompositions found ===\n\n", found + found2;

// =========== PART 2: VERIFICATION OF SCALED DECOMPOSITIONS ===========
printf "=== PART 2: VERIFICATION OF SCALED DECOMPOSITIONS ===\n\n";

// Main decomposition found: c=-2, Q2 = x^2+y^2-z^2
Q2 := x^2 + y^2 - z^2;
Q1 := x^2 - 2*x*y + y^2 + z^2;  // = (x-y)^2 + z^2
Q3 := x^2 + 2*x*y + y^2 + z^2;  // = (x+y)^2 + z^2

printf "Q1 = %o = (x-y)^2 + z^2\n", Q1;
printf "Q2 = %o\n", Q2;
printf "Q3 = %o = (x+y)^2 + z^2\n\n", Q3;

printf "Q1*Q3 = %o\n", Q1*Q3;
printf "Q2^2  = %o\n", Q2^2;
printf "Q1*Q3 + Q2^2 = %o\n", Q1*Q3 + Q2^2;
printf "2*F         = %o\n\n", 2*F;
printf "Q1*Q3 + Q2^2 = 2*F ? %o\n\n", Q1*Q3 + Q2^2 eq 2*F;

// On C: F=0, so Q1*Q3 = -Q2^2
printf "On C: Q1*Q3 = -Q2^2  (since F=0)\n";
printf "So div(Q1) + div(Q3) = 2*div(Q2) in function field of C\n";
printf "=> (1/2)div(Q1) + (1/2)div(Q3) - div(Q2) = 0\n";
printf "=> [(1/2)div(Q1)] = [(1/2)div(Q3)] (same class)\n\n";

// --- All decompositions from S3 x (Z/2)^3 symmetry ---
printf "--- All decompositions from S3 x (Z/2)^3 symmetry ---\n\n";

decomps := [
    <(z-y)^2+x^2, z^2+y^2-x^2, (z+y)^2+x^2, "z<->x">,
    <(x-z)^2+y^2, x^2+z^2-y^2, (x+z)^2+y^2, "z<->y">,
    <(x-y)^2+z^2, x^2+y^2-z^2, (x+y)^2+z^2, "original">
];

for tup in decomps do
    q1 := tup[1]; q2 := tup[2]; q3 := tup[3]; label := tup[4];
    ok := q1*q3 + q2^2 eq 2*F;
    printf "  %o: Q1=%o, Q2=%o => %o\n", label, q1, q2, ok;
end for;

// --- c=-9/2 decomposition ---
printf "\n--- c=-9/2 decomposition ---\n";
Q2b := x^2 - x*y + y^2 - 2*z^2;
G := Q2b^2 + (-9/2)*F;
printf "G = Q2^2 - (9/2)*F = %o\n", G;
fac := Factorization(G);
printf "Factorization:\n";
prod := R!1;
for pair in fac do
    printf "  (%o)^%o\n", pair[1], pair[2];
    prod *:= pair[1]^pair[2];
end for;
lc := LeadingCoefficient(G) / LeadingCoefficient(prod);
printf "Leading coeff ratio: %o\n", lc;
printf "G = %o * (product of factors) ? %o\n\n", lc, lc*prod eq G;

Q1b := fac[1][1]; Q3b := fac[2][1];
printf "So G = %o * Q1 * Q3\n", lc;
printf "=> Q2^2 - (9/2)*F = %o * Q1*Q3\n", lc;
printf "=> -(9/2)*F = %o*Q1*Q3 - Q2^2\n", lc;
printf "=> F = %o * Q1*Q3 - %o * Q2^2\n", -lc*2/9, 2/9;
printf "=> F = %o * (Q1*Q3 - %o*Q2^2)\n\n", -lc*2/9, 1/lc;

// Direct verify
val := lc*Q1b*Q3b - Q2b^2;
printf "(%o)*Q1*Q3 - Q2^2 = %o\n", lc, val;
printf "This equals %o * F? ", val/F;
if val eq 0 then
    printf "zero!\n";
else
    test := val - (LeadingCoefficient(val)/LeadingCoefficient(F))*F;
    if test eq 0 then
        printf "YES, ratio = %o\n", LeadingCoefficient(val)/LeadingCoefficient(F);
    else
        printf "NO\n";
    end if;
end if;

// =========== PART 3: 2-TORSION CLASS COMPUTATION (mod p) ===========
printf "\n=== PART 3: 2-TORSION CLASS COMPUTATION (mod p) ===\n";

p := 73;  // sqrt(-1), sqrt(-2), sqrt(-3) all exist
Fp := GF(p);
A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1; u := KC.2;

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

im := Sqrt(Fp!-1);
s3 := Sqrt(Fp!-3);

// Q1 = (x-y)^2 + z^2, affine z=1: q1 = (t-u)^2 + 1
q1 := KC!((t-u)^2 + 1);
printf "q1 = (t-u)^2 + 1\n";
D_q1 := Divisor(q1);
printf "div(q1):\n";
for pl in Support(D_q1) do
    v := Valuation(D_q1, pl);
    printf "  val = %o, deg = %o\n", v, Degree(pl);
end for;

ok, half_q1 := HalfDiv(D_q1);
printf "HalfDiv works? %o\n\n", ok;

if ok then
    // Classify using the standard basis
    L := [t+u+1, t+u-1, t-u+1, t-u-1];
    B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
    v1 := B[1] - B[2];
    v2 := B[1] - B[3];

    // eta reference from Q(sqrt(-3)) decomposition
    q1_ref := KC!(2*t^2 + (1-s3)*u^2 + (1+s3));
    _, half_ref := HalfDiv(Divisor(q1_ref));

    labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_q1 - a0*half_ref - a1*v1 - a2*v2;
        if IsPrincipal(test) then
            printf "CLASS: [(1/2)div(q1)] = %o\n", labels[4*a0+2*a1+a2+1];
        end if;
    end for; end for; end for;

    printf "\nIs it principal (= 0)? %o\n", IsPrincipal(half_q1);
    printf "Is 2*(1/2)div(q1) principal? %o (should be true for 2-torsion)\n",
        IsPrincipal(2*half_q1);
end if;

quit;
