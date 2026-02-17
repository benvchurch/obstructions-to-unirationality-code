/*******************************************************************************
 * verify_scaled.m
 *
 * Verify the scaled decompositions found by the search.
 * Key finding: 2F = Q1*Q3 + Q2^2 (note the + sign!)
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

printf "=== VERIFICATION OF SCALED DECOMPOSITIONS ===\n\n";

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

// =========================================================================
// By S3 symmetry of F, list all decompositions from permutations
// =========================================================================
printf "=== ALL DECOMPOSITIONS FROM S3 x (Z/2)^3 SYMMETRY ===\n\n";

decomps := [
    // From x<->y permutation (gives same decomp up to Q1<->Q3)
    // From z<->x:
    <(z-y)^2+x^2, z^2+y^2-x^2, (z+y)^2+x^2, "z<->x">,
    // From z<->y:
    <(x-z)^2+y^2, x^2+z^2-y^2, (x+z)^2+y^2, "z<->y">,
    // Original:
    <(x-y)^2+z^2, x^2+y^2-z^2, (x+y)^2+z^2, "original">
];

for tup in decomps do
    q1 := tup[1]; q2 := tup[2]; q3 := tup[3]; label := tup[4];
    ok := q1*q3 + q2^2 eq 2*F;
    printf "  %o: Q1=%o, Q2=%o => %o\n", label, q1, q2, ok;
end for;

// =========================================================================
// Also check the c=-9/2 decomposition
// =========================================================================
printf "\n=== c=-9/2 DECOMPOSITION ===\n";
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
    // Check if proportional to F
    test := val - (LeadingCoefficient(val)/LeadingCoefficient(F))*F;
    if test eq 0 then
        printf "YES, ratio = %o\n", LeadingCoefficient(val)/LeadingCoefficient(F);
    else
        printf "NO\n";
    end if;
end if;

// =========================================================================
// Compute the 2-torsion class from Q1 = (x-y)^2 + z^2
// =========================================================================
printf "\n=== 2-TORSION CLASS COMPUTATION (mod p) ===\n";

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
    im := Sqrt(Fp!-1);
    s3 := Sqrt(Fp!-3);

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
