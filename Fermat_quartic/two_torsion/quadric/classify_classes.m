/*******************************************************************************
 * classify_classes.m
 *
 * Methodology verification and J[2] class classification for quadric
 * decompositions of F = x^4+y^4+z^4.
 *
 * Merged from: check_consistency.m, decomp_by_field.m, all_classes.m
 *
 * Contents:
 *   Part 1: Methodology verification (HalfDiv vs HalfPositive consistency)
 *   Part 2: Classification of decompositions over various fields by J[2] class
 *   Part 3: All rational Q1 from scaled decomposition - class computation
 ******************************************************************************/

// =========== PART 1: METHODOLOGY VERIFICATION ===========
/*
 * Key identities: on C, F = Q1*Q3 - Q2^2 gives Q1*Q3 = Q2^2.
 * In the function field (affine z=1), q1 = Q1(t,u,1) etc.
 *
 * div(q1) + div(q3) = 2*div(q2), so:
 *   (1/2)div(q1) + (1/2)div(q3) = div(q2) ~ 0  (principal)
 *   => [(1/2)div(q1)] = [(1/2)div(q3)]  (same class)
 *
 * The nontrivial class is [(1/2)div(q1)] itself.
 * Since q1 = Q1(t,u,1) = Q1(x,y,z)/z^2, we have
 *   div(q1) = (Q1.C) - 2H  where H = (z=0).C
 * so (1/2)div(q1) = D1 - H  where D1 = (1/2)(Q1.C).
 * This is degree 0 and 2-torsion: the correct class.
 *
 * For bitangent lines L = (ax+by+cz)/z:
 *   div(L/z) = (L.C) - H
 * L is bitangent => L.C = 2*B_L (even), but H has 4 points at infinity
 * each with multiplicity 1 (ODD), so div(L/z) is NOT even.
 * That's why HalfPositive is used: B_j = (1/2)(positive part of div(L_j/z))
 * and v1 = B1-B2 = (1/2)div(L1/L2) since poles cancel.
 */

printf "=== PART 1: METHODOLOGY VERIFICATION ===\n\n";

p := 73;  // -1,-2,-3 all squares
Fp := GF(p);
im := Sqrt(Fp!-1);
s3 := Sqrt(Fp!-3);
s2 := Sqrt(Fp!-2);
printf "p = %o, i = %o, sqrt(-3) = %o, sqrt(-2) = %o\n\n", p, im, s3, s2;

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

// --- 1. Check: div(L_j) has ODD valuations at poles (so HalfDiv fails) ---
printf "--- 1. Bitangent line divisors ---\n";
L1 := KC!(t+u+1);
D_L1 := Divisor(L1);
printf "div(t+u+1):\n";
for pl in Support(D_L1) do
    v := Valuation(D_L1, pl);
    printf "  place: val=%o\n", v;
end for;
ok1, _ := HalfDiv(D_L1);
printf "HalfDiv works? %o  (expected: false, poles are odd)\n\n", ok1;

// --- 2. Check: div(L1/L2) IS even, and (1/2)div(L1/L2) = B1-B2 ---
printf "--- 2. Ratio L1/L2 ---\n";
L2 := KC!(t+u-1);
ratio := L1/L2;
D_ratio := Divisor(ratio);
printf "div((t+u+1)/(t+u-1)):\n";
for pl in Support(D_ratio) do
    v := Valuation(D_ratio, pl);
    printf "  place: val=%o\n", v;
end for;
ok_r, half_ratio := HalfDiv(D_ratio);
printf "HalfDiv works? %o  (poles cancel, all even)\n", ok_r;

B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
v1_direct := B1 - B2;
if ok_r then
    delta := v1_direct - half_ratio;
    printf "B1-B2 = (1/2)div(L1/L2)? %o\n\n", IsPrincipal(delta);
end if;

// --- 3. Check: div(q1) for quadric IS even (HalfDiv works) ---
printf "--- 3. Quadric Q1 = 2t^2+2i (from Q(i) decomposition) ---\n";
q1 := KC!(2*t^2 + 2*im);
D_q1 := Divisor(q1);
printf "div(2t^2+2i):\n";
for pl in Support(D_q1) do
    v := Valuation(D_q1, pl);
    printf "  place: val=%o\n", v;
end for;
ok_q1, half_q1 := HalfDiv(D_q1);
printf "HalfDiv works? %o  (all valuations even)\n\n", ok_q1;

// --- 4. Verify: Q1 and Q3 give SAME class ---
printf "--- 4. Q1 vs Q3 from decomposition ---\n";
printf "F = Q1*Q3 - Q2^2 with Q1=2X^2+2iZ^2, Q2=iY^2, Q3=X^2/2-iZ^2/2\n";
q3 := KC!((1/Fp!2)*t^2 - (im/Fp!2));
D_q3 := Divisor(q3);
ok_q3, half_q3 := HalfDiv(D_q3);
printf "Q3 half-divisor exists? %o\n", ok_q3;

if ok_q1 and ok_q3 then
    delta13 := half_q1 - half_q3;
    printf "[(1/2)div(q1)] = [(1/2)div(q3)]? %o\n", IsPrincipal(delta13);

    q2 := KC!(im*u^2);
    D_q2 := Divisor(q2);
    sum_halves := half_q1 + half_q3;
    delta_sum := sum_halves - D_q2;
    printf "(1/2)div(q1) + (1/2)div(q3) = div(q2)? %o\n", IsPrincipal(delta_sum);
end if;

// --- 5. Set up classification basis ---
printf "\n--- 5. Classification ---\n";
L := [t+u+1, t+u-1, t-u+1, t-u-1];
B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
v1 := B[1] - B[2];
v2 := B[1] - B[3];

// eta reference
q1_ref := KC!(2*t^2 + (1-s3)*u^2 + (1+s3));
_, half_ref := HalfDiv(Divisor(q1_ref));

function ClassifyHalf(half_D)
    if not IsPrincipal(2*half_D) then return "NOT 2-torsion"; end if;
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_D - a0*half_ref - a1*v1 - a2*v2;
        if IsPrincipal(test) then
            labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
            return labels[4*a0 + 2*a1 + a2 + 1];
        end if;
    end for; end for; end for;
    return "UNKNOWN";
end function;

if ok_q1 then
    cls_q1 := ClassifyHalf(half_q1);
    printf "  [(1/2)div(q1)] = %o\n", cls_q1;
end if;
if ok_q3 then
    cls_q3 := ClassifyHalf(half_q3);
    printf "  [(1/2)div(q3)] = %o\n", cls_q3;
end if;

cls_v1 := ClassifyHalf(v1);
printf "  v1 = B1-B2 = (1/2)div(L1/L2) = %o\n", cls_v1;

printf "  (1/2)div(q1) principal? %o (should be false for eta)\n", IsPrincipal(half_q1);

// --- 6. Degree check ---
printf "\n--- 6. Degree check ---\n";
deg_q1 := &+[Valuation(D_q1, pl) * Degree(pl) : pl in Support(D_q1)];
printf "deg(div(q1)) = %o (should be 0)\n", deg_q1;
deg_half := &+[Valuation(half_q1, pl) * Degree(pl) : pl in Support(half_q1)];
printf "deg((1/2)div(q1)) = %o (should be 0)\n", deg_half;

printf "\nSUMMARY: The scripts compute [(1/2)div(q1)] where q1 = Q1(t,u,1).\n";
printf "Since div(q1) = Q1.C - 2H, we get (1/2)div(q1) = D1 - H.\n";
printf "This IS the correct 2-torsion class [D1 - H] in J(C).\n";
printf "Q1 and Q3 give the same class (their sum = div(q2) is trivial).\n\n";

// =========== PART 2: CLASSIFICATION OVER VARIOUS FIELDS ===========
printf "=== PART 2: CLASSIFICATION OVER VARIOUS FIELDS ===\n\n";

// --- Q(i) decomposition ---
printf "--- Q(i) decomposition ---\n";
printf "Q1 = 2x^2 + 2iz^2 => q1 = 2t^2 + 2i (affine z=1)\n";
q1_Qi := KC!(2*t^2 + 2*im);
D1 := Divisor(q1_Qi);
ok1, half1 := HalfDiv(D1);
if ok1 then
    cls1 := ClassifyHalf(half1);
    printf "  Class: %o\n\n", cls1;
else
    printf "  Odd multiplicities!\n\n";
end if;

// --- Q(sqrt(-2)) decomposition from bitangent product ---
printf "--- Q(sqrt(-2)) decomposition (bitangent product) ---\n";
printf "Q1 = (x+y+z)(x+y-z),  Q2 = sqrt(-2)*(x^2+xy+y^2)\n";

// Affine z=1: Q1 = (t+u+1)(t+u-1) = (t+u)^2-1
q1_s2 := KC!((t+u)^2 - 1);
D_s2 := Divisor(q1_s2);
ok_s2, half_s2 := HalfDiv(D_s2);
if ok_s2 then
    cls_s2 := ClassifyHalf(half_s2);
    printf "  Class from Q1 = (t+u)^2-1: %o\n", cls_s2;
else
    printf "  Odd multiplicities for (t+u)^2-1!\n";
    printf "  (Q1 factors as L1*L2, try ratio approach)\n";
    combined := B[1] + B[2];
    cls_combined := ClassifyHalf(combined);
    printf "  Class from B1+B2: %o\n", cls_combined;
end if;

printf "\n  For reference:\n";
printf "    B[1]-B[2] = v1 (by definition)\n";
combined12 := B[1] + B[2];
cls12 := ClassifyHalf(combined12);
printf "    B[1]+B[2] class: %o\n", cls12;
combined13 := B[1] + B[3];
cls13 := ClassifyHalf(combined13);
printf "    B[1]+B[3] class: %o\n", cls13;
combined14 := B[1] + B[4];
cls14 := ClassifyHalf(combined14);
printf "    B[1]+B[4] class: %o\n", cls14;

printf "\n";

// --- All bitangent products ---
printf "--- All bitangent products ---\n";
names := ["x+y+z","x+y-z","x-y+z","x-y-z"];
for j1 in [1..4] do for j2 in [j1..4] do
    if j1 eq j2 then continue; end if;
    comb := B[j1] + B[j2];
    cls_c := ClassifyHalf(comb);
    printf "  Q1 = (%o)(%o): B%o+B%o = %o\n", names[j1], names[j2], j1, j2, cls_c;
end for; end for;

printf "\n";

// --- Search for mixed classes ---
printf "--- Searching for mixed classes ---\n";
printf "Testing various Q1 forms over extensions...\n\n";

vals := [Fp!0, Fp!1, -Fp!1, s2, -s2, im, -im, s3, -s3];
count := 0;
classes_found := {};
for a in vals do for b in vals do for c in [Fp!0] do
    for f in vals do
        if a eq 0 and b eq 0 and f eq 0 then continue; end if;
        q := a*t^2 + b*u^2 + c*t*u + f;
        D := Divisor(q);
        ok, half := HalfDiv(D);
        if ok then
            cls := ClassifyHalf(half);
            if cls notin classes_found then
                Include(~classes_found, cls);
                printf "  q = %o*t^2 + %o*u^2 + %o  -> %o\n", a, b, f, cls;
            end if;
            count +:= 1;
        end if;
    end for;
end for; end for; end for;
printf "\nDistinct classes found: %o\n\n", classes_found;

// =========== PART 3: ALL RATIONAL Q1 - CLASS COMPUTATION ===========
printf "=== PART 3: ALL RATIONAL Q1 - CLASS COMPUTATION ===\n\n";

printf "--- Rational decompositions 2F = Q1*Q3 + Q2^2 ---\n\n";

// Decomposition 1: Q1 = (x-y)^2+z^2, affine z=1: (t-u)^2+1
printf "--- Decomp 1: Q1 = (x-y)^2+z^2 ---\n";
q1a := KC!((t-u)^2 + 1);
D1 := Divisor(q1a);
ok1, h1 := HalfDiv(D1);
printf "  HalfDiv: %o, class = %o\n\n", ok1, ok1 select ClassifyHalf(h1) else "N/A";

// Decomposition 1': Q3 = (x+y)^2+z^2, affine z=1: (t+u)^2+1
printf "--- Decomp 1': Q3 = (x+y)^2+z^2 ---\n";
q3a := KC!((t+u)^2 + 1);
D3 := Divisor(q3a);
ok3, h3 := HalfDiv(D3);
printf "  HalfDiv: %o, class = %o\n", ok3, ok3 select ClassifyHalf(h3) else "N/A";
if ok1 and ok3 then
    printf "  Q1 and Q3 same class? %o\n\n", IsPrincipal(h1-h3);
end if;

// Decomposition 2: Q1 = (y-z)^2+x^2 = x^2+y^2-2yz+z^2, affine z=1: t^2+u^2-2u+1
printf "--- Decomp 2: Q1 = x^2+(y-z)^2 ---\n";
q1b := KC!(t^2 + u^2 - 2*u + 1);
D1b := Divisor(q1b);
ok1b, h1b := HalfDiv(D1b);
printf "  HalfDiv: %o, class = %o\n\n", ok1b, ok1b select ClassifyHalf(h1b) else "N/A";

// Decomposition 2': Q3 = x^2+(y+z)^2, affine z=1: t^2+u^2+2u+1
printf "--- Decomp 2': Q3 = x^2+(y+z)^2 ---\n";
q3b := KC!(t^2 + u^2 + 2*u + 1);
D3b := Divisor(q3b);
ok3b, h3b := HalfDiv(D3b);
printf "  HalfDiv: %o, class = %o\n\n", ok3b, ok3b select ClassifyHalf(h3b) else "N/A";

// Decomposition 3: Q1 = (x-z)^2+y^2, affine z=1: (t-1)^2+u^2
printf "--- Decomp 3: Q1 = (x-z)^2+y^2 ---\n";
q1c := KC!((t-1)^2 + u^2);
D1c := Divisor(q1c);
ok1c, h1c := HalfDiv(D1c);
printf "  HalfDiv: %o, class = %o\n\n", ok1c, ok1c select ClassifyHalf(h1c) else "N/A";

// Decomposition 3': Q3 = (x+z)^2+y^2, affine z=1: (t+1)^2+u^2
printf "--- Decomp 3': Q3 = (x+z)^2+y^2 ---\n";
q3c := KC!((t+1)^2 + u^2);
D3c := Divisor(q3c);
ok3c, h3c := HalfDiv(D3c);
printf "  HalfDiv: %o, class = %o\n\n", ok3c, ok3c select ClassifyHalf(h3c) else "N/A";

// --- c=-9/2 decomposition ---
printf "--- c=-9/2 decomp: Q3_new = x^2-10/7*xy+y^2+1/7*z^2 ---\n";
q3_new := KC!(t^2 - (Fp!10/Fp!7)*t*u + u^2 + Fp!1/Fp!7);
D3_new := Divisor(q3_new);
ok_new, h_new := HalfDiv(D3_new);
printf "  HalfDiv: %o, class = %o\n\n", ok_new, ok_new select ClassifyHalf(h_new) else "N/A";

// --- Summary ---
printf "=== SUMMARY ===\n";
printf "Rational decomposition 2F = Q1*Q3 + Q2^2 exists!\n";
printf "Three families from S3 symmetry.\n";
printf "Classes realized by rational Q1:\n";
if ok1 then printf "  (x-y)^2+z^2 -> %o\n", ClassifyHalf(h1); end if;
if ok3 then printf "  (x+y)^2+z^2 -> %o\n", ClassifyHalf(h3); end if;
if ok1b then printf "  x^2+(y-z)^2 -> %o\n", ClassifyHalf(h1b); end if;
if ok3b then printf "  x^2+(y+z)^2 -> %o\n", ClassifyHalf(h3b); end if;
if ok1c then printf "  (x-z)^2+y^2 -> %o\n", ClassifyHalf(h1c); end if;
if ok3c then printf "  (x+z)^2+y^2 -> %o\n", ClassifyHalf(h3c); end if;

quit;
