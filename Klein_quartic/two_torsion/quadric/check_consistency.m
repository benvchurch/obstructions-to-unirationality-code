/*******************************************************************************
 * check_consistency.m
 *
 * Verify that the 2-torsion class computation is correct.
 *
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
 ******************************************************************************/

p := 73;  // -1,-2,-3 all squares
Fp := GF(p);
im := Sqrt(Fp!-1);
s3 := Sqrt(Fp!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n\n", p, im, s3;

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

// =========================================================================
// 1. Check: div(L_j) has ODD valuations at poles (so HalfDiv fails)
// =========================================================================
printf "=== BITANGENT LINE DIVISORS ===\n";
L1 := KC!(t+u+1);
D_L1 := Divisor(L1);
printf "div(t+u+1):\n";
for pl in Support(D_L1) do
    v := Valuation(D_L1, pl);
    printf "  place: val=%o\n", v;
end for;
ok1, _ := HalfDiv(D_L1);
printf "HalfDiv works? %o  (expected: false, poles are odd)\n\n", ok1;

// =========================================================================
// 2. Check: div(L1/L2) IS even, and (1/2)div(L1/L2) = B1-B2
// =========================================================================
printf "=== RATIO L1/L2 ===\n";
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

// Compare with B1-B2
B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
v1_direct := B1 - B2;
if ok_r then
    delta := v1_direct - half_ratio;
    printf "B1-B2 = (1/2)div(L1/L2)? %o\n\n", IsPrincipal(delta);
end if;

// =========================================================================
// 3. Check: div(q1) for quadric IS even (HalfDiv works)
// =========================================================================
printf "=== QUADRIC Q1 = 2t^2+2i (from Q(i) decomposition) ===\n";
q1 := KC!(2*t^2 + 2*im);
D_q1 := Divisor(q1);
printf "div(2t^2+2i):\n";
for pl in Support(D_q1) do
    v := Valuation(D_q1, pl);
    printf "  place: val=%o\n", v;
end for;
ok_q1, half_q1 := HalfDiv(D_q1);
printf "HalfDiv works? %o  (all valuations even)\n\n", ok_q1;

// =========================================================================
// 4. Verify: Q1 and Q3 give SAME class
// =========================================================================
printf "=== Q1 vs Q3 FROM DECOMPOSITION ===\n";
printf "F = Q1*Q3 - Q2^2 with Q1=2X^2+2iZ^2, Q2=iY^2, Q3=X^2/2-iZ^2/2\n";
q3 := KC!((1/Fp!2)*t^2 - (im/Fp!2));
D_q3 := Divisor(q3);
ok_q3, half_q3 := HalfDiv(D_q3);
printf "Q3 half-divisor exists? %o\n", ok_q3;

if ok_q1 and ok_q3 then
    // Check they're the same class
    delta13 := half_q1 - half_q3;
    printf "[(1/2)div(q1)] = [(1/2)div(q3)]? %o\n", IsPrincipal(delta13);

    // Check their sum = div(q2)
    q2 := KC!(im*u^2);
    D_q2 := Divisor(q2);
    sum_halves := half_q1 + half_q3;
    delta_sum := sum_halves - D_q2;
    printf "(1/2)div(q1) + (1/2)div(q3) = div(q2)? %o\n", IsPrincipal(delta_sum);
end if;

// =========================================================================
// 5. Check: the class is nontrivial (= eta)
// =========================================================================
printf "\n=== CLASSIFICATION ===\n";
// V_rat references
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

// Is v1 nontrivial?
cls_v1 := ClassifyHalf(v1);
printf "  v1 = B1-B2 = (1/2)div(L1/L2) = %o\n", cls_v1;

// Is (1/2)div(q1) principal?
printf "  (1/2)div(q1) principal? %o (should be false for eta)\n", IsPrincipal(half_q1);

// =========================================================================
// 6. Degree check: div(q1) has degree 0 in function field
// =========================================================================
printf "\n=== DEGREE CHECK ===\n";
deg_q1 := &+[Valuation(D_q1, pl) * Degree(pl) : pl in Support(D_q1)];
printf "deg(div(q1)) = %o (should be 0)\n", deg_q1;
deg_half := &+[Valuation(half_q1, pl) * Degree(pl) : pl in Support(half_q1)];
printf "deg((1/2)div(q1)) = %o (should be 0)\n", deg_half;

printf "\n=== SUMMARY ===\n";
printf "The scripts compute [(1/2)div(q1)] where q1 = Q1(t,u,1).\n";
printf "Since div(q1) = Q1.C - 2H, we get (1/2)div(q1) = D1 - H.\n";
printf "This IS the correct 2-torsion class [D1 - H] in J(C).\n";
printf "Q1 and Q3 give the same class (their sum = div(q2) is trivial).\n";

quit;
