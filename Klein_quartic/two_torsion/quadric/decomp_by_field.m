/*******************************************************************************
 * decomp_by_field.m
 *
 * Explicit decompositions of F = x^4+y^4+z^4 over various fields,
 * and classify which J[2] class each produces.
 *
 * Key insight: on the conic Q1=0, we need Q2^2 = -F.  The required
 * square root depends on which Q1 (i.e., which pair of bitangents).
 *
 * For Q1 = (x+y+z)(x+y-z): F|_{Q1=0} = 2(x^2+xy+y^2)^2
 *   => need sqrt(-2), so decomp lives over Q(sqrt(-2))
 *
 * For Q1 from the Q(i) search: decomp lives over Q(i)
 ******************************************************************************/

// =========================================================================
// Setup: classify J[2] classes over F_p
// =========================================================================
p := 73;  // 73 = 1 mod 24, so -1,-2,-3 all squares
Fp := GF(p);
w  := Sqrt(Fp!-1);   // i mod p
s3 := Sqrt(Fp!-3);   // sqrt(-3) mod p
s2 := Sqrt(Fp!-2);   // sqrt(-2) mod p
printf "Working over F_%o:  i = %o, sqrt(-3) = %o, sqrt(-2) = %o\n\n", p, w, s3, s2;

A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1;
u := KC.2;

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

// V_rat reference
L := [t+u+1, t+u-1, t-u+1, t-u-1];
B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
v1 := B[1] - B[2];
v2 := B[1] - B[3];

// eta reference (from Q(sqrt(-3)) decomposition)
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

// =========================================================================
// 1. Q(i) decomposition: Q1 = 2x^2+2iz^2, already known to give eta
// =========================================================================
printf "=== Q(i) DECOMPOSITION ===\n";
printf "Q1 = 2x^2 + 2iz^2 => q1 = 2t^2 + 2i (affine z=1)\n";
q1_Qi := KC!(2*t^2 + 2*w);
D1 := Divisor(q1_Qi);
ok1, half1 := HalfDiv(D1);
if ok1 then
    cls1 := ClassifyHalf(half1);
    printf "  Class: %o\n\n", cls1;
else
    printf "  Odd multiplicities!\n\n";
end if;

// =========================================================================
// 2. Q(sqrt(-2)) decomposition from bitangent product
//
// F = Q1*Q3 - Q2^2 where:
//   Q1 = (x+y+z)(x+y-z) = (x+y)^2 - z^2
//   Q2 = sqrt(-2)*(x^2+xy+y^2)
//   Q3 = -(x+y)^2 - z^2
//
// Verify: Q1*Q3 = ((x+y)^2-z^2)(-(x+y)^2-z^2) = z^4-(x+y)^4
//   Q2^2 = -2*(x^2+xy+y^2)^2
//   Q1*Q3 - Q2^2 = z^4-(x+y)^4 + 2*(x^2+xy+y^2)^2
//                = z^4-(x^4+4x^3y+6x^2y^2+4xy^3+y^4)+2(x^4+2x^3y+3x^2y^2+2xy^3+y^4)
//                = x^4+y^4+z^4  ✓
// =========================================================================
printf "=== Q(sqrt(-2)) DECOMPOSITION (bitangent product) ===\n";
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
    // This is expected: (t+u)^2-1 = (t+u+1)(t+u-1) = L1*L2
    // Try using the half-positive of the ratio L1/L2 instead
    printf "  (Q1 factors as L1*L2, try ratio approach)\n";
    // The class from Q1 = L1*L2 is the same as B1+B2 (half-positive of each)
    combined := B[1] + B[2];
    cls_combined := ClassifyHalf(combined);
    printf "  Class from B1+B2: %o\n", cls_combined;
end if;

// Also directly: B1-B2 = v1, B1+B2 = ?
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

// =========================================================================
// 3. Other bitangent products
// =========================================================================
printf "=== ALL BITANGENT PRODUCTS ===\n";
names := ["x+y+z","x+y-z","x-y+z","x-y-z"];
for j1 in [1..4] do for j2 in [j1..4] do
    if j1 eq j2 then continue; end if;
    // Q1 = L_{j1} * L_{j2}, class = B[j1] + B[j2]
    comb := B[j1] + B[j2];
    cls_c := ClassifyHalf(comb);
    printf "  Q1 = (%o)(%o): B%o+B%o = %o\n", names[j1], names[j2], j1, j2, cls_c;
end for; end for;

printf "\n";

// =========================================================================
// 4. Try to find decompositions giving eta+v1, eta+v2, eta+v1+v2
//    These are the "mixed" classes.
// =========================================================================
printf "=== SEARCHING FOR MIXED CLASSES ===\n";
printf "Testing various Q1 forms over extensions...\n\n";

// Over Q(sqrt(-2)): try Q1 with sqrt(-2) coefficients
// Q1 = a*t^2 + b*u^2 + c*t*u + d*t + e*u + f
// with a,b,c,d,e,f in {0,1,-1,s2,-s2}
vals := [Fp!0, Fp!1, -Fp!1, s2, -s2, w, -w, s3, -s3];
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
printf "\nDistinct classes found: %o\n", classes_found;

quit;
