/*******************************************************************************
 * aut_Qi_action.m
 *
 * Check how the Q(i)-automorphism (x:y:z) -> (ix:y:z) acts on J[2].
 * Over F_p with p = 1 mod 4, i exists and we can compute the action.
 *
 * Key question: is eta the unique non-zero J[2](Q) element fixed by
 * the full Aut(C)(Q(i)) = S3 x (Z/4Z)^2?
 ******************************************************************************/

p := 13;
Fp := GF(p);
im := Sqrt(Fp!-1);
w  := Sqrt(Fp!-3);
printf "p = %o, i = %o\n\n", p, im;

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

// V_rat and eta reference
L := [t+u+1, t+u-1, t-u+1, t-u-1];
B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
v1 := B[1] - B[2];
v2 := B[1] - B[3];
q1_ref := KC!(2*t^2 + (1-w)*u^2 + (1+w));
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
// Action of alpha: (x:y:z) -> (ix:y:z), i.e., t -> i*t, u -> u
// On a quadric Q(t,u), alpha*(Q) = Q(i*t, u)
// The half-divisor class transforms accordingly
// =========================================================================
print "=== ACTION OF alpha: (x:y:z) -> (ix:y:z) ===";
print "In affine chart: t -> i*t, u -> u\n";

// Test on each J[2](Q) element represented by a concrete divisor
// We use the 8 elements: 0, v1, v2, v1+v2, eta, eta+v1, eta+v2, eta+v1+v2

// First get concrete divisors for v1 and v2
// v1 = B[1] - B[2] where B[j] = HalfPositive(div(L_j))
// Under alpha: L1 = t+u+1 -> i*t+u+1, L2 -> i*t+u-1, etc.

// Apply alpha to each bitangent half-divisor
L_alpha := [im*t+u+1, im*t+u-1, im*t-u+1, im*t-u-1];
B_alpha := [];
for j in [1..4] do
    D_La := Divisor(KC!L_alpha[j]);
    Ba := HalfPositive(D_La);
    Append(~B_alpha, Ba);
end for;

v1_alpha := B_alpha[1] - B_alpha[2];
v2_alpha := B_alpha[1] - B_alpha[3];

print "alpha*(v1):";
cls_v1a := ClassifyHalf(v1_alpha);
printf "  alpha*(v1) = %o\n", cls_v1a;

print "alpha*(v2):";
cls_v2a := ClassifyHalf(v2_alpha);
printf "  alpha*(v2) = %o\n", cls_v2a;

// alpha*(eta): apply alpha to the Q(sqrt(-3)) Q1
// Q1 = 2x^2 + (1-w)y^2 + (1+w)z^2
// alpha: x->ix, so Q1(ix,y,z) = 2(ix)^2 + (1-w)y^2 + (1+w)z^2
//                              = -2x^2 + (1-w)y^2 + (1+w)z^2
// In affine: -2t^2 + (1-w)u^2 + (1+w)
q1_alpha := KC!(-2*t^2 + (1-w)*u^2 + (1+w));
D_alpha := Divisor(q1_alpha);
ok_a, half_alpha := HalfDiv(D_alpha);
if ok_a then
    print "alpha*(eta):";
    cls_eta_a := ClassifyHalf(half_alpha);
    printf "  alpha*(eta) = %o\n", cls_eta_a;
else
    print "alpha*(eta): odd multiplicities, trying different approach...";
    // Try pulling back through the automorphism more carefully
    // alpha: t -> i*t means q1(alpha(t),u) = q1(i*t, u)
    q1_alpha2 := KC!(2*(im*t)^2 + (1-w)*u^2 + (1+w));
    D_alpha2 := Divisor(q1_alpha2);
    ok_a2, half_alpha2 := HalfDiv(D_alpha2);
    if ok_a2 then
        cls_eta_a2 := ClassifyHalf(half_alpha2);
        printf "  alpha*(eta) = %o\n", cls_eta_a2;
    else
        print "  Still odd multiplicities!";
    end if;
end if;

// =========================================================================
// More systematic: check alpha on all 8 elements
// Represent each by: a0*half_ref + a1*v1 + a2*v2
// Apply alpha, classify result
// =========================================================================
print "\n=== FULL alpha ACTION ON J[2] ===";

// We need alpha*(half_ref), alpha*(v1), alpha*(v2) and then
// alpha is linear so alpha*(a0*eta + a1*v1 + a2*v2) = a0*alpha*(eta) + ...

// But this assumes alpha is a group homomorphism on J[2], which it is
// (automorphisms act as group homomorphisms on the Jacobian)

// Let's just compute alpha on each of the 3 generators
print "Generators:";

// alpha*(v1) and alpha*(v2) already computed above
// For alpha*(eta), use the Q(i) Q1 directly
// Q1 = 2x^2 + 2iz^2 gives eta
// alpha: x->ix, so Q1(ix,y,z) = 2i^2x^2 + 2iz^2 = -2x^2 + 2iz^2
q1_a9 := KC!(2*t^2 + 2*im);       // original Q1 #9
q1_a9_alpha := KC!(-2*t^2 + 2*im); // Q1 after alpha

D_a9a := Divisor(q1_a9_alpha);
ok_a9, half_a9 := HalfDiv(D_a9a);
if ok_a9 then
    cls_a9 := ClassifyHalf(half_a9);
    printf "  alpha*(eta) via Q1#9: %o\n", cls_a9;
else
    printf "  alpha*(eta) via Q1#9: odd multiplicities\n";
end if;

// =========================================================================
// Try beta: (x:y:z) -> (x:iy:z), i.e., t -> t, u -> i*u
// =========================================================================
print "\n=== ACTION OF beta: (x:y:z) -> (x:iy:z) ===";
print "In affine chart: t -> t, u -> i*u\n";

// beta*(v1): L1/L2 = (t+u+1)/(t+u-1) -> (t+i*u+1)/(t+i*u-1)
L_beta := [t+im*u+1, t+im*u-1, t-im*u+1, t-im*u-1];
B_beta := [];
for j in [1..4] do
    D_Lb := Divisor(KC!L_beta[j]);
    Bb := HalfPositive(D_Lb);
    Append(~B_beta, Bb);
end for;
v1_beta := B_beta[1] - B_beta[2];
v2_beta := B_beta[1] - B_beta[3];

cls_v1b := ClassifyHalf(v1_beta);
cls_v2b := ClassifyHalf(v2_beta);
printf "  beta*(v1) = %o\n", cls_v1b;
printf "  beta*(v2) = %o\n", cls_v2b;

// beta*(eta): Q1 = 2x^2+2iz^2, beta: y->iy, so Q1(x,iy,z) = 2x^2+2iz^2 (SAME!)
// So beta fixes Q1 #9
printf "  beta*(eta) via Q1#9: Q1 = 2x^2+2iz^2 is beta-invariant";
printf " -> eta (trivially)\n";

// eta via Q(sqrt(-3)): Q1 = 2x^2+(1-w)y^2+(1+w)z^2
// beta: y->iy, so Q1(x,iy,z) = 2x^2 + (1-w)i^2 y^2 + (1+w)z^2
//                              = 2x^2 - (1-w)y^2 + (1+w)z^2
q1_beta := KC!(2*t^2 - (1-w)*u^2 + (1+w));
D_beta := Divisor(q1_beta);
ok_b, half_beta := HalfDiv(D_beta);
if ok_b then
    cls_b := ClassifyHalf(half_beta);
    printf "  beta*(eta) via Q(sqrt(-3)): %o\n", cls_b;
else
    printf "  beta*(eta) via Q(sqrt(-3)): odd multiplicities\n";
end if;

// =========================================================================
// Summary table
// =========================================================================
print "\n=== SUMMARY ===";
printf "alpha: (x:y:z)->(ix:y:z)\n";
printf "  v1 -> %o,  v2 -> %o\n", cls_v1a, cls_v2a;
printf "beta: (x:y:z)->(x:iy:z)\n";
printf "  v1 -> %o,  v2 -> %o\n", cls_v1b, cls_v2b;

quit;
