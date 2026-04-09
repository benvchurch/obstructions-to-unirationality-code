/*******************************************************************************
 * group_actions_J2.m
 *
 * Group actions on J[2] for the Fermat quartic x^4+y^4+z^4.
 *
 * Merged from: S3_action_J2.m + aut_Qi_action.m
 *
 * Part 1: S3 (coordinate permutations) acting on J[2](F_3).
 * Part 2: Q(i)-automorphisms alpha: (x:y:z)->(ix:y:z) and
 *          beta: (x:y:z)->(x:iy:z) acting on J[2](F_p).
 ******************************************************************************/

// =========== PART 1: S3 ACTION ON J[2](F_3) ===========

printf "=== PART 1: S3 ACTION ON J[2](F_3) ===\n\n";

p := 3;
Fp := GF(p);
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
ff := u^4 + t^4 + 1;
FF := FunctionField(ff);
Cl, m := ClassGroup(FF);
elt_t := FF ! t;
elt_u := FF.1;
invs := Invariants(Cl);
printf "Cl = %o\n", invs;

e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;
printf "J[2] order = %o\n", #J2;
printf "e1 = %o\ne2 = %o\ne3 = %o\n\n", e1, e2, e3;

// HalfDiv and HalfPositive helpers
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

// V_rat generators via bitangent half-divisors
L1 := elt_t + elt_u + 1;  // (x+y+z)/z
L2 := elt_t + elt_u - 1;  // (x+y-z)/z
L3 := elt_t - elt_u + 1;  // (x-y+z)/z
L4 := elt_t - elt_u - 1;  // (x-y-z)/z

B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
B4 := HalfPositive(Divisor(L4));
v1 := (B1-B2) @@ m;
v2 := (B1-B3) @@ m;

printf "V_rat generators:\n";
printf "  v1 = (L1-L2)/2 = %o\n", v1;
printf "  v2 = (L1-L3)/2 = %o\n", v2;
V_rat := sub<Cl | v1, v2>;
printf "  |V_rat cap J[2]| = %o\n\n", #(V_rat meet J2);

// eta from Q1 = 2x^2 + y^2 + z^2 (the Q(sqrt(-3)) decomposition reduced to F_3)
print "=== eta FROM Q1 = 2x^2 + y^2 + z^2 ===";
q1_s := 2*elt_t^2 + elt_u^2 + 1;
D_s := Divisor(q1_s);
ok_s, half_s := HalfDiv(D_s);
printf "All even: %o\n", ok_s;
if ok_s then
    eta_s := half_s @@ m;
    printf "eta = %o\n", eta_s;
    printf "In V_rat? %o\n\n", eta_s in V_rat;
end if;

// S3 images of eta: apply coordinate permutations to Q1 = 2x^2 + y^2 + z^2
print "=== S3 IMAGES OF Q1 = 2x^2 + y^2 + z^2 ===";
// In affine chart z=1:
//   id:   2t^2 + u^2 + 1
//   (xy): t^2 + 2u^2 + 1
//   (xz): t^2 + u^2 + 2
//   (yz): 2t^2 + 1 + u^2 = same as id (symmetric in y,z)

perms := [
    <2*elt_t^2 + elt_u^2 + 1, "id: 2x^2+y^2+z^2">,
    <elt_t^2 + 2*elt_u^2 + 1, "(xy): x^2+2y^2+z^2">,
    <elt_t^2 + elt_u^2 + 2, "(xz): x^2+y^2+2z^2">
];

for data in perms do
    q1_perm := data[1]; name := data[2];
    D_perm := Divisor(q1_perm);
    ok_p, half_p := HalfDiv(D_perm);
    if ok_p then
        cls := half_p @@ m;
        same_as_eta := (ok_s and cls eq eta_s);
        in_vrat := cls in V_rat;
        printf "  %o: class = %o [=eta? %o, V_rat? %o]\n",
            name, cls, same_as_eta, in_vrat;
    else
        printf "  %o: odd multiplicities!\n", name;
    end if;
end for;

// All J[2] elements: which are in V_rat, which = eta?
print "\n=== ALL J[2] ELEMENTS ===";
for a in [0,1] do for b in [0,1] do for c in [0,1] do
    cls := a*e1 + b*e2 + c*e3;
    is_vrat := cls in V_rat;
    is_eta := (ok_s and cls eq eta_s);
    printf "  %oe1+%oe2+%oe3: V_rat=%o, =eta=%o\n", a, b, c, is_vrat, is_eta;
end for; end for; end for;

// Express V_rat generators and eta in e1,e2,e3 basis
print "\n=== V_rat IN e1,e2,e3 BASIS ===";
for a in [0,1] do for b in [0,1] do for c in [0,1] do
    cls := a*e1 + b*e2 + c*e3;
    if cls eq v1 then printf "v1 = %oe1+%oe2+%oe3\n", a, b, c; end if;
    if cls eq v2 then printf "v2 = %oe1+%oe2+%oe3\n", a, b, c; end if;
end for; end for; end for;

if ok_s then
    for a in [0,1] do for b in [0,1] do for c in [0,1] do
        cls := a*e1 + b*e2 + c*e3;
        if cls eq eta_s then printf "eta = %oe1+%oe2+%oe3\n", a, b, c; end if;
    end for; end for; end for;
end if;

// =========== PART 2: Q(i)-AUTOMORPHISM ACTION ON J[2](F_p) ===========

printf "\n\n=== PART 2: Q(i)-AUTOMORPHISM ACTIONS ON J[2](F_p) ===\n\n";

p2 := 13;
Fp2 := GF(p2);
im := Sqrt(Fp2!-1);
w  := Sqrt(Fp2!-3);
printf "p = %o, i = %o\n\n", p2, im;

A2<t2,u2> := AffineSpace(Fp2, 2);
Caff := Curve(A2, t2^4 + u2^4 + 1);
KC := FunctionField(Caff);
t2 := KC.1; u2 := KC.2;

// V_rat and eta reference at p2
LL := [t2+u2+1, t2+u2-1, t2-u2+1, t2-u2-1];
BB := [HalfPositive(Divisor(KC!LL[j])) : j in [1..4]];
v1b := BB[1] - BB[2];
v2b := BB[1] - BB[3];
q1_refb := KC!(2*t2^2 + (1-w)*u2^2 + (1+w));
_, half_refb := HalfDiv(Divisor(q1_refb));

function ClassifyHalf(half_D)
    if not IsPrincipal(2*half_D) then return "NOT 2-torsion"; end if;
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_D - a0*half_refb - a1*v1b - a2*v2b;
        if IsPrincipal(test) then
            labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
            return labels[4*a0 + 2*a1 + a2 + 1];
        end if;
    end for; end for; end for;
    return "UNKNOWN";
end function;

// ---- alpha: (x:y:z) -> (ix:y:z), i.e., t -> i*t, u -> u ----
print "=== ACTION OF alpha: (x:y:z) -> (ix:y:z) ===";
print "In affine chart: t -> i*t, u -> u";
print "";

// alpha on bitangent half-divisors
L_alpha := [im*t2+u2+1, im*t2+u2-1, im*t2-u2+1, im*t2-u2-1];
B_alpha := [];
for j in [1..4] do
    D_La := Divisor(KC!L_alpha[j]);
    Ba := HalfPositive(D_La);
    Append(~B_alpha, Ba);
end for;

v1_alpha := B_alpha[1] - B_alpha[2];
v2_alpha := B_alpha[1] - B_alpha[3];

cls_v1a := ClassifyHalf(v1_alpha);
cls_v2a := ClassifyHalf(v2_alpha);
printf "  alpha*(v1) = %o\n", cls_v1a;
printf "  alpha*(v2) = %o\n", cls_v2a;

// alpha*(eta) via Q1 #9: Q1 = 2x^2+2iz^2
// alpha: x->ix, so Q1(ix,y,z) = -2x^2+2iz^2
q1_a9 := KC!(2*t2^2 + 2*im);
q1_a9_alpha := KC!(-2*t2^2 + 2*im);
D_a9a := Divisor(q1_a9_alpha);
ok_a9, half_a9 := HalfDiv(D_a9a);
if ok_a9 then
    cls_a9 := ClassifyHalf(half_a9);
    printf "  alpha*(eta) via Q1#9: %o\n", cls_a9;
else
    printf "  alpha*(eta) via Q1#9: odd multiplicities\n";
end if;

// alpha*(eta) via Q(sqrt(-3)): Q1 = 2x^2+(1-w)y^2+(1+w)z^2
// alpha: x->ix, so Q1(ix,y,z) = -2x^2+(1-w)y^2+(1+w)z^2
q1_alpha := KC!(-2*t2^2 + (1-w)*u2^2 + (1+w));
D_alpha := Divisor(q1_alpha);
ok_a, half_alpha := HalfDiv(D_alpha);
if ok_a then
    cls_eta_a := ClassifyHalf(half_alpha);
    printf "  alpha*(eta) via Q(sqrt(-3)): %o\n", cls_eta_a;
else
    printf "  alpha*(eta) via Q(sqrt(-3)): odd multiplicities\n";
end if;

// ---- beta: (x:y:z) -> (x:iy:z), i.e., t -> t, u -> i*u ----
print "\n=== ACTION OF beta: (x:y:z) -> (x:iy:z) ===";
print "In affine chart: t -> t, u -> i*u";
print "";

L_beta := [t2+im*u2+1, t2+im*u2-1, t2-im*u2+1, t2-im*u2-1];
B_beta := [];
for j in [1..4] do
    D_Lb := Divisor(KC!L_beta[j]);
    Bbt := HalfPositive(D_Lb);
    Append(~B_beta, Bbt);
end for;
v1_beta := B_beta[1] - B_beta[2];
v2_beta := B_beta[1] - B_beta[3];

cls_v1b := ClassifyHalf(v1_beta);
cls_v2b := ClassifyHalf(v2_beta);
printf "  beta*(v1) = %o\n", cls_v1b;
printf "  beta*(v2) = %o\n", cls_v2b;

// beta*(eta): Q1 = 2x^2+2iz^2, beta: y->iy => Q1 unchanged
printf "  beta*(eta) via Q1#9: Q1 = 2x^2+2iz^2 is beta-invariant";
printf " -> eta (trivially)\n";

// Cross-check with Q(sqrt(-3)) form:
// Q1 = 2x^2+(1-w)y^2+(1+w)z^2
// beta: y->iy, so Q1(x,iy,z) = 2x^2-(1-w)y^2+(1+w)z^2
q1_beta := KC!(2*t2^2 - (1-w)*u2^2 + (1+w));
D_beta := Divisor(q1_beta);
ok_b, half_beta := HalfDiv(D_beta);
if ok_b then
    cls_b := ClassifyHalf(half_beta);
    printf "  beta*(eta) via Q(sqrt(-3)): %o\n", cls_b;
else
    printf "  beta*(eta) via Q(sqrt(-3)): odd multiplicities\n";
end if;

// ---- Summary ----
print "\n=== SUMMARY ===";
printf "alpha: (x:y:z)->(ix:y:z)\n";
printf "  v1 -> %o,  v2 -> %o\n", cls_v1a, cls_v2a;
printf "beta: (x:y:z)->(x:iy:z)\n";
printf "  v1 -> %o,  v2 -> %o\n", cls_v1b, cls_v2b;

quit;
