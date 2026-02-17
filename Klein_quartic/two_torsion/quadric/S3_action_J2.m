/*******************************************************************************
 * S3_action_J2.m
 *
 * How does S3 (coordinate permutations) act on J[2](F_3) for the
 * Fermat quartic x^4+y^4+z^4?  Are e1,e2,e3 permuted by S3?
 ******************************************************************************/

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

// =========================================================================
// S3 action on function field.
// In affine chart z=1: t = x/z, u = y/z.
//
// (x,y,z) -> (y,x,z): t -> u, u -> t    [swap xy]
// (x,y,z) -> (x,z,y): t -> t/u, u -> 1/u [swap yz]
// (x,y,z) -> (z,y,x): t -> 1/t, u -> u/t [swap xz]
//
// For a divisor class [D] in Cl, the action sigma* sends
// the places in D to their images under sigma.
// =========================================================================

// HalfDiv helper
function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

// =========================================================================
// Strategy: Use specific functions to probe the S3 action.
// The bitangent lines x+y+z, x+y-z, x-y+z, x-y-z give V_rat generators.
// The decomposition Q1 gives eta.
// Apply S3 to these functions and see what classes result.
// =========================================================================

// V_rat generators via bitangent half-divisors
function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

L1 := elt_t + elt_u + 1;  // (x+y+z)/z
L2 := elt_t + elt_u - 1;  // (x+y-z)/z
L3 := elt_t - elt_u + 1;  // (x-y+z)/z
L4 := elt_t - elt_u - 1;  // (x-y-z)/z

B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
B4 := HalfPositive(Divisor(L4));
v1 := (B1-B2) @@ m;  // class from L1/L2
v2 := (B1-B3) @@ m;  // class from L1/L3

printf "V_rat generators:\n";
printf "  v1 = (L1-L2)/2 = %o\n", v1;
printf "  v2 = (L1-L3)/2 = %o\n", v2;
V_rat := sub<Cl | v1, v2>;
printf "  |V_rat ∩ J[2]| = %o\n\n", #(V_rat meet J2);

// =========================================================================
// eta from Q(sqrt(-3)) decomposition reduced to F_3
// Q1 = 2x^2 + (1-w)y^2 + (1+w)z^2, w=sqrt(-3)
// Over F_3: w=0, so Q1 = 2x^2 + y^2 + z^2
// =========================================================================
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

// =========================================================================
// S3 images of eta
// Apply coordinate permutations to Q1 = 2x^2 + y^2 + z^2
// =========================================================================
print "=== S3 IMAGES OF Q1 = 2x^2 + y^2 + z^2 ===";

// Identity: Q1 = 2x^2 + y^2 + z^2  -> q1 = 2t^2 + u^2 + 1
// (xy):     Q1 = x^2 + 2y^2 + z^2  -> q1 = t^2 + 2u^2 + 1
// (xz):     Q1 = z^2 + y^2 + 2x^2  = 2x^2 + y^2 + z^2 (SAME!)
//   Wait no: (x,y,z)->(z,y,x): Q1(z,y,x) = 2z^2+y^2+x^2 -> q1 = 2+u^2+t^2 = t^2+u^2+2
// (yz):     Q1(x,z,y) = 2x^2+z^2+y^2 -> q1 = 2t^2 + 1 + u^2 (SAME as identity!)
//   Hmm, Q1 = 2x^2+y^2+z^2 is symmetric in y,z, so (yz) fixes it.

perms := [
    <2*elt_t^2 + elt_u^2 + 1, "id: 2x^2+y^2+z^2">,
    <elt_t^2 + 2*elt_u^2 + 1, "(xy): x^2+2y^2+z^2">,
    <elt_t^2 + elt_u^2 + 2, "(xz): x^2+y^2+2z^2">
];
// (yz) gives same as id since Q1 symmetric in y,z
// (xyz) = (xz)(xy): 2z^2+x^2+y^2 at (x,y,z)->(y,z,x) -> q1 in chart...
// Let's just compute all S3 images of the FORM 2x^2+y^2+z^2

print "Direct approach: evaluate 2a^2+b^2+c^2 for each permutation of (x,y,z)";
for data in perms do
    q1_perm := data[1];
    name := data[2];
    D_perm := Divisor(q1_perm);
    ok_p, half_p := HalfDiv(D_perm);
    if ok_p then
        cls := half_p @@ m;
        same_as_eta := (cls eq eta_s);
        in_vrat := cls in V_rat;
        printf "  %o: class = %o [=eta? %o, V_rat? %o]\n",
            name, cls, same_as_eta, in_vrat;
    else
        printf "  %o: odd multiplicities!\n", name;
    end if;
end for;

// =========================================================================
// Check all 8 elements of J[2]: which are in V_rat, which = eta?
// =========================================================================
print "\n=== ALL J[2] ELEMENTS ===";
for a in [0,1] do for b in [0,1] do for c in [0,1] do
    cls := a*e1 + b*e2 + c*e3;
    is_vrat := cls in V_rat;
    is_eta := (ok_s and cls eq eta_s);
    printf "  %oe1+%oe2+%oe3: V_rat=%o, =eta=%o\n", a, b, c, is_vrat, is_eta;
end for; end for; end for;

// =========================================================================
// Express V_rat generators in e1,e2,e3 basis
// =========================================================================
print "\n=== V_rat IN e1,e2,e3 BASIS ===";
for a in [0,1] do for b in [0,1] do for c in [0,1] do
    cls := a*e1 + b*e2 + c*e3;
    if cls eq v1 then printf "v1 = %oe1+%oe2+%oe3\n", a, b, c; end if;
    if cls eq v2 then printf "v2 = %oe1+%oe2+%oe3\n", a, b, c; end if;
end for; end for; end for;

// eta in basis
if ok_s then
    for a in [0,1] do for b in [0,1] do for c in [0,1] do
        cls := a*e1 + b*e2 + c*e3;
        if cls eq eta_s then printf "eta = %oe1+%oe2+%oe3\n", a, b, c; end if;
    end for; end for; end for;
end if;

quit;
