/*******************************************************************************
 * missing_cover.m
 *
 * For the Fermat quartic C: x^4+y^4+z^4=0 over F_3, construct the etale
 * double cover corresponding to the "missing" 2-torsion class e3 that is
 * NOT in the span of Q-rational bitangent differences.
 *
 * Since Br(F_3)=0, this cover exists over F_3. We want to understand
 * WHY it doesn't lift to Q (the Brauer obstruction).
 ******************************************************************************/

p := 3;
Fp := GF(p);
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
f := u^4 + t^4 + 1;
assert IsIrreducible(f);
FF := FunctionField(f);
Cl, m := ClassGroup(FF);
invs := Invariants(Cl);
printf "Cl(C/F_%o) = Z/%oZ x Z/%oZ x Z/%oZ x Z\n", p, invs[1], invs[2], invs[3];

elt_t := FF ! t;
elt_u := FF.1;

// J[2] generators
e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;
printf "J[2](F_%o) = (Z/2Z)^3, order %o\n\n", p, #J2;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then
            B := B + (v div 2) * pl;
        end if;
    end for;
    return B;
end function;

// Q-rational bitangent classes
L1 := elt_t + elt_u + 1;
L2 := elt_t + elt_u - 1;
L3 := elt_t - elt_u + 1;
L4 := -elt_t + elt_u + 1;

B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
B4 := HalfPositive(Divisor(L4));

P12 := (B1-B2) @@ m;
P13 := (B1-B3) @@ m;
P14 := (B1-B4) @@ m;

printf "P12 = %o\nP13 = %o\nP14 = %o\n\n", P12, P13, P14;

V_rat := sub<Cl | P12, P13>;
printf "V_rat = span(P12,P13) has order %o in J[2]\n", #(V_rat meet J2);

// The missing class: find e3 explicitly
printf "\ne3 = %o\n", e3;
printf "e3 in V_rat? %o\n\n", e3 in V_rat;

// =========================================================================
// Construct the divisor representative of e3
// =========================================================================
print "=== DIVISOR REPRESENTATIVE OF e3 ===";
D_e3 := m(e3);
printf "D_e3 = m(e3) has degree %o\n", Degree(D_e3);
printf "Support:\n";
for pl in Support(D_e3) do
    v := Valuation(D_e3, pl);
    deg_pl := Degree(pl);
    printf "  place of degree %o, multiplicity %o\n", deg_pl, v;
end for;

// =========================================================================
// Find a function f with div(f) = 2*D_e3
// (This f defines the etale double cover w^2 = f)
// =========================================================================
print "";
print "=== FUNCTION FOR THE DOUBLE COVER ===";

// 2*e3 = 0 in Cl, so 2*D_e3 is principal.
// Find f with div(f) = 2*D_e3
D_2e3 := 2*D_e3;
printf "2*D_e3 has degree %o\n", Degree(D_2e3);

// Use RiemannRochSpace: L(2*D_e3 + high_degree) to find f
// Actually, we need f with div(f) = 2*D_e3 exactly.
// Since 2*D_e3 ~ 0, f is a constant times a function.
// Use: if D ~ 0, then D = div(g) for some g.
// The Riemann-Roch space L(-D) = {f : div(f) + (-D) >= 0} = {f : div(f) >= D}
// If D is principal with D = div(g), then L(-D) = g * L(0) = <g>.
// But we want div(f) = D, so f = 1/g.
// L(-2*D_e3) = {f : div(f) >= 2*D_e3}

// Actually, for D = 2*D_e3 ~ 0:
// div(f) = D means f ∈ L(-D) and dim(L(-D)) = 1 (since D ~ 0).
neg_D := -D_2e3;
V, phi := RiemannRochSpace(neg_D);
printf "dim L(-2*D_e3) = %o\n", Dimension(V);

if Dimension(V) gt 0 then
    f_cover := phi(V.1);
    printf "Function f with div(f) >= 2*D_e3:\n";
    printf "  f = %o\n", f_cover;
    D_f := Divisor(f_cover);
    printf "  Zeros and poles of f:\n";
    for pl in Support(D_f) do
        v := Valuation(D_f, pl);
        deg_pl := Degree(pl);
        printf "    degree-%o place, mult %o\n", deg_pl, v;
    end for;
    printf "  Class of div(f): %o\n", D_f @@ m;
    printf "  2*e3 in Cl: %o\n", 2*e3;
end if;

// =========================================================================
// Now construct the double cover D: w^2 = f_cover
// and compute its genus (should be 5 for unramified)
// =========================================================================
print "";
print "=== DOUBLE COVER w^2 = f ===";
printf "The etale double cover is w^2 = f where f = %o\n", f_cover;

// The function field of the double cover
// D is: k(C)[w]/(w^2 - f_cover)
// In Magma: create a degree-2 extension of FF
Rw<w> := PolynomialRing(FF);
g := w^2 - f_cover;
if IsIrreducible(g) then
    print "w^2 - f is irreducible over k(C): nontrivial double cover!";
    FD := ext<FF | g>;

    // Compute genus of D
    gD := Genus(FD);
    printf "Genus of D = %o (expected 5 for unramified double cover of genus 3)\n", gD;

    if gD eq 5 then
        print "Genus matches: the cover is UNRAMIFIED (etale).";
    elif gD eq 3 then
        print "Genus 3: the cover is ramified. Something is wrong.";
    end if;
else
    print "w^2 - f is REDUCIBLE: cover is TRIVIAL!";
    print "This means e3 = 0, contradiction.";
end if;

// =========================================================================
// Express f_cover in terms of the coordinate functions
// This tells us what polynomial relation defines the cover
// =========================================================================
print "";
print "=== ANALYZING f ===";
print "The function f lives in k(C) = F_3(t)[u]/(u^4+t^4+1).";
print "We want to understand what f looks like as a rational function";
print "on C in terms of the original coordinates x,y,z (with z=1, x=t, y=u).";
print "";

// f_cover is an element of FF = F_3(t)[u]/(u^4+t^4+1)
// Print its representation
printf "f = %o\n\n", f_cover;

// Check: what are the zeros and poles of f?
print "Zeros and poles of f on C:";
D_f := Divisor(f_cover);
for pl in Support(D_f) do
    v := Valuation(D_f, pl);
    deg_pl := Degree(pl);
    printf "  degree-%o place, multiplicity %o", deg_pl, v;
    if v gt 0 then printf " (zero)"; else printf " (pole)"; end if;
    printf "\n";
end for;

// =========================================================================
// Now find ALL 28 bitangent lines over F_3^bar and see which give e3
// =========================================================================
print "";
print "=== BITANGENT LINES OVER F_9 ===";
print "Over F_3, the 4th roots of -1 are i, -i where i^2 = -1 = 2.";
print "F_9 = F_3(i) contains sqrt(-1).";
print "";

// Work over F_9 to access more bitangent lines
F9<i> := GF(9);
// i satisfies i^2 + 1 = 0 in F_9 (since char = 3, -1 = 2)
// Actually in GF(9), the primitive element satisfies x^2 + x + 2 = 0 or similar
// Let me find an element with square = -1 = 2
printf "Primitive element of F_9: %o\n", PrimitiveElement(F9);
alpha := PrimitiveElement(F9);
printf "alpha^2 = %o, alpha^4 = %o\n", alpha^2, alpha^4;

// Find sqrt(-1) in F_9
for a in F9 do
    if a^2 eq F9!2 then // 2 = -1 in F_3
        printf "sqrt(-1) in F_9: %o (check: %o^2 = %o)\n", a, a, a^2;
        break;
    end if;
end for;

// Function field over F_9
Fpt9<t9> := FunctionField(F9);
Fptu9<u9> := PolynomialRing(Fpt9);
f9 := u9^4 + t9^4 + 1;
// f9 might factor over F_9
fac9 := Factorization(f9);
printf "\nFactorization of u^4+t^4+1 over F_9: ";
for pair in fac9 do
    printf "(%o)^%o ", pair[1], pair[2];
end for;
printf "\n";

if #fac9 eq 1 then
    FF9 := FunctionField(f9);
    Cl9, m9 := ClassGroup(FF9);
    invs9 := Invariants(Cl9);
    printf "Cl(C/F_9) = ";
    for ii in [1..#invs9] do
        if ii gt 1 then printf " x "; end if;
        if invs9[ii] eq 0 then printf "Z"; else printf "Z/%oZ", invs9[ii]; end if;
    end for;
    printf "\n";

    // J[2](F_9)
    tors_gens9 := [];
    for ii in [1..#invs9] do
        if invs9[ii] ne 0 and invs9[ii] mod 2 eq 0 then
            Append(~tors_gens9, (invs9[ii] div 2) * Cl9.ii);
        end if;
    end for;
    J2_9 := sub<Cl9 | tors_gens9>;
    printf "J[2](F_9) has order %o\n\n", #J2_9;
end if;

quit;
