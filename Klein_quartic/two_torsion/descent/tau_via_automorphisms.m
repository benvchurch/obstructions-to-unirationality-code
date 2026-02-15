/*******************************************************************************
 * tau_via_automorphisms.m
 *
 * Compute τ action on J[2] using Magma's function field automorphisms.
 * τ: (t,u) -> (t/i, u/i) is an automorphism of C2: u^4+t^4-1=0.
 *
 * Try: construct τ as a function field map, then use pullback on divisors.
 ******************************************************************************/

function J2Subgroup(Cl, invs)
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    if #gens eq 0 then return sub<Cl | Cl!0>; end if;
    return sub<Cl | gens>;
end function;

p := 17;
printf "p = %o\n", p;
Fp := GF(p);
ii := Fp!0;
for x in Fp do
    if x ne 0 and x^2 eq Fp!(-1) then ii := x; break; end if;
end for;
printf "i = %o\n\n", ii;

Fpt<tt> := FunctionField(Fp);
Fptu<uu> := PolynomialRing(Fpt);
FF2<vv> := FunctionField(uu^4 + tt^4 - 1);
Cl2, mm2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
J2_sub := J2Subgroup(Cl2, invs2);
printf "Cl = %o, |J[2]| = %o\n", invs2, #J2_sub;

// Try 1: Compute automorphism group
printf "\n=== AUTOMORPHISM GROUP ===\n";
try
    A, phi_A, perm := AutomorphismGroup(FF2);
    printf "Aut(C2/F_%o) has order %o\n", p, #A;
    printf "Generators:\n";
    for g in Generators(A) do
        sigma := phi_A(g);
        printf "  g -> sigma(t) = %o, sigma(u) = %o\n",
            sigma(FF2!tt), sigma(vv);
    end for;
catch e
    printf "AutomorphismGroup failed: %o\n", e`Object;
end try;

// Try 2: Construct τ directly as iso
// τ*: f(t,u) -> f(t/i, u/i)
// In FF2: t -> t/i, u -> u/i
printf "\n=== CONSTRUCTING τ DIRECTLY ===\n";

// The element t/i in the base field:
t_over_i := tt * (1/ii);
// The element u/i in FF2:
u_over_i := vv * (1/ii);

// Check: (u/i)^4 + (t/i)^4 = u^4/i^4 + t^4/i^4 = (u^4+t^4)/1 = 1. ✓
printf "Verification: (u/i)^4 + (t/i)^4 = %o (should be 1)\n",
    u_over_i^4 + (FF2!t_over_i)^4;

// For each J[2] generator, compute τ(g) using pullback of the representing
// rational function.
// Strategy: for g in J[2], mm2(g) = D_g (a divisor).
// If we can express D_g = div(f) + D_0 where D_0 is "canonical" (e.g., a
// multiple of the place at infinity), then τ*(D_g) = div(f(t/i, u/i)) + τ*(D_0).
// This requires understanding Magma's divisor representation.

// Alternative: use the Frobenius-at-p approach.
// The key idea: we know both L-poly and we know J[2](F_p) = (Z/2Z)^6 at p=17.
// Instead of computing τ via places, compute it via FUNCTIONS.
//
// For each g in J[2], 2g = 0, so 2*D_g = div(f_g) for some f_g in FF2*.
// τ acts on g by: τ*(g) has 2*τ*(D_g) = div(f_g(t/i, u/i)).
// So τ*(g) - g has: 2*(τ*(D_g) - D_g) = div(f_g(t/i,u/i) / f_g(t,u)).
// If f_g(t/i,u/i)/f_g(t,u) is a square, then τ*(g) = g.

printf "\n=== τ ACTION VIA FUNCTION PULLBACK ===\n";

for k in [1..#invs2] do
    if invs2[k] eq 0 then continue; end if;
    if invs2[k] mod 2 ne 0 then continue; end if;

    g := (invs2[k] div 2) * Cl2.k;
    D := mm2(g);

    // 2g = 0, so 2*D is principal. Compute 2*D:
    D2 := mm2(2*g);  // should be the zero divisor (principal)
    // Actually, mm2(0) gives a principal divisor. We need the function.
    // Let's try: mm2(g) gives D_g. Then 2*D_g ~ 0 (linearly equiv to 0).
    // So 2*D_g = div(h) for some h.

    // Compute the divisor 2*D and check if it's principal
    twoD := 2 * D;
    // Is there a function with this divisor?

    // Try: the class of 2*D should be 0. Check:
    cls_2D := twoD @@ mm2;
    printf "Generator Cl2.%o: invs=%o, g=%o, 2g=%o (zero? %o)\n",
        k, invs2[k], g, cls_2D, cls_2D eq Cl2!0;
end for;

// Try yet another approach: direct substitution
// For each class group generator, get the divisor, find a representing function,
// substitute t->t/i, u->u/i, and find the new class.
printf "\n=== TRYING RIEMANN-ROCH APPROACH ===\n";

// For each J[2] generator g, 2*mm2(g) = div(f_g).
// Find f_g using RiemannRochSpace.
for k in [1..#invs2] do
    if invs2[k] eq 0 then continue; end if;
    if invs2[k] mod 2 ne 0 then continue; end if;

    g := (invs2[k] div 2) * Cl2.k;
    D := mm2(g);

    // We want f such that div(f) = 2D.
    // Equivalently, f in L(-2D) \ {0}.
    // But 2D has degree 0, so L(-2D) = {f : div(f) >= 2D} might be tricky.
    // Instead: 2D ~ 0, so there exists f with div(f) = 2D.
    // This f spans L(-2D) which is 1-dimensional (since deg(2D) = 0 and 2D is principal).

    neg2D := -2*D;
    V, phi_V := RiemannRochSpace(neg2D);
    printf "L(-2D) for gen %o: dim = %o\n", k, Dimension(V);

    if Dimension(V) ge 1 then
        f_g := phi_V(V.1);
        // Check: div(f_g) should equal 2D
        divf := Divisor(f_g);
        // They should be equal as divisors
        // printf "  div(f_g) - 2D = degree %o\n", Degree(divf - 2*D);

        // Now compute τ*(f_g) = f_g(t/i, u/i)
        // In FF2: t is FF2!tt, u is vv.
        // Need to substitute t -> t/i, u -> u/i in the rational function f_g.
        // f_g is an element of FF2 = Fp(t)[u]/(u^4+t^4-1).
        // Express f_g = sum_{j=0}^{3} a_j(t) * u^j where a_j in Fp(t).
        // Then τ*(f_g) = sum a_j(t/i) * (u/i)^j.

        // Extract coefficients
        elt := ElementToSequence(f_g);  // returns [a_0, a_1, a_2, a_3] in Fp(t)
        printf "  f_g has %o coefficients in base field\n", #elt;

        // Substitute: a_j(t) -> a_j(t/i), multiply by (1/i)^j
        tau_fg := FF2!0;
        for j in [1..#elt] do
            // a_j is in Fp(t). Substitute t -> t/i.
            num := Numerator(elt[j]);
            den := Denominator(elt[j]);
            // Substitute in polynomial: t -> t/i
            R := Parent(num);
            // num(t/i) = sum c_k (t/i)^k
            num_sub := Evaluate(num, tt/ii);
            den_sub := Evaluate(den, tt/ii);
            a_sub := num_sub / den_sub;
            tau_fg := tau_fg + (FF2!a_sub) * vv^(j-1) * (FF2!(1/ii))^(j-1);
        end for;

        // Now div(tau_fg) = τ*(2D) = 2*τ*(D).
        // The ratio tau_fg / f_g has divisor 2*(τ*(D) - D).
        // If this ratio is a square, then τ*(g) = g.
        ratio := tau_fg / f_g;
        div_ratio := Divisor(ratio);
        // div_ratio = 2*(τ*(D) - D). Check if this is 2 * (something in J[2]).
        cls_ratio := div_ratio @@ mm2;
        printf "  τ*(f_g)/f_g class: %o\n", cls_ratio;
        // This class represents 2*(τ*(g) - g).
        // If it's 0 in Cl, then τ*(g) - g is in J[2] or is 0.
        // Actually, div(ratio) = div(τ*(f_g)) - div(f_g) = 2*τ*(D) - 2*D.
        // class of div(ratio) = 0 always (it's principal!). Let me reconsider.

        // div(tau_fg/f_g) = 0 in the class group (it's principal).
        // So 2*τ*(D) - 2*D = div(tau_fg/f_g) => 2*(τ*(D)-D) ~ 0 => τ*(D)-D in J[2].
        // But we need τ*(g) exactly: τ*(D) @@ mm2.
        // The problem is τ*(D) is a divisor on C2, and we need its class.
        // div(tau_fg) = 2*τ*(D), so τ*(D) = div(tau_fg)/2 (as divisors).
        // But dividing a divisor by 2 isn't straightforward.

        // Alternative: div(tau_fg) gives us 2*τ*(D). The class of τ*(D) is
        // some element of Cl2. Since 2*τ*(D) is principal, τ*(D) is in J[2].
        // We need: which element of J[2]?

        // Since div(tau_fg) = 2*τ*(D), and τ*(D) represents τ*(g) in J[2]:
        // We know 2*τ*(g) = 0 and the divisor 2*τ*(D) = div(tau_fg).
        // To find τ*(g), we need a "square root" of div(tau_fg) in the class group.
        // i.e., find D' with 2D' ~ div(tau_fg) and class(D') in J[2].
        // But that's D' = τ*(D) = half-divisor of div(tau_fg).
        // We can compute this via the support: div(tau_fg) should have all even valuations.

        div_tau := Divisor(tau_fg);
        supp_tau := Support(div_tau);
        half_div := DivisorGroup(FF2) ! 0;
        all_even := true;
        for P in supp_tau do
            val := Valuation(div_tau, P);
            if val mod 2 ne 0 then
                all_even := false;
                printf "  ODD valuation %o at place of degree %o\n", val, Degree(P);
            else
                half_div := half_div + (val div 2) * (1*P);
            end if;
        end for;

        if all_even then
            tau_g := half_div @@ mm2;
            printf "  τ*(g) = %o  (g = %o, same? %o)\n", tau_g, g, tau_g eq g;
        else
            printf "  div(tau_fg) has odd valuations — not a perfect square\n";
            printf "  (This means the half-divisor approach needs adjustment)\n";
        end if;
    end if;
    printf "\n";
end for;

quit;
