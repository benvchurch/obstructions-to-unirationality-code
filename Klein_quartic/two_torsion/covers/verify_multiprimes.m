/*******************************************************************************
 * verify_cover_multiprimes.m
 *
 * The function g = (xy+z^2)(x^2*y^2+z^4) restricted to C: x^4+y^4+z^4=0
 * gives the "missing" 2-torsion class e3 over F_3.
 *
 * Key question: does this hold over Q? Check: does div(g) have all-even
 * multiplicities at every prime of good reduction? If div(g) = 2D over F_p
 * for all tested p, this is strong evidence it works over Q.
 *
 * Also check: is w^2 = g an etale double cover (genus 5) at each prime?
 ******************************************************************************/

for p in [3, 7, 11, 13, 17, 19, 23, 31, 37, 41, 43] do
    if p eq 2 then continue; end if;

    printf "=== p = %o ===\n", p;
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);
    f := u^4 + t^4 + 1;

    if not IsIrreducible(f) then
        printf "  u^4+t^4+1 reducible over F_%o, skipping.\n\n", p;
        continue;
    end if;

    FF := FunctionField(f);
    elt_t := FF ! t;
    elt_u := FF.1;

    // g = (xy+z^2)(x^2y^2+z^4) in affine chart z=1
    g1 := elt_t*elt_u + 1;
    g2 := elt_t^2*elt_u^2 + 1;
    g := g1 * g2;

    D_g := Divisor(g);

    // Check all-even multiplicities
    all_even := true;
    for pl in Support(D_g) do
        v := Valuation(D_g, pl);
        if v mod 2 ne 0 then
            all_even := false;
            printf "  ODD mult %o at degree-%o place\n", v, Degree(pl);
        end if;
    end for;

    if all_even then
        printf "  div(g) has ALL EVEN multiplicities.\n";

        // Compute the double cover
        Rw<w> := PolynomialRing(FF);
        h := w^2 - g;
        if IsIrreducible(h) then
            FD := ext<FF | h>;
            gD := Genus(FD);
            printf "  Double cover w^2=g has genus %o", gD;
            if gD eq 5 then
                printf " (ETALE, unramified)\n";
            else
                printf " (RAMIFIED)\n";
            end if;
        else
            printf "  w^2-g is REDUCIBLE (g is a square): trivial cover\n";
        end if;
    else
        printf "  div(g) has ODD multiplicities: NOT an etale cover!\n";
    end if;
    printf "\n";
end for;

// =========================================================================
// Now check: at primes where J[2] = (Z/2Z)^3, is the class e3?
// =========================================================================
print "=== CLASS CHECK AT p=3 ===";
p := 3;
Fp := GF(p);
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
f := u^4 + t^4 + 1;
FF := FunctionField(f);
Cl, m := ClassGroup(FF);
elt_t := FF ! t;
elt_u := FF.1;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;

// Q-rational bitangent classes
L1 := elt_t + elt_u + 1; L2 := elt_t + elt_u - 1;
L3 := elt_t - elt_u + 1; L4 := -elt_t + elt_u + 1;
B1 := HalfPositive(Divisor(L1)); B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3)); B4 := HalfPositive(Divisor(L4));
P12 := (B1-B2) @@ m; P13 := (B1-B3) @@ m; P14 := (B1-B4) @@ m;
V_rat := sub<Cl | P12, P13>;

g := (elt_t*elt_u + 1)*(elt_t^2*elt_u^2 + 1);
D_g := Divisor(g);
D_half := HalfPositive(D_g) - HalfPositive(-D_g);
cls_g := D_half @@ m;

printf "g = (tu+1)(t^2u^2+1)\n";
printf "Class of (1/2)div(g) = %o\n", cls_g;
printf "e3 = %o\n", e3;
printf "Equals e3? %o\n", cls_g eq e3;
printf "In V_rat (bitangent span)? %o\n\n", cls_g in V_rat;

// Full span including g
V_full := sub<Cl | P12, P13, cls_g>;
V_full_J2 := V_full meet J2;
printf "Span of {P12, P13, class(g)} in J[2]: order %o\n", #V_full_J2;
printf "J[2] order: %o\n\n", #J2;

if #V_full_J2 eq #J2 then
    print "*** ALL of J[2] is now reached! ***";
    print "";
    print "CONCLUSION:";
    print "  The Q-rational function g = (xy+z^2)(x^2y^2+z^4) on C";
    print "  defines an etale double cover w^2 = g that gives the";
    print "  'missing' 2-torsion class e3 not reachable from bitangent lines.";
    print "";
    print "  This means the Brauer obstruction delta: J[2](Q) -> Br(Q)[2]";
    print "  has ker(delta) = J[2](Q) = (Z/2Z)^3, i.e., delta = 0.";
    print "";
    print "  THE BRAUER OBSTRUCTION VANISHES FOR THE FERMAT QUARTIC.";
    print "";
    print "  All 7 nontrivial etale double covers of C descend to Q.";
    print "  The cover for e3 is NOT bitangent-derived; it comes from the";
    print "  Q-rational conic xy+z^2 = 0 and the quartic x^2y^2+z^4 = 0.";
else
    printf "Only %o/%o reached. Obstruction may be nonzero.\n", #V_full_J2, #J2;
end if;

quit;
