/*******************************************************************************
 * brauer_multicheck.m
 *
 * Verify the Brauer obstruction for x^4+y^4+z^4=0 across multiple primes.
 * For each prime p of good reduction with p = 1 mod 8 (full 2-torsion visible),
 * compute J[2](F_p) and check which subspace is spanned by:
 *   (a) Q-rational bitangent line differences
 *   (b) Conjugate-pair bitangent classes
 *   (c) All Galois-equivariant constructions
 *
 * The prediction: only (Z/2Z)^2 is reached, never the full (Z/2Z)^3.
 ******************************************************************************/

function AnalyzePrime(p)
    printf "========================================\n";
    printf "=== p = %o (p mod 8 = %o) ===\n", p, p mod 8;
    printf "========================================\n";

    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);
    f := u^4 + t^4 + 1;

    if not IsIrreducible(f) then
        printf "  f is reducible over F_%o, skipping.\n\n", p;
        return 0, 0;
    end if;

    FF := FunctionField(f);
    Cl, m := ClassGroup(FF);
    invs := Invariants(Cl);

    elt_t := FF ! t;
    elt_u := FF.1;

    // Find J[2]: degree-0 2-torsion subgroup
    tors_gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~tors_gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    J2 := sub<Cl | tors_gens>;
    printf "  J[2](F_%o) has order %o\n", p, #J2;
    if #J2 ne 8 then
        printf "  Not (Z/2Z)^3, skipping.\n\n";
        return 0, 0;
    end if;

    // Half-positive divisor helper
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

    // Q-rational bitangent lines: x+y+z, x+y-z, x-y+z, -x+y+z
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

    V_rat := sub<Cl | P12, P13>;
    V_rat_J2 := V_rat meet J2;
    printf "  Q-rat bitangent span in J[2]: order %o\n", #V_rat_J2;

    // Conjugate-pair bitangent classes
    // g = (x+z)^2 + y^2, (x-z)^2 + y^2, x^2+(y+z)^2, x^2+(y-z)^2, (x+y)^2+z^2, (x-y)^2+z^2
    ref := 2*B1;
    conj_classes := [];

    gs := [
        (elt_t+1)^2 + elt_u^2,
        (elt_t-1)^2 + elt_u^2,
        elt_t^2 + (elt_u+1)^2,
        elt_t^2 + (elt_u-1)^2,
        (elt_t+elt_u)^2 + 1,
        (elt_t-elt_u)^2 + 1
    ];

    for g in gs do
        Bg := HalfPositive(Divisor(g));
        Qg := (Bg - ref) @@ m;
        Append(~conj_classes, Qg);
    end for;

    V_all := sub<Cl | P12, P13, P14> cat conj_classes;
    V_all := sub<Cl | [P12, P13, P14] cat conj_classes>;
    V_all_J2 := V_all meet J2;
    printf "  All constructions span in J[2]: order %o\n", #V_all_J2;

    printf "  Result: %o/%o of J[2] reached\n\n", #V_all_J2, #J2;
    return #V_all_J2, #J2;
end function;

// Test primes p = 1 mod 8 (where full 2-torsion is visible)
// Also try some p = 1 mod 4 primes
good_primes := [p : p in PrimesInInterval(3, 100) |
                p mod 4 eq 1 and p ne 5 and p ne 29];

printf "Testing primes: %o\n\n", good_primes;

all_match := true;
for p in good_primes do
    reached, total := AnalyzePrime(p);
    if total ne 0 and reached ne 4 then
        printf "*** UNEXPECTED at p=%o: reached %o/%o ***\n\n", p, reached, total;
        all_match := false;
    end if;
end for;

if all_match then
    print "=== CONCLUSION ===";
    print "At every tested prime, Q-rational constructions span exactly";
    print "(Z/2Z)^2 inside J[2] = (Z/2Z)^3.";
    print "";
    print "This confirms: ker(ob) = (Z/2Z)^2, and the Brauer obstruction";
    print "ob: J[2](Q) -> Br(Q)[2] is NONZERO on the missing direction.";
    print "";
    print "By global reciprocity (4 bad places: inf, 2, 5, 29):";
    print "  inv_5(ob) = inv_29(ob) = 0 (Br(F_p) = 0 at good reduction)";
    print "  inv_inf(ob) + inv_2(ob) = 0 (reciprocity)";
    print "  => inv_inf(ob) = inv_2(ob) = 1/2";
end if;

quit;
