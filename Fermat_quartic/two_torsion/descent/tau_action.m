/*******************************************************************************
 * tau_action.m
 *
 * Compute the tau action (twist cocycle) on J[2] for C2: x^4+y^4-z^4=0.
 * tau: (x:y:z) -> (x:y:iz), in affine (t,u) -> (t/i, u/i).
 *
 * Merged from: test_involution_J2.m, test_tau_J2.m, tau_full_J2.m,
 *              tau_via_automorphisms.m, tau_matrix.m, tau_matrix_final.m
 *
 * Contents:
 *   1. Helper functions (J2Subgroup, TauPullback, TauOnJ2, ComputeTauMatrix)
 *   2. Involution triviality test: (t,u)->(-t,-u) acts trivially on J[2]
 *   3. Tau matrix computation & fixed subspace analysis (multi-prime)
 ******************************************************************************/


// =========== HELPER FUNCTIONS ===========

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

// Compute tau*(f) for f in FF2, where tau: (t,u) -> (t/i, u/i)
function TauPullback(f, FF, gen_u, base_t, inv_i)
    elt := ElementToSequence(f);
    result := FF!0;
    for j in [1..#elt] do
        num := Numerator(elt[j]);
        den := Denominator(elt[j]);
        num_sub := Evaluate(num, base_t * inv_i);
        den_sub := Evaluate(den, base_t * inv_i);
        a_sub := num_sub / den_sub;
        result := result + (FF!a_sub) * gen_u^(j-1) * (FF!inv_i)^(j-1);
    end for;
    return result;
end function;

// Compute tau*(g) for g in J[2], using Riemann-Roch to find the representing
// function, then half-divisor of the pullback
function TauOnJ2(g, mm, FF, gen_u, base_t, inv_i, Cl)
    D := mm(g);
    neg2D := -2*D;
    V, phi_V := RiemannRochSpace(neg2D);
    f_g := phi_V(V.1);
    tau_fg := TauPullback(f_g, FF, gen_u, base_t, inv_i);
    div_tau := Divisor(tau_fg);
    supp_tau := Support(div_tau);
    half_div := DivisorGroup(FF) ! 0;
    for P in supp_tau do
        val := Valuation(div_tau, P);
        assert val mod 2 eq 0;
        half_div := half_div + (val div 2) * (1*P);
    end for;
    return half_div @@ mm;
end function;

// Compute the full F_2 matrix of tau on J[2] at a given prime p
function ComputeTauMatrix(p)
    Fp := GF(p);
    ii := Fp!0;
    for x in Fp do
        if x ne 0 and x^2 eq Fp!(-1) then ii := x; break; end if;
    end for;
    inv_i := Fp!(1/ii);

    Fpt<tt> := FunctionField(Fp);
    Fptu<uu> := PolynomialRing(Fpt);
    FF2<vv> := FunctionField(uu^4 + tt^4 - 1);
    Cl2, mm2 := ClassGroup(FF2);
    invs2 := Invariants(Cl2);
    J2_sub := J2Subgroup(Cl2, invs2);
    printf "p=%o: Cl=%o, |J[2]|=%o\n", p, invs2, #J2_sub;

    j2_gens := [];
    for k in [1..#invs2] do
        if invs2[k] eq 0 then continue; end if;
        if invs2[k] mod 2 ne 0 then continue; end if;
        Append(~j2_gens, (invs2[k] div 2) * Cl2.k);
    end for;
    n := #j2_gens;

    // Compute tau images
    tau_images := [];
    for idx in [1..n] do
        g := j2_gens[idx];
        tau_g := TauOnJ2(g, mm2, FF2, vv, tt, inv_i, Cl2);
        Append(~tau_images, tau_g);
    end for;

    // Express as F_2 matrix
    V2 := VectorSpace(GF(2), n);
    T := ZeroMatrix(GF(2), n, n);
    for idx in [1..n] do
        h := tau_images[idx];
        for bits in [0..2^n-1] do
            sum := Cl2!0;
            for i in [1..n] do
                if (bits div 2^(i-1)) mod 2 eq 1 then
                    sum := sum + j2_gens[i];
                end if;
            end for;
            if sum eq h then
                for j in [1..n] do
                    T[idx][j] := GF(2)!((bits div 2^(j-1)) mod 2);
                end for;
                break;
            end if;
        end for;
    end for;

    return T, n;
end function;


// =========== INVOLUTION TRIVIALITY TEST ===========
// Test: does (t,u) -> (-t,-u) [i.e., (x:y:z)->(x:y:-z)] act trivially on J[2]?
// Since tau^2 = this involution, triviality of tau^2 on J[2] is essential.

print "========================================";
print "SECTION 1: Involution (z -> -z) on J[2]";
print "========================================";

for p in [3, 5, 7, 11, 13, 17, 19] do
    printf "=== p = %o (p mod 8 = %o) ===\n", p, p mod 8;
    Fp := GF(p);
    Fpt<tt> := FunctionField(Fp);
    Fptu<uu> := PolynomialRing(Fpt);

    f2 := uu^4 + tt^4 - 1;
    if not IsIrreducible(f2) then
        printf "  f2 reducible over F_%o, skipping\n\n", p;
        continue;
    end if;

    FF2<vv> := FunctionField(f2);
    Cl2, mm2 := ClassGroup(FF2);
    invs2 := Invariants(Cl2);
    J2_2 := J2Subgroup(Cl2, invs2);
    printf "  Cl = %o, |J[2]| = %o\n", invs2, #J2_2;

    // Enumerate affine degree-1 places
    pls2 := Places(FF2, 1);
    aff2 := [];
    coord_lookup := AssociativeArray();
    for P in pls2 do
        if Valuation(FF2!tt, P) lt 0 or Valuation(vv, P) lt 0 then continue; end if;
        tv := Fp!Evaluate(FF2!tt, P);
        uv := Fp!Evaluate(vv, P);
        Append(~aff2, P);
        coord_lookup[Sprint(<tv, uv>)] := P;
    end for;
    printf "  Affine deg-1 places: %o\n", #aff2;

    // Build involution map: (t,u) -> (-t,-u)
    inv_map := AssociativeArray();
    for P in aff2 do
        tv := Fp!Evaluate(FF2!tt, P);
        uv := Fp!Evaluate(vv, P);
        key := Sprint(<-tv, -uv>);
        if IsDefined(coord_lookup, key) then
            inv_map[P] := coord_lookup[key];
        end if;
    end for;
    printf "  Involution maps %o/%o affine places\n", #Keys(inv_map), #aff2;

    // Test involution on each J[2] element
    inv_trivial := true;
    tested := 0;
    failed := 0;
    for g in J2_2 do
        if g eq Cl2!0 then continue; end if;
        D := mm2(g);
        supp := Support(D);
        invD := DivisorGroup(FF2) ! 0;
        ok := true;
        for P in supp do
            n := Valuation(D, P);
            if Degree(P) ne 1 then
                ok := false; break;
            end if;
            if not IsDefined(inv_map, P) then
                ok := false; break;
            end if;
            invD := invD + n * (1*inv_map[P]);
        end for;

        if ok then
            inv_g := invD @@ mm2;
            tested +:= 1;
            if inv_g ne g then
                printf "  NONTRIVIAL: %o -> %o\n", g, inv_g;
                inv_trivial := false;
            end if;
        else
            failed +:= 1;
        end if;
    end for;

    printf "  Tested: %o, Failed: %o (non-deg-1 in divisor)\n", tested, failed;
    if tested eq 0 then
        printf "  Could not test any elements (all have non-deg-1 places)\n";
    elif inv_trivial then
        printf "  z->-z acts TRIVIALLY on all tested J[2] elements\n";
    else
        printf "  z->-z acts NONTRIVIALLY on J[2]\n";
    end if;
    printf "\n";
end for;


// =========== TAU MATRIX & FIXED SUBSPACE ===========
// Core computation: tau matrix on J[2] at multiple primes, verify order,
// compute fixed subspace. Uses Riemann-Roch function pullback approach.

print "==============================================";
print "SECTION 2: Tau matrix on J[2] (multi-prime)";
print "==============================================";

// Main computation at p=17 (p = 1 mod 8, full J[2] visible)
print "=== p = 17 (full J[2] = (Z/2Z)^6 visible) ===";
T17, n17 := ComputeTauMatrix(17);
I17 := IdentityMatrix(GF(2), n17);

printf "T =\n%o\n\n", T17;
printf "Order checks:\n";
printf "  T^1 = I? %o\n", T17 eq I17;
printf "  T^2 = I? %o\n", T17^2 eq I17;
printf "  T^3 = I? %o\n", T17^3 eq I17;
printf "  T^4 = I? %o\n", T17^4 eq I17;

ord := Order(T17);
printf "  Order of T: %o\n\n", ord;

K17 := NullSpace(T17 + I17);
printf "ker(T+I) = tau-fixed subspace: dim = %o\n", Dimension(K17);
printf "Basis: %o\n", Basis(K17);

// Also compute ker(T^2 + I) in case we need it
K17_2 := NullSpace(T17^2 + I17);
printf "ker(T^2+I) = tau^2-fixed subspace: dim = %o\n\n", Dimension(K17_2);

// Verification at p=41 (also = 1 mod 8)
print "=== p = 41 (verification, also full J[2]) ===";
T41, n41 := ComputeTauMatrix(41);
I41 := IdentityMatrix(GF(2), n41);
printf "T =\n%o\n\n", T41;
printf "Order of T: %o\n", Order(T41);
K41 := NullSpace(T41 + I41);
printf "tau-fixed subspace: dim = %o\n", Dimension(K41);
K41_2 := NullSpace(T41^2 + I41);
printf "tau^2-fixed subspace: dim = %o\n\n", Dimension(K41_2);

// Also check at p=5 (J[2] = (Z/2Z)^4, partial view)
print "=== p = 5 (partial J[2] = (Z/2Z)^4) ===";
T5, n5 := ComputeTauMatrix(5);
I5 := IdentityMatrix(GF(2), n5);
printf "T =\n%o\n\n", T5;
printf "Order of T: %o\n", Order(T5);
K5 := NullSpace(T5 + I5);
printf "tau-fixed subspace: dim = %o\n\n", Dimension(K5);


// =========== CONCLUSION ===========

print "=== SUMMARY ===";
printf "At p=17 (full J[2]=(Z/2Z)^6): tau has order %o, fixed dim = %o\n",
    Order(T17), Dimension(K17);
printf "At p=41 (full J[2]=(Z/2Z)^6): tau has order %o, fixed dim = %o\n",
    Order(T41), Dimension(K41);
printf "At p=5 (partial J[2]=(Z/2Z)^4): tau has order %o, fixed dim = %o\n\n",
    Order(T5), Dimension(K5);

fd := Dimension(K17);
print "=== FINAL CONCLUSION ===";
printf "tau = (x:y:z)->(x:y:iz) acts on J[2](Qbar) = (Z/2Z)^6 with:\n";
printf "  - order %o\n", Order(T17);
printf "  - fixed subspace of dimension %o\n\n", fd;
printf "The twist cocycle c: G_Q -> Aut(C2) takes values in <tau>.\n";
printf "For phi_*(J[2](Q)_{C1}) = J[2](Q)_{C2}, we need tau to fix\n";
printf "the 3-dimensional subspace phi_*(J[2](Q)_{C1}).\n\n";
if fd lt 3 then
    printf "Since dim(tau-fixed) = %o < 3 = dim(J[2](Q)), this is IMPOSSIBLE.\n\n", fd;
    printf "*** CONCLUSION: The J[2](Q) subspaces for C1 and C2 are NOT ***\n";
    printf "*** the same under the isomorphism phi: C1 -> C2.             ***\n";
else
    printf "dim(tau-fixed) = %o >= 3, so further analysis needed.\n", fd;
end if;

quit;
