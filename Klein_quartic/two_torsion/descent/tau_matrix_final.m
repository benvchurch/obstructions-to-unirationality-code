/*******************************************************************************
 * tau_matrix_final.m
 *
 * Final computation: τ matrix on J[2], verify order, compute fixed subspace.
 * Verify at two independent primes for confidence.
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

    // Compute τ images
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

// =========================================================================
// Main computation at p=17 (p ≡ 1 mod 8, full J[2] visible)
// =========================================================================
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
printf "ker(T+I) = τ-fixed subspace: dim = %o\n", Dimension(K17);
printf "Basis: %o\n", Basis(K17);

// Also compute ker(T^2 + I) in case we need it
K17_2 := NullSpace(T17^2 + I17);
printf "ker(T^2+I) = τ²-fixed subspace: dim = %o\n\n", Dimension(K17_2);

// =========================================================================
// Verification at p=41 (also ≡ 1 mod 8)
// =========================================================================
print "=== p = 41 (verification, also full J[2]) ===";
T41, n41 := ComputeTauMatrix(41);
I41 := IdentityMatrix(GF(2), n41);
printf "T =\n%o\n\n", T41;
printf "Order of T: %o\n", Order(T41);
K41 := NullSpace(T41 + I41);
printf "τ-fixed subspace: dim = %o\n", Dimension(K41);
K41_2 := NullSpace(T41^2 + I41);
printf "τ²-fixed subspace: dim = %o\n\n", Dimension(K41_2);

// =========================================================================
// Also check at p=5 (J[2] = (Z/2Z)^4, partial view)
// =========================================================================
print "=== p = 5 (partial J[2] = (Z/2Z)^4) ===";
T5, n5 := ComputeTauMatrix(5);
I5 := IdentityMatrix(GF(2), n5);
printf "T =\n%o\n\n", T5;
printf "Order of T: %o\n", Order(T5);
K5 := NullSpace(T5 + I5);
printf "τ-fixed subspace: dim = %o\n\n", Dimension(K5);

// =========================================================================
// CONCLUSION
// =========================================================================
print "=== SUMMARY ===";
printf "At p=17 (full J[2]=(Z/2Z)^6): τ has order %o, fixed dim = %o\n",
    Order(T17), Dimension(K17);
printf "At p=41 (full J[2]=(Z/2Z)^6): τ has order %o, fixed dim = %o\n",
    Order(T41), Dimension(K41);
printf "At p=5 (partial J[2]=(Z/2Z)^4): τ has order %o, fixed dim = %o\n\n",
    Order(T5), Dimension(K5);

fd := Dimension(K17);
print "=== FINAL CONCLUSION ===";
printf "τ = (x:y:z)->(x:y:iz) acts on J[2](Q̄) = (Z/2Z)^6 with:\n";
printf "  - order %o\n", Order(T17);
printf "  - fixed subspace of dimension %o\n\n", fd;
printf "The twist cocycle c: G_Q -> Aut(C2) takes values in <τ>.\n";
printf "For φ_*(J[2](Q)_{C1}) = J[2](Q)_{C2}, we need τ to fix\n";
printf "the 3-dimensional subspace φ_*(J[2](Q)_{C1}).\n\n";
if fd lt 3 then
    printf "Since dim(τ-fixed) = %o < 3 = dim(J[2](Q)), this is IMPOSSIBLE.\n\n", fd;
    printf "*** CONCLUSION: The J[2](Q) subspaces for C1 and C2 are NOT ***\n";
    printf "*** the same under the isomorphism φ: C1 -> C2.             ***\n";
else
    printf "dim(τ-fixed) = %o >= 3, so further analysis needed.\n", fd;
end if;

quit;
