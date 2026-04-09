/*******************************************************************************
 * picard_local.m
 *
 * For the Fermat quartic C: x^4+y^4+z^4=0, compute Pic(C/F_p) at the
 * primes where C has no local points. If index(C/F_p) = 1 (i.e., Pic^1
 * is nonempty over F_p), then by smoothness of Pic, Pic^1(C/Q_p) is also
 * nonempty, so the local Brauer obstruction vanishes at p.
 ******************************************************************************/

for p in [5, 29] do
    printf "\n========================================\n";
    printf "=== p = %o (good reduction) ===\n", p;
    printf "========================================\n";
    Fp := GF(p);

    // -------------------------------------------------------------------------
    // Point counts over F_{p^n}
    // -------------------------------------------------------------------------
    printf "\nPoint counts #C(F_{p^n}):\n";
    nps := [];
    for n in [1..6] do
        Fpn := GF(p^n);
        P2<x,y,z> := ProjectiveSpace(Fpn, 2);
        C := Curve(P2, x^4 + y^4 + z^4);
        np := #RationalPoints(C);
        Append(~nps, np);
        printf "  n=%o: #C(F_{%o^%o}) = %o\n", n, p, n, np;
    end for;

    // -------------------------------------------------------------------------
    // Closed points by degree
    // -------------------------------------------------------------------------
    printf "\nClosed points by degree (via Mobius inversion):\n";
    degrees_with_points := [];
    for d in [1..6] do
        count := 0;
        for e in Divisors(d) do
            count +:= MoebiusMu(d div e) * nps[e];
        end for;
        Nd := count div d;
        printf "  degree %o: %o closed points\n", d, Nd;
        if Nd gt 0 then
            Append(~degrees_with_points, d);
        end if;
    end for;

    idx := GCD(degrees_with_points);
    printf "\nDegrees present: %o\n", degrees_with_points;
    printf "Index = gcd = %o\n", idx;

    if idx eq 1 then
        printf "\n=> Pic^1(C)(F_%o) is NONEMPTY.\n", p;
        printf "=> By smoothness of Pic (good reduction), lifts to Pic^1(C)(Q_%o).\n", p;
        printf "=> LOCAL BRAUER OBSTRUCTION AT v=%o VANISHES.\n", p;
    else
        printf "\n=> Index > 1: Pic^1(C)(F_%o) = EMPTY.\n", p;
        printf "=> Local Brauer obstruction at v=%o may be nonzero.\n", p;
    end if;

    // -------------------------------------------------------------------------
    // Class group via function field
    // -------------------------------------------------------------------------
    printf "\nClass group (function field method):\n";
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);
    f := u^4 + t^4 + 1;

    if IsIrreducible(f) then
        FF := FunctionField(f);
        Cl, m := ClassGroup(FF);
        invs := Invariants(Cl);
        printf "  Cl(C/F_%o) = ", p;
        for i in [1..#invs] do
            if i gt 1 then printf " x "; end if;
            printf "Z/%oZ", invs[i];
        end for;
        printf "\n";

        // Find degree of generator of the free part (invariant = 0)
        for i in [1..#invs] do
            if invs[i] eq 0 then
                g := Cl.i;
                D := m(g);
                deg_g := Degree(D);
                printf "  Free generator (gen %o) has degree %o\n", i, deg_g;
                printf "  => Image of deg: Pic -> Z contains %oZ\n", Abs(deg_g);

                // Check if smaller degree is achievable via torsion + free
                // The index is the GCD of deg_g and degrees achievable from torsion
                // But torsion classes have degree 0, so index = |deg_g|
                printf "  => Index from class group = %o\n", Abs(deg_g);
            end if;
        end for;
    else
        printf "  f is reducible over F_%o, using factorization...\n", p;
        fac := Factorization(f);
        for pair in fac do
            printf "    factor: degree %o, multiplicity %o\n", Degree(pair[1]), pair[2];
        end for;
    end if;
end for;

// =============================================================================
// p = 2 (bad reduction)
// =============================================================================
printf "\n========================================\n";
printf "=== p = 2 (bad reduction) ===\n";
printf "========================================\n";
printf "\nOver F_2: x^4+y^4+z^4 = (x+y+z)^4. The special fiber is non-reduced.\n";
printf "No smooth model over Z_2, so cannot use reduction for Pic.\n\n";

printf "Global argument for index(C/Q_2):\n";
printf "  C has a degree-2 closed point over Q: the pair of conjugate points\n";
printf "  over Q(sqrt(-3)) where (-2*sqrt(-3) : -sqrt(-3)+3 : sqrt(-3)+3).\n";
printf "  So index(C/Q) | 2. Since C(Q) = empty, index(C/Q) >= 2.\n";
printf "  Hence index(C/Q) = 2.\n\n";

printf "  Over Q_2: sqrt(-3) is in Q_2? Check: -3 mod 8 = 5.\n";
printf "  A 2-adic unit u is a square iff u = 1 mod 8.\n";
printf "  -3 mod 8 = 5 != 1, so sqrt(-3) is NOT in Q_2.\n";
printf "  The degree-2 point remains a degree-2 point over Q_2.\n";
printf "  So index(C/Q_2) | 2.\n";
printf "  Since C(Q_2) = empty, index(C/Q_2) >= 2.\n";
printf "  Hence index(C/Q_2) = 2, and Pic^1(C)(Q_2) = EMPTY.\n";
printf "  => Local Brauer obstruction at v=2 MAY BE NONZERO.\n\n";

// But wait: could there be a degree-1 Q_2-rational divisor class
// not coming from a closed point? No: index = min degree of rational divisor class.
// And we showed index = 2.

// Alternative: check if there's a degree-1 point over an odd-degree
// extension of Q_2. A closed point of odd degree on C/Q_2 would give index = 1.
printf "Check for odd-degree closed points over Q_2:\n";
printf "  Any closed point of C/Q_2 has degree d where C(Q_{2^d}) != empty.\n";
printf "  We need to check if C has points over some odd-degree unramified\n";
printf "  extension of Q_2.\n\n";

// C over F_{2^n}: check if C_smooth has F_{2^n}-points
// Actually C is singular over F_2, but we can look at F_{2^n}-points
// of the equation x^4+y^4+z^4=0
printf "Points on x^4+y^4+z^4=0 over F_{2^n} (even though singular at p=2):\n";
for n in [1..8] do
    Fpn := GF(2^n);
    P2<x,y,z> := ProjectiveSpace(Fpn, 2);
    C := Curve(P2, x^4 + y^4 + z^4);
    np := #RationalPoints(C);
    printf "  #C(F_{2^%o}) = %o\n", n, np;
end for;
printf "\n";
printf "Over F_2: C is (x+y+z)^4 = 0, a 4-fold line. All points on x+y+z=0 work.\n";
printf "The 'points' here are on the singular model and don't lift to smooth Q_2-points.\n";
printf "For the smooth C/Q_2: no point can reduce to the singular special fiber.\n";
printf "(More precisely: C(Q_2) injects into smooth locus of special fiber, which is empty.)\n";

// =============================================================================
// v = infinity
// =============================================================================
printf "\n========================================\n";
printf "=== v = infinity (archimedean) ===\n";
printf "========================================\n";
printf "\nC(R) = empty.\n";
printf "The degree-2 point from Q(sqrt(-3)): since sqrt(-3) not in R,\n";
printf "the conjugate pair gives a degree-2 effective divisor over R.\n";
printf "So index(C/R) | 2. Since C(R) = empty, index(C/R) = 2.\n";
printf "=> Pic^1(C)(R) = EMPTY. Local Brauer obstruction at infinity MAY BE NONZERO.\n";

// =============================================================================
// SUMMARY
// =============================================================================
printf "\n========================================\n";
printf "=== SUMMARY ===\n";
printf "========================================\n";
printf "\nLocal Brauer obstruction analysis for C: x^4+y^4+z^4=0:\n\n";
printf "  v=infinity: index(C/R) = 2.   Obstruction POSSIBLY NONZERO.\n";
printf "  v=2:        index(C/Q_2) = 2. Obstruction POSSIBLY NONZERO.\n";
printf "  v=5:        index(C/F_5) = ?  (computed above)\n";
printf "  v=29:       index(C/F_29) = ? (computed above)\n";
printf "  all other:  C(Q_p) nonempty.  Obstruction = 0.\n\n";
printf "If index = 1 at v=5,29 then obstruction vanishes there, leaving\n";
printf "only v=infinity and v=2 as candidates for nonzero local obstruction.\n";

quit;
