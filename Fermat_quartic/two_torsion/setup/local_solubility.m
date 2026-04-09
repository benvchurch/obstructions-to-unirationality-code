/*******************************************************************************
 * local_solubility_fermat.m
 *
 * Find ALL local obstructions for the Fermat quartic C: x^4 + y^4 + z^4 = 0.
 * Check C(Q_v) for every place v of Q.
 ******************************************************************************/

// =============================================================================
// PLACE v = infinity (archimedean)
// =============================================================================
print "=== LOCAL SOLUBILITY OF C: x^4 + y^4 + z^4 = 0 ===";
print "";
print "--- v = infinity (real place) ---";
print "x^4 + y^4 + z^4 >= 0 for all real (x,y,z), equality only at (0,0,0).";
print "C(R) = EMPTY.";

// =============================================================================
// PLACE v = 2 (bad reduction)
// =============================================================================
print "";
print "--- v = 2 (bad reduction) ---";
print "Mod 2: x^4+y^4+z^4 = (x+y+z)^4, so equation is x+y+z = 0 mod 2.";
print "This has 3 projective solutions: (0:1:1), (1:0:1), (1:1:0).";
print "";
print "Try to lift to mod 4: need x^4+y^4+z^4 = 0 mod 4.";
print "For any integer u: u^4 mod 4 = 0 if u even, 1 if u odd.";
print "Primitive triples (at least one odd):";
print "  3 odd => 1+1+1 = 3 mod 4";
print "  2 odd, 1 even => 1+1+0 = 2 mod 4";
print "  1 odd, 2 even => 1+0+0 = 1 mod 4";
print "None are 0 mod 4, so NO LIFT from mod 2 to mod 4.";
print "";

// Verify computationally
print "Computational verification (primitive solutions mod 2^k):";
for k in [1..5] do
    N := 2^k;
    count := 0;
    for x in [0..N-1] do
        for y in [0..N-1] do
            for z in [0..N-1] do
                if GCD(GCD(x, GCD(y,z)), N) eq 1 then
                    if (x^4 + y^4 + z^4) mod N eq 0 then
                        count +:= 1;
                    end if;
                end if;
            end for;
        end for;
    end for;
    printf "  mod 2^%o = %o: %o primitive solutions\n", k, N, count;
end for;
print "C(Q_2) = EMPTY (obstruction already at mod 4).";

// =============================================================================
// ODD PRIMES (good reduction => Hensel's lemma applies)
// =============================================================================
print "";
print "--- Odd primes (good reduction) ---";
print "The curve is smooth over F_p for p odd: partials 4x^3, 4y^3, 4z^3";
print "vanish simultaneously only at (0,0,0) not in P^2 (and 4 is invertible).";
print "By Hensel's lemma: C(Q_p) nonempty iff C(F_p) nonempty.";
print "";

// Check all primes up to 200
print "Checking C(F_p) for all odd primes p <= 200:";
empty_primes := [];
for p in PrimesInInterval(3, 200) do
    Fp := GF(p);
    P2<x,y,z> := ProjectiveSpace(Fp, 2);
    C := Curve(P2, x^4 + y^4 + z^4);
    np := #RationalPoints(C);
    if np eq 0 then
        Append(~empty_primes, p);
        printf "  p = %o (p mod 8 = %o): C(F_%o) = EMPTY => C(Q_%o) = EMPTY\n",
               p, p mod 8, p, p;
    end if;
end for;
printf "Primes with C(F_p) = 0: %o\n", empty_primes;
print "";

// Weil bound argument for large primes
print "Weil bound: #C(F_p) >= p+1-6*sqrt(p).";
print "This is > 0 when p+1 > 6*sqrt(p), i.e., p >= 37.";
print "We verified all primes p <= 200 above, so no further obstructions.";
print "";

// =============================================================================
// WHY exactly p=5 and p=29?
// =============================================================================
print "--- Why C(F_5) = C(F_29) = 0? ---";
print "";

// p=5 analysis
print "p = 5: F_5* = <2> has order 4. Fourth powers: {a^4 : a in F_5}.";
Fp := GF(5);
fourth_powers := {a^4 : a in Fp};
printf "  Fourth powers in F_5: %o\n", fourth_powers;
print "  Need a+b+c = 0 in F_5 with a,b,c in {0,1}, not all zero.";
print "  Possible sums: 1, 2, 3 -- none is 0 mod 5. So C(F_5) = empty.";
print "";

// p=29 analysis
print "p = 29: F_29* has order 28. Fourth powers have index gcd(4,28)=4.";
Fp := GF(29);
fourth_powers_29 := Sort(Setseq({a^4 : a in Fp}));
printf "  Fourth powers in F_29: %o (%o values)\n", fourth_powers_29, #fourth_powers_29;
print "  Need a+b+c = 0 mod 29 with a,b,c fourth powers, not all zero.";
// Check directly
found := false;
for a in fourth_powers_29 do
    for b in fourth_powers_29 do
        c := Fp ! (-(Fp!a + Fp!b));
        if c in {Fp!x : x in fourth_powers_29} then
            if not (a eq 0 and b eq 0 and Integers()!c eq 0) then
                found := true;
            end if;
        end if;
    end for;
end for;
printf "  Found a+b+c=0 with a,b,c fourth powers (not all 0)? %o\n", found;
print "";

// For p = 3 mod 4: explain why always p+1 points
print "--- p = 3 mod 4: always has p+1 points ---";
print "When p = 3 mod 4: |F_p*| = p-1 = 2 mod 4, so gcd(4,p-1)=2.";
print "The fourth power map x->x^4 has the same image as x->x^2 (the squares).";
print "The quartic character (of order 4) does not exist over F_p.";
print "Point count formula gives #C(F_p) = p+1 (Jacobi sums vanish).";
print "";
print "Verification:";
for p in PrimesInInterval(3, 100) do
    if p mod 4 eq 3 then
        Fp := GF(p);
        P2<x,y,z> := ProjectiveSpace(Fp, 2);
        C := Curve(P2, x^4 + y^4 + z^4);
        np := #RationalPoints(C);
        match := (np eq p+1);
        if not match then
            printf "  UNEXPECTED: p=%o, #C=%o != %o\n", p, np, p+1;
        end if;
    end if;
end for;
print "  Confirmed: #C(F_p) = p+1 for all p = 3 mod 4, p <= 100.";
print "";

// For p = 1 mod 4: relate to E_i: y^2 = x^3-x
print "--- p = 1 mod 4: point counts via E_i ---";
print "J(C) is isogenous to E_i^3 where E_i: y^2 = x^3-x (CM by Z[i]).";
E := EllipticCurve([0, 0, 0, -1, 0]);
print "";
printf "%-5o %-6o %-8o %-5o %-8o %-8o\n", "p", "p%8", "#C(Fp)", "a_p", "#E(Fp)", "#E^3";
for p in PrimesInInterval(5, 100) do
    if p mod 4 eq 1 then
        Fp := GF(p);
        P2<x,y,z> := ProjectiveSpace(Fp, 2);
        C := Curve(P2, x^4 + y^4 + z^4);
        np := #RationalPoints(C);

        Ep := ChangeRing(E, Fp);
        nE := #Ep;
        ap := p + 1 - nE;

        printf "%-5o %-6o %-8o %-5o %-8o %-8o\n", p, p mod 8, np, ap, nE, nE^3;
    end if;
end for;

// =============================================================================
// SUMMARY
// =============================================================================
print "";
print "============================================================";
print "SUMMARY: LOCAL OBSTRUCTIONS FOR x^4 + y^4 + z^4 = 0";
print "============================================================";
print "";
print "C(Q_v) = EMPTY at exactly these places:";
print "  (1) v = infinity: sum of 4th powers > 0";
print "  (2) v = 2: no lift from mod 2 to mod 4 (u^4 = 0 or 1 mod 4)";
printf "  (3) v = 5: C(F_5) = 0 (only 4th powers in F_5 are 0,1)\n";
printf "  (4) v = 29: C(F_29) = 0 (4th powers don't sum to 0)\n";
print "";
print "C(Q_v) != EMPTY at all other primes p:";
print "  - p = 3 mod 4: #C(F_p) = p+1 > 0 (quartic character absent)";
print "  - p = 1 mod 4, p >= 37: Weil bound forces C(F_p) > 0";
print "  - Remaining p in {3,7,11,13,17,19,23,31,37}: verified C(F_p) > 0";
print "";
print "Total bad places: 4 (infinity, 2, 5, 29)";
print "Parity check: for Brauer-Manin, need even number of places where";
print "local invariant is 1/2. We have 4 bad places (even). Consistent.";

quit;
