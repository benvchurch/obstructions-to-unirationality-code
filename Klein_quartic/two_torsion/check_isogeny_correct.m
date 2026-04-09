/*******************************************************************************
 * check_isogeny_correct.m - Correct isogeny test using CM field criterion
 *
 * Two ordinary elliptic curves over F_p are isogenous over F_p^bar iff they
 * have the same CM field, i.e., squarefree_part(a_p^2 - 4p) is the same.
 * An isogeny over Qbar reduces to an isogeny over F_p^bar, so if the CM
 * fields differ at any prime, the curves are NOT isogenous over Qbar.
 ******************************************************************************/

PQ<v> := PolynomialRing(Rationals());
mp1_Q := v^2 + 13856*v - 26578688;
mp23_Q := v^4 - 103439*v^3 + 6670405329*v^2 + 31128229267744*v + 148381159092130048;

K<w> := QuadraticField(-7);
PK<u> := PolynomialRing(K);
fac_K := Factorization(PK!mp23_Q);
mp2 := fac_K[1][1];
mp3 := fac_K[2][1];

function SquarefreePart(n)
    if n eq 0 then return 0; end if;
    sign := n gt 0 select 1 else -1;
    n := Abs(n);
    fac := Factorization(n);
    sfp := 1;
    for f in fac do
        if f[2] mod 2 eq 1 then sfp *:= f[1]; end if;
    end for;
    return sign * sfp;
end function;

function TraceFromJ(j_val, Fq)
    if j_val eq Fq!1728 then
        E := EllipticCurve([Fq| 1, 0]);
    elif j_val eq 0 then
        E := EllipticCurve([Fq| 0, 1]);
    else
        denom := j_val - Fq!1728;
        if denom eq 0 then return false, 0; end if;
        c := 27*j_val / denom;
        disc := -4*(-c)^3 - 27*(-2*c)^2;
        if disc eq 0 then return false, 0; end if;
        E := EllipticCurve([Fq| -c, -2*c]);
    end if;
    return true, TraceOfFrobenius(E);
end function;

// ============================================================
// Test 1: j1 (28-orbit) vs j23 (7+7-orbit)
// ============================================================
print "=== j1 (28-orbit) vs j23 (7+7-orbit): CM field test ===";
print "  p | a_p(j1) | a_p(j23) | disc1=a^2-4p | disc2=a^2-4p | sfp1 | sfp2 | same?";

for p in PrimesInInterval(5, 500) do
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);

    f1 := PFp![Fp!c : c in Coefficients(mp1_Q)];
    f23 := PFp![Fp!c : c in Coefficients(mp23_Q)];

    fac1 := Factorization(f1);
    fac23 := Factorization(f23);
    if not &and[Degree(ff[1]) eq 1 : ff in fac1] then continue; end if;
    if not &and[Degree(ff[1]) eq 1 : ff in fac23] then continue; end if;

    j1p := -Coefficient(fac1[1][1], 0);
    j23p := -Coefficient(fac23[1][1], 0);

    ok1, a1 := TraceFromJ(j1p, Fp);
    ok2, a2 := TraceFromJ(j23p, Fp);
    if not ok1 or not ok2 then continue; end if;

    d1 := Integers()!(a1^2 - 4*p);
    d2 := Integers()!(a2^2 - 4*p);

    // Skip supersingular (disc = 0)
    if d1 eq 0 or d2 eq 0 then continue; end if;

    sfp1 := SquarefreePart(d1);
    sfp2 := SquarefreePart(d2);
    same := sfp1 eq sfp2;

    printf "%4o | %6o | %8o | %10o | %10o | %6o | %6o | %o\n",
        p, a1, a2, d1, d2, sfp1, sfp2, same;

    if not same then
        printf "  => PROVEN not isogenous over Qbar at p=%o\n", p;
        printf "     CM fields: Q(sqrt(%o)) vs Q(sqrt(%o))\n", sfp1, sfp2;
        break;
    end if;
end for;

// ============================================================
// Test 2: mp2 roots vs mp3 roots (within j23)
// ============================================================
print "\n=== mp2 vs mp3 (within 7+7-orbit): CM field test ===";

for p in PrimesInInterval(5, 500) do
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);

    f23 := PFp![Fp!c : c in Coefficients(mp23_Q)];
    fac_p := Factorization(f23);
    if not &and[Degree(ff[1]) eq 1 : ff in fac_p] then continue; end if;

    is_sq, sq7 := IsSquare(Fp!(-7));
    if not is_sq then continue; end if;

    // Reduce mp2 coefficients
    mp2_coeffs := [];
    for i in [0..2] do
        ci := Coefficient(mp2, i);
        cs := Eltseq(K!ci);
        Append(~mp2_coeffs, Fp!(cs[1]) + sq7*Fp!(cs[2]));
    end for;
    f2 := PFp!mp2_coeffs;
    fac2 := Factorization(f2);
    if not &and[Degree(ff[1]) eq 1 : ff in fac2] then continue; end if;

    all_roots := [-Coefficient(ff[1], 0) : ff in fac_p];
    mp2_roots := {-Coefficient(ff[1], 0) : ff in fac2};
    mp3_roots := {r : r in all_roots | r notin mp2_roots};

    if #mp3_roots eq 0 then
        // Try other sign of sqrt(-7)
        mp2_coeffs2 := [];
        for i in [0..2] do
            ci := Coefficient(mp2, i);
            cs := Eltseq(K!ci);
            Append(~mp2_coeffs2, Fp!(cs[1]) - sq7*Fp!(cs[2]));
        end for;
        f2b := PFp!mp2_coeffs2;
        fac2b := Factorization(f2b);
        if not &and[Degree(ff[1]) eq 1 : ff in fac2b] then continue; end if;
        mp2_roots := {-Coefficient(ff[1], 0) : ff in fac2};
        mp3_roots := {-Coefficient(ff[1], 0) : ff in fac2b};
    end if;
    if #mp2_roots lt 2 or #mp3_roots lt 2 then continue; end if;

    // Get one trace from each
    r2 := Representative(mp2_roots);
    r3 := Representative(mp3_roots);
    ok2, a2 := TraceFromJ(r2, Fp);
    ok3, a3 := TraceFromJ(r3, Fp);
    if not ok2 or not ok3 then continue; end if;

    d2 := Integers()!(a2^2 - 4*p);
    d3 := Integers()!(a3^2 - 4*p);
    if d2 eq 0 or d3 eq 0 then continue; end if;

    sfp2 := SquarefreePart(d2);
    sfp3 := SquarefreePart(d3);
    same := sfp2 eq sfp3;

    printf "%4o | a_p(mp2)=%4o, a_p(mp3)=%4o | disc %o vs %o | sfp %o vs %o | %o\n",
        p, a2, a3, d2, d3, sfp2, sfp3, same;

    if not same then
        printf "  => PROVEN not isogenous over Qbar at p=%o\n", p;
        printf "     CM fields: Q(sqrt(%o)) vs Q(sqrt(%o))\n", sfp2, sfp3;
        break;
    end if;
end for;

// ============================================================
// Also: what if all our "NO OVERLAP" primes actually had same CM field?
// Let's check ALL split primes systematically for j1 vs j23
// ============================================================
print "\n=== Full CM field comparison j1 vs j23 ===";
proofs := 0;
for p in PrimesInInterval(5, 500) do
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);
    f1 := PFp![Fp!c : c in Coefficients(mp1_Q)];
    f23 := PFp![Fp!c : c in Coefficients(mp23_Q)];
    fac1 := Factorization(f1);
    fac23 := Factorization(f23);
    if not &and[Degree(ff[1]) eq 1 : ff in fac1] then continue; end if;
    if not &and[Degree(ff[1]) eq 1 : ff in fac23] then continue; end if;

    // Get all traces from both
    j1_roots := [-Coefficient(ff[1], 0) : ff in fac1];
    j23_roots := [-Coefficient(ff[1], 0) : ff in fac23];

    j1_discs := {};
    j23_discs := {};
    all_ok := true;
    for r in j1_roots do
        ok, a := TraceFromJ(r, Fp);
        if not ok then all_ok := false; break; end if;
        d := Integers()!(a^2 - 4*p);
        if d ne 0 then Include(~j1_discs, SquarefreePart(d)); end if;
    end for;
    if not all_ok then continue; end if;
    for r in j23_roots do
        ok, a := TraceFromJ(r, Fp);
        if not ok then all_ok := false; break; end if;
        d := Integers()!(a^2 - 4*p);
        if d ne 0 then Include(~j23_discs, SquarefreePart(d)); end if;
    end for;
    if not all_ok then continue; end if;

    overlap := j1_discs meet j23_discs;
    if #overlap eq 0 and #j1_discs gt 0 and #j23_discs gt 0 then
        printf "p=%o: j1 CM fields %o, j23 CM fields %o => NO OVERLAP\n",
            p, j1_discs, j23_discs;
        proofs +:= 1;
    end if;
end for;
printf "Proven non-isogenous at %o primes\n", proofs;
