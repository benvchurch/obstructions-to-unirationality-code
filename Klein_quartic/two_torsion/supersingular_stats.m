/*******************************************************************************
 * supersingular_stats.m - Count supersingular primes by characteristic
 *
 * For each rational prime p, check if E has supersingular reduction at
 * any prime above p in the field of definition of j.
 *
 * j1 in Q(sqrt(7)):  mp1 = v^2 + 13856v - 26578688
 * j23 in 4.0.1372.1: mp23 = v^4 - 103439v^3 + ...
 *   which splits over Q(sqrt(-7)) as mp2 * mp3
 *
 * Lang-Trotter predicts ~C*sqrt(x)/log(x) supersingular primes up to x
 * for non-CM curves. CM curves have density 1/2.
 ******************************************************************************/

PQ<v> := PolynomialRing(Rationals());
mp1_Q := v^2 + 13856*v - 26578688;
mp23_Q := v^4 - 103439*v^3 + 6670405329*v^2 + 31128229267744*v + 148381159092130048;

K1<j1> := NumberField(mp1_Q);
K23<j23> := NumberField(mp23_Q);
O1 := Integers(K1);
O23 := Integers(K23);

// Build elliptic curves over the number fields
// E: y^2 = x^3 - 27j/(j-1728) x - 54j/(j-1728)
c1 := 27*j1/(j1 - 1728);
E1 := EllipticCurve([K1| -c1, -2*c1]);
E1 := MinimalModel(E1);

c23 := 27*j23/(j23 - 1728);
E23 := EllipticCurve([K23| -c23, -2*c23]);
E23 := MinimalModel(E23);

printf "E1 over Q(sqrt(7)): %o\n", aInvariants(E1);
printf "Conductor E1: %o\n", Factorization(Norm(Conductor(E1)));
printf "E23 over 4.0.1372.1: %o\n", aInvariants(E23);
printf "Conductor E23: %o\n", Factorization(Norm(Conductor(E23)));

// For each rational prime p, find primes above p and compute traces
BOUND := 100000;

// Count supersingular primes (a_P = 0 for some prime P above p)
// Also count: ss_all (a_P = 0 for ALL primes above p)
ss1_any := 0;  // p where some prime above p in K1 gives a_P = 0
ss23_any := 0;
ss1_all := 0;
ss23_all := 0;

total_primes := 0;

// Track counts at various thresholds for growth rate analysis
thresholds := [100, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000];
thresh_idx := 1;

printf "\n%10o %8o %8o %8o %8o %10o %10o %10o %10o\n",
    "x", "ss1_any", "ss23any", "ss1_all", "ss23all",
    "sqrt(x)/ln(x)", "ss1/predict", "ss23/predict", "primes";

for p in PrimesUpTo(BOUND) do
    if p le 3 then continue; end if;
    total_primes +:= 1;

    // E1 over K1 = Q(sqrt(7))
    // Check if p is a prime of good reduction first
    bad1 := false;
    primes1 := Decomposition(O1, p);
    any_ss1 := false;
    all_ss1 := true;
    for pp in primes1 do
        P := pp[1];
        f := pp[2];  // ramification index... actually Decomposition returns <prime, e, f>
        // Wait, in Magma Decomposition returns sequence of <prime ideal, ramification index>
        // and the residue degree is Degree(P) / ... hmm
        // Let me use a different approach
    end for;

    // Simpler: just reduce the minimal polynomial mod p and compute traces
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);

    // For j1: factor mp1 mod p
    f1p := PFp![Fp!c : c in Coefficients(mp1_Q)];
    if Degree(f1p) lt 2 then continue; end if;  // bad prime
    fac1 := Factorization(f1p);

    any_ss1 := false;
    all_ss1 := true;
    for fac in fac1 do
        d := Degree(fac[1]);
        if d eq 1 then
            // Prime of degree 1 above p
            jp := -Coefficient(fac[1], 0);
            if jp eq Fp!1728 then
                Ep := EllipticCurve([Fp| 1, 0]);
            elif jp eq 0 then
                Ep := EllipticCurve([Fp| 0, 1]);
            else
                denom := jp - Fp!1728;
                if denom eq 0 then all_ss1 := false; continue; end if;
                cc := 27*jp/denom;
                disc := -4*(-cc)^3 - 27*(-2*cc)^2;
                if disc eq 0 then all_ss1 := false; continue; end if;
                Ep := EllipticCurve([Fp| -cc, -2*cc]);
            end if;
            ap := TraceOfFrobenius(Ep);
            if ap eq 0 then any_ss1 := true; else all_ss1 := false; end if;
        else
            // Prime of degree d above p, work over F_{p^d}
            Fq := GF(p^d);
            rts := Roots(ChangeRing(fac[1], Fq));
            if #rts eq 0 then all_ss1 := false; continue; end if;
            jp := rts[1][1];
            if jp eq Fq!1728 then
                Ep := EllipticCurve([Fq| 1, 0]);
            elif jp eq 0 then
                Ep := EllipticCurve([Fq| 0, 1]);
            else
                denom := jp - Fq!1728;
                if denom eq 0 then all_ss1 := false; continue; end if;
                cc := 27*jp/denom;
                disc := -4*(-cc)^3 - 27*(-2*cc)^2;
                if disc eq 0 then all_ss1 := false; continue; end if;
                Ep := EllipticCurve([Fq| -cc, -2*cc]);
            end if;
            ap := TraceOfFrobenius(Ep);
            if ap eq 0 then any_ss1 := true; else all_ss1 := false; end if;
        end if;
    end for;
    if any_ss1 then ss1_any +:= 1; end if;
    if all_ss1 then ss1_all +:= 1; end if;

    // For j23: factor mp23 mod p
    f23p := PFp![Fp!c : c in Coefficients(mp23_Q)];
    if Degree(f23p) lt 4 then continue; end if;
    fac23 := Factorization(f23p);

    any_ss23 := false;
    all_ss23 := true;
    for fac in fac23 do
        d := Degree(fac[1]);
        if d eq 1 then
            jp := -Coefficient(fac[1], 0);
            if jp eq Fp!1728 then
                Ep := EllipticCurve([Fp| 1, 0]);
            elif jp eq 0 then
                Ep := EllipticCurve([Fp| 0, 1]);
            else
                denom := jp - Fp!1728;
                if denom eq 0 then all_ss23 := false; continue; end if;
                cc := 27*jp/denom;
                disc := -4*(-cc)^3 - 27*(-2*cc)^2;
                if disc eq 0 then all_ss23 := false; continue; end if;
                Ep := EllipticCurve([Fp| -cc, -2*cc]);
            end if;
            ap := TraceOfFrobenius(Ep);
            if ap eq 0 then any_ss23 := true; else all_ss23 := false; end if;
        else
            Fq := GF(p^d);
            rts := Roots(ChangeRing(fac[1], Fq));
            if #rts eq 0 then all_ss23 := false; continue; end if;
            jp := rts[1][1];
            if jp eq Fq!1728 then
                Ep := EllipticCurve([Fq| 1, 0]);
            elif jp eq 0 then
                Ep := EllipticCurve([Fq| 0, 1]);
            else
                denom := jp - Fq!1728;
                if denom eq 0 then all_ss23 := false; continue; end if;
                cc := 27*jp/denom;
                disc := -4*(-cc)^3 - 27*(-2*cc)^2;
                if disc eq 0 then all_ss23 := false; continue; end if;
                Ep := EllipticCurve([Fq| -cc, -2*cc]);
            end if;
            ap := TraceOfFrobenius(Ep);
            if ap eq 0 then any_ss23 := true; else all_ss23 := false; end if;
        end if;
    end for;
    if any_ss23 then ss23_any +:= 1; end if;
    if all_ss23 then ss23_all +:= 1; end if;

    // Print at thresholds
    if thresh_idx le #thresholds and p ge thresholds[thresh_idx] then
        x := RealField(6)!p;
        lt_predict := Sqrt(x)/Log(x);
        r1 := ss1_any gt 0 select RealField(4)!(ss1_any/lt_predict) else RealField(4)!0;
        r23 := ss23_any gt 0 select RealField(4)!(ss23_any/lt_predict) else RealField(4)!0;
        printf "%10o %8o %8o %8o %8o %10o %10o %10o %10o\n",
            p, ss1_any, ss23_any, ss1_all, ss23_all,
            RealField(6)!lt_predict, r1, r23, total_primes;
        thresh_idx +:= 1;
    end if;
end for;

// Final summary
print "\n=== Final counts ===";
printf "Primes up to %o: %o\n", BOUND, total_primes;
printf "j1  (28-orbit): ss_any = %o, ss_all = %o\n", ss1_any, ss1_all;
printf "j23 (7+7-orbit): ss_any = %o, ss_all = %o\n", ss23_any, ss23_all;

x := RealField(8)!BOUND;
lt := Sqrt(x)/Log(x);
printf "\nsqrt(x)/log(x) at x=%o: %o\n", BOUND, lt;
printf "j1  ratio ss_any / (sqrt(x)/log(x)) = %o\n", RealField(6)!(ss1_any/lt);
printf "j23 ratio ss_any / (sqrt(x)/log(x)) = %o\n", RealField(6)!(ss23_any/lt);
printf "j1  ratio ss_all / (sqrt(x)/log(x)) = %o\n", RealField(6)!(ss1_all/lt);
printf "j23 ratio ss_all / (sqrt(x)/log(x)) = %o\n", RealField(6)!(ss23_all/lt);

// Also print sqrt(x) / log(x) ratios
printf "\n=== Growth rate analysis ===\n";
printf "If Lang-Trotter: ss(x) ~ C * sqrt(x)/log(x), ratio should stabilize\n";
printf "If CM-like: ss(x) ~ C * x/log(x), ratio with sqrt(x)/log(x) grows as sqrt(x)\n";
