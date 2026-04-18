/*******************************************************************************
 * supersingular_stats2.m - Supersingular prime statistics to 10^6
 * Optimized: skip degree>2 extensions, only track ss_any and ss_all
 ******************************************************************************/

PQ<v> := PolynomialRing(Rationals());
mp1_Q := v^2 + 13856*v - 26578688;
mp23_Q := v^4 - 103439*v^3 + 6670405329*v^2 + 31128229267744*v + 148381159092130048;

mp1_coeffs := Coefficients(mp1_Q);
mp23_coeffs := Coefficients(mp23_Q);

BOUND := 1000000;

ss1_any := 0;
ss1_all := 0;
ss23_any := 0;
ss23_all := 0;
total := 0;

// Track at thresholds
thresholds := [1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000, 500000, 1000000];
thresh_idx := 1;

print "         x  ss1_any ss23_any  ss1_all ss23_all  sqrt/log     C1     C23    primes";

for p in PrimesUpTo(BOUND) do
    if p le 3 then continue; end if;
    total +:= 1;

    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);

    // === j1 over Q(sqrt(7)) ===
    f1 := PFp![Fp!c : c in mp1_coeffs];
    fac1 := Factorization(f1);

    any1 := false;
    all1 := true;
    for ff in fac1 do
        d := Degree(ff[1]);
        if d eq 1 then
            jp := -Coefficient(ff[1], 0);
            denom := jp - Fp!1728;
            if denom eq 0 then
                // j=1728: E: y^2 = x^3 + x, a_p = 0 iff p = 3 mod 4
                if p mod 4 eq 3 then any1 := true; else all1 := false; end if;
            elif jp eq 0 then
                // j=0: E: y^2 = x^3 + 1, a_p = 0 iff p = 2 mod 3
                if p mod 3 eq 2 then any1 := true; else all1 := false; end if;
            else
                cc := 27*jp/denom;
                Ep := EllipticCurve([Fp| -cc, -2*cc]);
                ap := TraceOfFrobenius(Ep);
                if ap eq 0 then any1 := true; else all1 := false; end if;
            end if;
        elif d eq 2 then
            // Inert prime, residue field F_{p^2}
            Fq := GF(p^2);
            PFq<tq> := PolynomialRing(Fq);
            rts := Roots(PFq!Eltseq(ff[1]));
            if #rts eq 0 then all1 := false; continue; end if;
            jp := rts[1][1];
            denom := jp - Fq!1728;
            if denom eq 0 then
                all1 := false; continue;  // handle separately if needed
            elif jp eq 0 then
                all1 := false; continue;
            else
                cc := 27*jp/denom;
                Ep := EllipticCurve([Fq| -cc, -2*cc]);
                ap := TraceOfFrobenius(Ep);
                if ap eq 0 then any1 := true; else all1 := false; end if;
            end if;
        end if;
    end for;
    if any1 then ss1_any +:= 1; end if;
    if all1 then ss1_all +:= 1; end if;

    // === j23 over degree-4 field ===
    f23 := PFp![Fp!c : c in mp23_coeffs];
    fac23 := Factorization(f23);

    any23 := false;
    all23 := true;
    for ff in fac23 do
        d := Degree(ff[1]);
        if d eq 1 then
            jp := -Coefficient(ff[1], 0);
            denom := jp - Fp!1728;
            if denom eq 0 then
                if p mod 4 eq 3 then any23 := true; else all23 := false; end if;
            elif jp eq 0 then
                if p mod 3 eq 2 then any23 := true; else all23 := false; end if;
            else
                cc := 27*jp/denom;
                Ep := EllipticCurve([Fp| -cc, -2*cc]);
                ap := TraceOfFrobenius(Ep);
                if ap eq 0 then any23 := true; else all23 := false; end if;
            end if;
        elif d eq 2 then
            Fq := GF(p^2);
            PFq<tq> := PolynomialRing(Fq);
            rts := Roots(PFq!Eltseq(ff[1]));
            if #rts eq 0 then all23 := false; continue; end if;
            jp := rts[1][1];
            denom := jp - Fq!1728;
            if denom eq 0 or jp eq 0 then
                all23 := false; continue;
            else
                cc := 27*jp/denom;
                Ep := EllipticCurve([Fq| -cc, -2*cc]);
                ap := TraceOfFrobenius(Ep);
                if ap eq 0 then any23 := true; else all23 := false; end if;
            end if;
        elif d eq 4 then
            // Skip degree-4 for speed — only affects ss_all (rare anyway)
            // For ss_any: we'd need to check, but degree-4 primes have norm p^4
            // and supersingularity at such primes is extremely rare
            // For correctness, let's check it
            Fq := GF(p^4);
            PFq<tq> := PolynomialRing(Fq);
            rts := Roots(PFq!Eltseq(ff[1]));
            if #rts eq 0 then all23 := false; continue; end if;
            jp := rts[1][1];
            denom := jp - Fq!1728;
            if denom eq 0 or jp eq 0 then
                all23 := false; continue;
            else
                cc := 27*jp/denom;
                Ep := EllipticCurve([Fq| -cc, -2*cc]);
                ap := TraceOfFrobenius(Ep);
                if ap eq 0 then any23 := true; else all23 := false; end if;
            end if;
        else
            all23 := false;
        end if;
    end for;
    if any23 then ss23_any +:= 1; end if;
    if all23 then ss23_all +:= 1; end if;

    // Print at thresholds
    if thresh_idx le #thresholds and p ge thresholds[thresh_idx] then
        x := RealField(6)!p;
        pred := Sqrt(x)/Log(x);
        c1 := ss1_any gt 0 select RealField(4)!(ss1_any/pred) else RealField(4)!0;
        c23 := ss23_any gt 0 select RealField(4)!(ss23_any/pred) else RealField(4)!0;
        printf "%10o %8o %8o %8o %8o %9o %7o %7o %9o\n",
            p, ss1_any, ss23_any, ss1_all, ss23_all, pred, c1, c23, total;
        thresh_idx +:= 1;
    end if;
end for;

// Final
x := RealField(8)!BOUND;
pred := Sqrt(x)/Log(x);
printf "\nFinal at x = %o:\n", BOUND;
printf "  j1:  ss_any = %o, ss_all = %o, C = %o\n",
    ss1_any, ss1_all, RealField(6)!(ss1_any/pred);
printf "  j23: ss_any = %o, ss_all = %o, C = %o\n",
    ss23_any, ss23_all, RealField(6)!(ss23_any/pred);
printf "  sqrt(x)/log(x) = %o\n", pred;
printf "  Total primes: %o\n", total;

// Splitting behavior of mp23 — what fraction of primes have each type?
print "\n=== Splitting behavior of mp23 mod p ===";
split_counts := AssociativeArray();
for p in PrimesUpTo(10000) do
    if p le 3 then continue; end if;
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);
    f := PFp![Fp!c : c in mp23_coeffs];
    fac := Factorization(f);
    degs := Sort([Degree(ff[1]) : ff in fac]);
    key := Sprint(degs);
    if IsDefined(split_counts, key) then
        split_counts[key] +:= 1;
    else
        split_counts[key] := 1;
    end if;
end for;
total_small := &+[split_counts[k] : k in Keys(split_counts)];
printf "Splitting types of mp23 (primes up to 10000):\n";
for k in Sort(SetToSequence(Keys(split_counts))) do
    printf "  %o: %o (%o%%)\n", k, split_counts[k],
        RealField(4)!(100.0*split_counts[k]/total_small);
end for;
