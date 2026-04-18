/*******************************************************************************
 * ss_coincidences.m
 *
 * For each of the three quartics, collect the distinct elliptic j-invariant
 * minimal polynomials found via the Z/2 and Z/3 quotients of genus-2 Pryms.
 * For each pair of non-Galois-conjugate elliptic curves arising from the SAME
 * quartic, compute supersingular primes up to BOUND and look for "inclusion
 * coincidences": pairs where the symmetric difference of ss prime sets is small
 * relative to the union.
 *
 * A prime p is "ss for j-class m(t)" if m(t) has a root j0 in F_p such that
 * the elliptic curve with j-invariant j0 has a_p = 0.
 ******************************************************************************/

SetColumns(0);
BOUND := 10000;

// Helper: given a min poly m(t) over Q (as a univariate over Z after clearing
// denominators), return the set of primes p <= BOUND where the j-class is
// supersingular.
function SSPrimes(m_poly, BOUND)
    ss := {};
    // Bad primes: divide leading coeff or discriminant
    lc := LeadingCoefficient(m_poly);
    disc := Discriminant(m_poly);
    for p in PrimesInInterval(5, BOUND) do
        if lc mod p eq 0 then continue; end if;
        Fp := GF(p);
        Rp<tp> := PolynomialRing(Fp);
        mp := Rp ! [Fp ! (Integers() ! c) : c in Coefficients(m_poly)];
        roots := Roots(mp);
        for pair in roots do
            j0 := pair[1];
            if j0 eq Fp ! 0 then
                // j = 0: ss iff p = 2 mod 3
                if p mod 3 eq 2 then Include(~ss, p); end if;
                continue;
            end if;
            if j0 eq Fp ! 1728 then
                // j = 1728: ss iff p = 3 mod 4
                if p mod 4 eq 3 then Include(~ss, p); end if;
                continue;
            end if;
            E := EllipticCurveWithjInvariant(j0);
            ap := p + 1 - #E;
            if ap eq 0 then
                Include(~ss, p);
                break;  // one ss root suffices
            end if;
            // Also check the quadratic twist (ap -> -ap)
            if (-ap) eq 0 then
                Include(~ss, p);
                break;
            end if;
        end for;
    end for;
    return ss;
end function;

// Helper: clear denominators of a polynomial over Q
function ClearDenominators(f)
    coeffs := Coefficients(f);
    denoms := [Denominator(c) : c in coeffs];
    L := LCM(denoms);
    R := PolynomialRing(Integers());
    return R ! [Integers() ! (c * L) : c in coeffs];
end function;

procedure AnalyzePairs(label, j_polys, j_labels)
    printf "\n%o\n%o\n", "=" ^ 60, label;
    printf "%o\n", "=" ^ 60;

    n := #j_polys;
    printf "%o elliptic j-classes:\n", n;
    for i in [1..n] do
        printf "  [%o] %o: %o\n", i, j_labels[i], j_polys[i];
    end for;

    // Compute ss primes for each
    ss_sets := [];
    for i in [1..n] do
        m_int := ClearDenominators(j_polys[i]);
        ss := SSPrimes(m_int, BOUND);
        Append(~ss_sets, ss);
        printf "\n  [%o] %o: %o ss primes up to %o\n", i, j_labels[i], #ss, BOUND;
        if #ss le 30 then
            printf "    primes: %o\n", Sort(Setseq(ss));
        else
            sorted := Sort(Setseq(ss));
            printf "    first 20: %o ...\n", sorted[1..20];
        end if;
    end for;

    // Compare all pairs
    printf "\n--- Pairwise comparison ---\n";
    for i in [1..n] do
        for j in [i+1..n] do
            A := ss_sets[i];
            B := ss_sets[j];
            inter := A meet B;
            sym_diff := (A join B) diff inter;
            union := A join B;
            printf "\n  [%o] vs [%o]: |A|=%o, |B|=%o, |A∩B|=%o, |AΔB|=%o, |A∪B|=%o\n",
                i, j, #A, #B, #inter, #sym_diff, #union;
            if #union gt 0 then
                ratio := 1.0 * #sym_diff / #union;
                printf "    |AΔB|/|A∪B| = %.3o", ratio;
                if ratio lt 0.5 then
                    printf "  *** NOTABLE OVERLAP ***";
                end if;
                printf "\n";
            end if;
            if #inter gt 0 then
                printf "    shared ss primes: %o\n", Sort(Setseq(inter));
            end if;
            // Check inclusion: is A ⊂ B or B ⊂ A?
            if A subset B and #A gt 0 then
                printf "    A ⊂ B (full inclusion of [%o] in [%o])\n", i, j;
            end if;
            if B subset A and #B gt 0 then
                printf "    B ⊂ A (full inclusion of [%o] in [%o])\n", j, i;
            end if;
        end for;
    end for;
end procedure;

// =====================================================================
// Define the j min polys for each quartic
// =====================================================================
PQ<t> := PolynomialRing(Rationals());

// --- KLEIN TWIST ---
klein_polys := [
    t^2 + 13856*t - 26578688,
    t^4 - 103439*t^3 + 6670405329*t^2 + 31128229267744*t + 148381159092130048,
    t^2 + 7184*t + 16777216
];
klein_labels := [
    "Z/3 class 1 (28 cpx)",
    "Z/3 classes 3,4 (14 cpx)",
    "Z/2 class 2 (21 cpx)"
];

// --- FERMAT ---
fermat_polys := [
    t^4 + 73216*t^3 + 1533640704*t^2 + 6119514701824*t - 15081210455785472,
    t - 8000,
    t - 128
];
fermat_labels := [
    "Z/3 classes 2,3 (32 cpx)",
    "Z/3+Z/2 class 5 (j=8000, CM sqrt-2)",
    "Z/2 class 4 (j=128, D4 curve)"
];

// --- EDGE ---
edge_polys := [
    t - 54000,
    t^2 - 775180000/729*t + 40873252000000/6561,
    t^2 - 541157005431/15625*t + 25745806977673041/390625,
    t + 11664/625,
    t - 3538944/25
];
edge_labels := [
    "Z/3+Z/2 class 6 (j=54000, CM sqrt-3)",
    "Z/3 class 7 (4 cpx)",
    "Z/3 class 10 (1 cpx, singleton)",
    "Z/2 class 9 (j=-11664/625)",
    "Z/2 class 9 (j=3538944/25)"
];

// =====================================================================
// Run
// =====================================================================
SetOutputFile("results/ss_coincidences.log" : Overwrite := true);

AnalyzePairs("KLEIN TWIST", klein_polys, klein_labels);
AnalyzePairs("FERMAT", fermat_polys, fermat_labels);
AnalyzePairs("EDGE", edge_polys, edge_labels);

UnsetOutputFile();
printf "\nDone. Results in results/ss_coincidences.log\n";
quit;
