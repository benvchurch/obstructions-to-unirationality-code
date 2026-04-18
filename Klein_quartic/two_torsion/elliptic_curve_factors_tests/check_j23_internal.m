/*******************************************************************************
 * check_j23_internal.m - Are the 4 roots of mp23 pairwise isogenous?
 *
 * mp23 = v^4 - 103439v^3 + 6670405329v^2 + 31128229267744v + 148381159092130048
 * Over Q(sqrt(-7)), mp23 = mp2 * mp3 where mp2, mp3 are conjugate quadratics.
 * Question: are curves from mp2 isogenous to curves from mp3 over Qbar?
 ******************************************************************************/

PQ<v> := PolynomialRing(Rationals());
mp23_Q := v^4 - 103439*v^3 + 6670405329*v^2 + 31128229267744*v + 148381159092130048;

K<w> := QuadraticField(-7);
PK<u> := PolynomialRing(K);
fac_K := Factorization(PK!mp23_Q);
printf "mp23 over Q(sqrt(-7)): %o factors of degrees %o\n",
    #fac_K, [Degree(f[1]) : f in fac_K];
for f in fac_K do
    printf "  %o\n", f[1];
end for;

mp2 := fac_K[1][1];
mp3 := fac_K[2][1];

function TraceFromJ(j_val, Fq)
    if j_val eq 0 then
        E := EllipticCurve([Fq| 0, 1]);
    elif j_val eq Fq!1728 then
        E := EllipticCurve([Fq| 1, 0]);
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

// At primes where mp23 splits completely over F_p, compare traces
// from mp2 roots vs mp3 roots

print "\n=== Traces from mp2 vs mp3 roots ===";
print "  p: mp2_traces | mp3_traces | a_p^2 sets | overlap?";

PFp_gen<t> := PolynomialRing(Rationals());

for p in PrimesInInterval(5, 500) do
    Fp := GF(p);
    PFp<tp> := PolynomialRing(Fp);

    // Factor mp23 over F_p
    f23 := PFp![Fp!c : c in Coefficients(PQ!mp23_Q)];
    fac_p := Factorization(f23);
    if not &and[Degree(ff[1]) eq 1 : ff in fac_p] then continue; end if;
    all_roots := [-Coefficient(ff[1], 0) : ff in fac_p];

    // Also factor mp2 over F_p (need sqrt(-7) in F_p)
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
    fac2_p := Factorization(f2);

    if not &and[Degree(ff[1]) eq 1 : ff in fac2_p] then continue; end if;
    mp2_roots := {-Coefficient(ff[1], 0) : ff in fac2_p};
    mp3_roots := {r : r in all_roots | r notin mp2_roots};

    // Compute traces
    mp2_traces := [];
    mp3_traces := [];
    all_ok := true;
    for r in SetToSequence(mp2_roots) do
        ok, ap := TraceFromJ(r, Fp);
        if not ok then all_ok := false; break; end if;
        Append(~mp2_traces, ap);
    end for;
    if not all_ok then continue; end if;
    for r in SetToSequence(mp3_roots) do
        ok, ap := TraceFromJ(r, Fp);
        if not ok then all_ok := false; break; end if;
        Append(~mp3_traces, ap);
    end for;
    if not all_ok then continue; end if;

    Sort(~mp2_traces);
    Sort(~mp3_traces);

    sq2 := {a^2 : a in mp2_traces};
    sq3 := {a^2 : a in mp3_traces};
    overlap := sq2 meet sq3;

    printf "%4o: mp2 %o | mp3 %o | a^2: %o vs %o",
        p, mp2_traces, mp3_traces, sq2, sq3;
    if #overlap eq 0 then
        printf " *** NO OVERLAP => NOT isogenous";
    end if;
    print "";
end for;
