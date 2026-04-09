/*******************************************************************************
 * check_isogeny.m - Check if the 3 j-invariants define isogenous elliptic curves
 ******************************************************************************/

load "two_torsion/bitangent_data.m";
K := Parent(bitangent_lines[1][1]);
w := K.1;

PQ<v> := PolynomialRing(Rationals());

// j-invariant min polys over Q
mp1_Q := v^2 + 13856*v - 26578688;
// mp2*mp3 product (absolute min poly of j2 over Q, degree 4)
mp23_Q := v^4 - 103439*v^3 + 6670405329*v^2 + 31128229267744*v + 148381159092130048;

print "mp1 (28 complexes):", mp1_Q;
print "mp23 (7+7 complexes):", mp23_Q;

disc1 := Discriminant(mp1_Q);
printf "disc(mp1) = %o\n", Factorization(Integers()!disc1);

function TraceFromJ(j_val, Fq)
    if j_val eq 0 then
        E := EllipticCurve([Fq| 0, 1]);
    elif j_val eq Fq!1728 then
        E := EllipticCurve([Fq| 1, 0]);
    else
        c := 27*j_val / (j_val - Fq!1728);
        E := EllipticCurve([Fq| -c, -2*c]);
    end if;
    return TraceOfFrobenius(E);
end function;

// For each prime where both polys split, show ALL traces
print "\n=== All traces of Frobenius at split primes ===";
print "  p : traces(j1 roots) | traces(j23 roots) | j1_traces^2 | j23_traces^2";

not_isog := false;

for p in PrimesInInterval(5, 500) do
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);
    f1 := PFp![Fp!c : c in Coefficients(mp1_Q)];
    f23 := PFp![Fp!c : c in Coefficients(mp23_Q)];

    fac1 := Factorization(f1);
    fac23 := Factorization(f23);

    if not &and[Degree(ff[1]) eq 1 : ff in fac1] then continue; end if;
    if not &and[Degree(ff[1]) eq 1 : ff in fac23] then continue; end if;

    j1_roots := [-Coefficient(ff[1], 0) : ff in fac1];
    j23_roots := [-Coefficient(ff[1], 0) : ff in fac23];

    // Skip if any root is 1728
    skip := false;
    for j in j1_roots cat j23_roots do
        if j eq Fp!1728 then skip := true; break; end if;
    end for;
    if skip then continue; end if;

    a1s := Sort([TraceFromJ(j, Fp) : j in j1_roots]);
    a23s := Sort([TraceFromJ(j, Fp) : j in j23_roots]);

    a1_sq := Sort(SetToSequence({a^2 : a in a1s}));
    a23_sq := Sort(SetToSequence({a^2 : a in a23s}));

    // For isogeny over Qbar: there should exist a pairing of roots
    // such that the traces match. At minimum, the multisets of a_p^2
    // should have overlap.
    overlap := exists{a : a in a1_sq | a in Set(a23_sq)};

    printf "%4o: j1 traces %o | j23 traces %o | a^2: %o vs %o",
        p, a1s, a23s, a1_sq, a23_sq;
    if not overlap then
        printf " *** NO OVERLAP";
        not_isog := true;
    end if;
    print "";
end for;

if not_isog then
    print "\nConclusion: j1 and j23 curves are NOT isogenous over Qbar";
    print "(a_p^2 values have no overlap at some primes)";
else
    print "\nConclusion: a_p^2 values always overlap => possibly isogenous";
end if;

// Also check: are the j1-curves CM?
print "\n=== CM check ===";
// disc(mp1) = 2^14 * 3^2 * 7 * 17^2
// sqrt(disc) = 2^7 * 3 * 17 * sqrt(7) = 128 * 51 * sqrt(7) = 6528*sqrt(7)
// So j1 in Q(sqrt(7)), NOT Q(sqrt(-7))
// j = (-13856 +/- 6528*sqrt(7))/2 = -6928 +/- 3264*sqrt(7)
printf "j1 values: -6928 +/- 3264*sqrt(7)\n";
printf "j1 lives in Q(sqrt(7))\n\n";

// Check if j1 matches CM j-invariants
// Over Q(sqrt(7)):
// The CM j-invariants for discriminant D are algebraic integers
// j1 = -6928 + 3264*sqrt(7) ≈ -6928 + 3264*2.6458 = -6928 + 8634.5 = 1706.5
// j1' = -6928 - 3264*sqrt(7) ≈ -6928 - 8634.5 = -15562.5
// These don't look like standard CM values

// Better: check if the curves have CM by looking at endomorphism ring
// via the trace criterion: E has CM by Q(sqrt(-d)) iff a_p = 0 for all
// primes p that are inert in Q(sqrt(-d))
print "=== CM test via trace pattern ===";
// Collect a_p values for j1
printf "Traces for j1 curve (first root mod p):\n";
j1_traces := [];
for p in PrimesInInterval(5, 200) do
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);
    f1 := PFp![Fp!c : c in Coefficients(mp1_Q)];
    fac1 := Factorization(f1);
    if not &and[Degree(ff[1]) eq 1 : ff in fac1] then continue; end if;
    j1p := -Coefficient(fac1[1][1], 0);
    if j1p eq Fp!1728 then continue; end if;
    ap := TraceFromJ(j1p, Fp);
    Append(~j1_traces, <p, ap>);
    printf "  p=%o: a_p=%o\n", p, ap;
end for;

// Count how many a_p = 0
zero_count := #[t : t in j1_traces | t[2] eq 0];
printf "a_p = 0 for %o out of %o primes\n", zero_count, #j1_traces;
if zero_count gt #j1_traces / 3 then
    print "Pattern suggests CM";
else
    print "Pattern suggests NOT CM (a_p = 0 is rare)";
end if;
