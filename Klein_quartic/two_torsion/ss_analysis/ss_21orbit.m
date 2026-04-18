/*******************************************************************************
 * ss_21orbit.m
 *
 * Supersingular primes for the Z/2-symmetry elliptic curves of the Klein
 * twist 21-orbit (Igusa class 2).
 *
 * The 21-orbit genus-2 Pryms have an extra involution beyond the hyperelliptic
 * one.  The Z/2 quotient gives elliptic curves whose j-invariant satisfies
 *     j^2 + 7184 j + 16777216 = 0
 * with discriminant -2^8 * 3^2 * 7 * 31^2, so j in Q(sqrt(-7)).
 *
 * Since the two conjugate elliptic curves are isogenous (Galois conjugate over
 * Q(sqrt(-7))), supersingularity at a rational prime p is well-defined:
 * check at any/either prime of Q(sqrt(-7)) above p.
 *
 * For split primes (Legendre symbol (-7|p) = 1): the j-poly has roots in F_p,
 *   so build E over F_p and check a_p = 0.
 * For inert primes ((-7|p) = -1): roots live in F_{p^2},
 *   so build E over F_{p^2} and check #E = (p+1)^2 (equiv to a_p = 0).
 ******************************************************************************/

SetColumns(0);
BOUND := 100000;

PQ<t> := PolynomialRing(Rationals());
j_poly := t^2 + 7184*t + 16777216;

printf "Supersingular primes for Klein twist 21-orbit Z/2 elliptic curves\n";
printf "j min poly: %o\n", j_poly;
printf "Bound: %o\n\n", BOUND;

// Verify discriminant
disc := 7184^2 - 4*16777216;
printf "Discriminant: %o = ", disc;
printf "%o\n", Factorization(Abs(disc));
printf "j-values lie in Q(sqrt(-7))\n\n";

ss_primes := [];
bad_primes := {2, 7, 31};  // dividing disc or leading coeff

for p in PrimesInInterval(3, BOUND) do
    if p in bad_primes then continue; end if;

    Fp := GF(p);
    Rp<tp> := PolynomialRing(Fp);
    jp := Rp ! [Fp ! c : c in [16777216, 7184, 1]];
    roots := Roots(jp);

    is_ss := false;

    if #roots gt 0 then
        // Split prime: j-poly has roots in F_p
        for pair in roots do
            j0 := pair[1];
            if j0 eq Fp ! 0 then
                if p mod 3 eq 2 then is_ss := true; end if;
                continue;
            end if;
            if j0 eq Fp ! 1728 then
                if p mod 4 eq 3 then is_ss := true; end if;
                continue;
            end if;
            E := EllipticCurveWithjInvariant(j0);
            ap := p + 1 - #E;
            if ap eq 0 then
                is_ss := true;
                break;
            end if;
        end for;
    else
        // Inert prime: work over F_{p^2}
        Fp2 := GF(p^2);
        Rp2<tp2> := PolynomialRing(Fp2);
        jp2 := Rp2 ! [Fp2 ! c : c in [16777216, 7184, 1]];
        roots2 := Roots(jp2);
        if #roots2 gt 0 then
            j0 := roots2[1][1];
            if j0 eq Fp2 ! 0 then
                if p mod 3 eq 2 then is_ss := true; end if;
            elif j0 eq Fp2 ! 1728 then
                if p mod 4 eq 3 then is_ss := true; end if;
            else
                E := EllipticCurveWithjInvariant(j0);
                npts := #E;
                // SS iff #E(F_{p^2}) = (p+1)^2
                if npts eq (p+1)^2 then
                    is_ss := true;
                end if;
            end if;
        end if;
    end if;

    if is_ss then
        Append(~ss_primes, p);
    end if;
end for;

printf "Found %o supersingular primes up to %o\n\n", #ss_primes, BOUND;

// Separate by splitting behavior
ss_split := [p : p in ss_primes | KroneckerSymbol(-7, p) eq 1];
ss_inert := [p : p in ss_primes | KroneckerSymbol(-7, p) eq -1];

printf "Split in Q(sqrt(-7)): %o primes\n", #ss_split;
printf "Inert in Q(sqrt(-7)): %o primes\n\n", #ss_inert;

// Print all primes (if not too many)
if #ss_primes le 200 then
    printf "All SS primes: %o\n\n", ss_primes;
end if;

if #ss_split le 100 then
    printf "Split SS primes: %o\n\n", ss_split;
end if;
if #ss_inert le 100 then
    printf "Inert SS primes: %o\n\n", ss_inert;
end if;

// =====================================================================
// Residue analysis
// =====================================================================

printf "=== Residue analysis (all SS primes) ===\n\n";

// mod 7
printf "--- mod 7 ---\n";
for r in [0..6] do
    ct := #[p : p in ss_primes | p mod 7 eq r];
    if ct gt 0 then printf "  %o mod 7: %o\n", r, ct; end if;
end for;

// mod 8
printf "\n--- mod 8 ---\n";
for r in [0..7] do
    ct := #[p : p in ss_primes | p mod 8 eq r];
    if ct gt 0 then printf "  %o mod 8: %o\n", r, ct; end if;
end for;

// mod 3
printf "\n--- mod 3 ---\n";
for r in [0..2] do
    ct := #[p : p in ss_primes | p mod 3 eq r];
    if ct gt 0 then printf "  %o mod 3: %o\n", r, ct; end if;
end for;

// mod 4
printf "\n--- mod 4 ---\n";
for r in [0..3] do
    ct := #[p : p in ss_primes | p mod 4 eq r];
    if ct gt 0 then printf "  %o mod 4: %o\n", r, ct; end if;
end for;

// mod 7*4 = 28
printf "\n--- mod 28 ---\n";
for r in [0..27] do
    ct := #[p : p in ss_primes | p mod 28 eq r];
    if ct gt 0 then printf "  %o mod 28: %o\n", r, ct; end if;
end for;

// mod 56 = 7*8
printf "\n--- mod 56 ---\n";
for r in [0..55] do
    ct := #[p : p in ss_primes | p mod 56 eq r];
    if ct gt 0 then printf "  %o mod 56: %o\n", r, ct; end if;
end for;

// mod 31
printf "\n--- mod 31 ---\n";
for r in [0..30] do
    ct := #[p : p in ss_primes | p mod 31 eq r];
    if ct gt 0 then printf "  %o mod 31: %o\n", r, ct; end if;
end for;

// =====================================================================
// Residue analysis: split vs inert separately
// =====================================================================
printf "\n=== Split SS primes: residues ===\n";

printf "\n--- mod 7 ---\n";
for r in [0..6] do
    ct := #[p : p in ss_split | p mod 7 eq r];
    if ct gt 0 then printf "  %o mod 7: %o\n", r, ct; end if;
end for;

printf "\n--- mod 8 ---\n";
for r in [0..7] do
    ct := #[p : p in ss_split | p mod 8 eq r];
    if ct gt 0 then printf "  %o mod 8: %o\n", r, ct; end if;
end for;

printf "\n--- mod 28 ---\n";
for r in [0..27] do
    ct := #[p : p in ss_split | p mod 28 eq r];
    if ct gt 0 then printf "  %o mod 28: %o\n", r, ct; end if;
end for;

printf "\n=== Inert SS primes: residues ===\n";

printf "\n--- mod 7 ---\n";
for r in [0..6] do
    ct := #[p : p in ss_inert | p mod 7 eq r];
    if ct gt 0 then printf "  %o mod 7: %o\n", r, ct; end if;
end for;

printf "\n--- mod 8 ---\n";
for r in [0..7] do
    ct := #[p : p in ss_inert | p mod 8 eq r];
    if ct gt 0 then printf "  %o mod 8: %o\n", r, ct; end if;
end for;

printf "\n--- mod 28 ---\n";
for r in [0..27] do
    ct := #[p : p in ss_inert | p mod 28 eq r];
    if ct gt 0 then printf "  %o mod 28: %o\n", r, ct; end if;
end for;

// =====================================================================
// Density analysis
// =====================================================================
printf "\n=== Density ===\n\n";

thresholds := [1000, 5000, 10000, 50000, BOUND];
for N in thresholds do
    if N gt BOUND then continue; end if;
    ct := #[p : p in ss_primes | p le N];
    total := #PrimesInInterval(3, N);
    sqrtN := Sqrt(1.0 * N);
    logN := Log(1.0 * N);
    lt_pred := sqrtN / logN;  // Lang-Trotter for non-CM
    printf "Up to %o: %o ss primes / %o total primes", N, ct, total;
    printf "  (sqrt(N)/log(N) = %.1o, ratio = %.2o)\n", lt_pred, ct / lt_pred;
end for;

// =====================================================================
// Cross-reference with Klein Jacobian ss primes (J ~ E^3, E = 49a1, j = -3375)
// =====================================================================
printf "\n=== Cross-reference with J(C_twist) = 49a1^3 ===\n\n";

ss_49a1 := [];
for p in PrimesInInterval(3, BOUND) do
    if p eq 7 then continue; end if;
    Fp := GF(p);
    E := EllipticCurveWithjInvariant(Fp ! (-3375 mod p));
    ap := p + 1 - #E;
    if ap eq 0 then
        Append(~ss_49a1, p);
    end if;
end for;

printf "49a1 (j=-3375) has %o ss primes up to %o\n", #ss_49a1, BOUND;

overlap := [p : p in ss_primes | p in {x : x in ss_49a1}];
printf "Overlap with 21-orbit Z/2 elliptic: %o\n", #overlap;
if #overlap le 50 then
    printf "Overlap primes: %o\n", overlap;
end if;

printf "\n21-orbit primes NOT in 49a1 ss: %o\n",
    #[p : p in ss_primes | not (p in {x : x in ss_49a1})];
printf "49a1 primes NOT in 21-orbit ss: %o\n",
    #[p : p in ss_49a1 | not (p in {x : x in ss_primes})];

// =====================================================================
// Cross-reference with other Prym j-invariant classes
// =====================================================================
printf "\n=== Cross-reference with 28-orbit Z/3 elliptic ===\n\n";

j1_poly := PQ ! (t^2 + 13856*t - 26578688);
j1_int := j1_poly;  // already integral
ss_j1 := [];
lc := LeadingCoefficient(j1_int);
for p in PrimesInInterval(5, BOUND) do
    if Integers() ! lc mod p eq 0 then continue; end if;
    Fp := GF(p);
    Rp<tp> := PolynomialRing(Fp);
    mp := Rp ! [Fp ! (Integers() ! c) : c in Coefficients(j1_int)];
    roots := Roots(mp);
    for pair in roots do
        j0 := pair[1];
        if j0 eq Fp ! 1728 then
            if p mod 4 eq 3 then Include(~ss_j1, p); end if;
            continue;
        end if;
        if j0 eq Fp ! 0 then
            if p mod 3 eq 2 then Include(~ss_j1, p); end if;
            continue;
        end if;
        E := EllipticCurveWithjInvariant(j0);
        ap := p + 1 - #E;
        if ap eq 0 then
            Include(~ss_j1, p);
            break;
        end if;
    end for;
end for;

// Convert to set for membership testing
ss_j1_set := {p : p in ss_j1};
ss_21_set := {p : p in ss_primes};

printf "28-orbit Z/3 elliptic: %o ss primes\n", #ss_j1;
overlap_j1 := ss_21_set meet ss_j1_set;
printf "Overlap with 21-orbit: %o\n", #overlap_j1;
if #overlap_j1 le 50 then
    printf "Overlap primes: %o\n", Sort(Setseq(overlap_j1));
end if;

quit;
