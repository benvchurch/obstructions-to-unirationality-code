/*******************************************************************************
 * check_isogeny_21orbit.m
 *
 * Check whether the two Z/2-quotient elliptic curves of the 21-orbit
 * (j-poly t^2 + 7184t + 16777216, roots in Q(sqrt(-7))) are isogenous.
 *
 * At split primes where both j-values reduce to F_p, compare traces of
 * Frobenius.  Isogenous curves have the same a_p (up to sign from twist).
 ******************************************************************************/

SetColumns(0);

PQ<t> := PolynomialRing(Rationals());
j_poly := t^2 + 7184*t + 16777216;

printf "Checking isogeny of the two Z/2-quotient elliptic curves\n";
printf "j min poly: %o\n\n", j_poly;

printf "%-6o | %-10o %-10o | %-10o %-10o | %-6o %-6o\n",
    "p", "j1", "j2", "a_p(j1)", "a_p(j2)", "same?", "neg?";
printf "%o\n", "-" ^ 72;

same_count := 0;
neg_count := 0;
neither_count := 0;
total := 0;

for p in PrimesInInterval(5, 10000) do
    Fp := GF(p);
    Rp<tp> := PolynomialRing(Fp);
    jp := Rp ! [Fp ! c : c in [16777216, 7184, 1]];
    roots := Roots(jp);

    if #roots ne 2 then continue; end if;  // need both roots in F_p

    j1 := roots[1][1];
    j2 := roots[2][1];

    // Build elliptic curves and get traces
    E1 := EllipticCurveWithjInvariant(j1);
    E2 := EllipticCurveWithjInvariant(j2);
    a1 := p + 1 - #E1;
    a2 := p + 1 - #E2;

    total +:= 1;
    same := (a1 eq a2);
    neg := (a1 eq -a2);
    if same then same_count +:= 1;
    elif neg then neg_count +:= 1;
    else neither_count +:= 1;
    end if;

    if total le 40 or (not same and not neg) then
        printf "%-6o | %-10o %-10o | %-10o %-10o | %-6o %-6o\n",
            p, j1, j2, a1, a2,
            same select "YES" else "--",
            neg select "NEG" else "--";
    end if;
end for;

printf "\n%o split primes checked\n", total;
printf "a_p(j1) =  a_p(j2): %o  (%o%%)\n", same_count, Round(100.0*same_count/total);
printf "a_p(j1) = -a_p(j2): %o  (%o%%)\n", neg_count, Round(100.0*neg_count/total);
printf "neither:             %o\n", neither_count;

if neither_count eq 0 and neg_count eq 0 then
    printf "\n*** All traces agree: curves are isogenous (same twist) ***\n";
elif neither_count eq 0 and same_count eq 0 then
    printf "\n*** All traces are negated: curves are quadratic twists ***\n";
elif neither_count eq 0 then
    printf "\n*** Traces agree up to sign: curves are twist-isogenous ***\n";
    printf "*** (isogenous but possibly different twists at each prime) ***\n";
else
    printf "\n*** Curves are NOT isogenous ***\n";
end if;

quit;
