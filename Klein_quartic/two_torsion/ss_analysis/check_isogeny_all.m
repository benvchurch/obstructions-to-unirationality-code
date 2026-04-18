/*******************************************************************************
 * check_isogeny_all.m
 *
 * For each curve with (Z/2)^2 symmetry giving two quotient elliptic curves,
 * check whether the two quotients are isogenous (same a_p) or twist-isogenous
 * (a_p agree up to sign).
 *
 * Cases:
 *   Klein twist class 2 (21-orbit): j-poly t^2 + 7184t + 16777216 over Q(sqrt(-7))
 *     [already checked in check_isogeny_21orbit.m -- twist-isogenous]
 *
 *   Fermat class 4: both quotients have j=128 (rational) -- trivially isogenous
 *   Fermat class 5: both quotients have j=8000 (rational) -- trivially isogenous
 *   Edge class 6: both quotients have j=54000 (rational) -- trivially isogenous
 *
 *   Edge class 9: two j-values -11664/625 and -3538944/25 (both rational)
 *     -- need to check
 ******************************************************************************/

SetColumns(0);

printf "=== Edge class 9: j = -11664/625 vs j = -3538944/25 ===\n\n";

// First check: are they isogenous over Q?
j1_val := -11664/625;
j2_val := -3538944/25;

E1 := EllipticCurveWithjInvariant(Rationals() ! j1_val);
E2 := EllipticCurveWithjInvariant(Rationals() ! j2_val);
E1m := MinimalModel(E1);
E2m := MinimalModel(E2);

printf "E1 (j=%o): %o\n", j1_val, E1m;
printf "  Conductor: %o\n", Conductor(E1m);
N1 := Conductor(E1m);
if N1 le 500000 then
    printf "  Cremona label: %o\n", CremonaReference(E1m);
else
    printf "  Conductor too large for Cremona database\n";
end if;

printf "E2 (j=%o): %o\n", j2_val, E2m;
printf "  Conductor: %o\n", Conductor(E2m);
N2 := Conductor(E2m);
if N2 le 500000 then
    printf "  Cremona label: %o\n", CremonaReference(E2m);
else
    printf "  Conductor too large for Cremona database\n";
end if;

// Direct isogeny check
iso, phi := IsIsogenous(E1m, E2m);
if iso then
    printf "\nE1 and E2 are ISOGENOUS over Q (degree %o)\n", Degree(phi);
else
    printf "\nE1 and E2 are NOT isogenous over Q\n";
    printf "Checking if they are twist-isogenous...\n";
end if;

// Compare traces
printf "\n%-6o | %-10o %-10o | %-6o %-6o\n",
    "p", "a_p(E1)", "a_p(E2)", "same?", "neg?";
printf "%o\n", "-" ^ 52;

same_count := 0;
neg_count := 0;
neither_count := 0;
total := 0;

for p in PrimesInInterval(7, 5000) do
    Fp := GF(p);
    // Skip primes of bad reduction
    j1p := Fp ! (Integers() ! (Numerator(j1_val) mod p)) /
           Fp ! (Integers() ! (Denominator(j1_val) mod p));
    j2p := Fp ! (Integers() ! (Numerator(j2_val) mod p)) /
           Fp ! (Integers() ! (Denominator(j2_val) mod p));

    e1 := EllipticCurveWithjInvariant(j1p);
    e2 := EllipticCurveWithjInvariant(j2p);
    a1 := p + 1 - #e1;
    a2 := p + 1 - #e2;

    total +:= 1;
    same := (a1 eq a2);
    neg := (a1 eq -a2);
    if same then same_count +:= 1;
    elif neg then neg_count +:= 1;
    else neither_count +:= 1;
    end if;

    if total le 30 or (not same and not neg) then
        printf "%-6o | %-10o %-10o | %-6o %-6o\n",
            p, a1, a2,
            same select "YES" else "--",
            neg select "NEG" else "--";
    end if;
end for;

printf "\n%o primes checked\n", total;
printf "a_p(E1) =  a_p(E2): %o  (%o%%)\n", same_count, Round(100.0*same_count/total);
printf "a_p(E1) = -a_p(E2): %o  (%o%%)\n", neg_count, Round(100.0*neg_count/total);
printf "neither:             %o\n", neither_count;

if neither_count eq 0 and neg_count eq 0 then
    printf "\n*** Curves are isogenous (same twist) ***\n";
elif neither_count eq 0 and same_count eq 0 then
    printf "\n*** Curves are quadratic twists ***\n";
elif neither_count eq 0 then
    printf "\n*** Curves are twist-isogenous ***\n";
else
    printf "\n*** Curves are NOT isogenous ***\n";
end if;

// Also check: are the j-values related by any simple transformation?
printf "\n=== Algebraic relationship between j-values ===\n";
printf "j1 = %o = %o\n", j1_val, Factorization(Integers() ! Numerator(j1_val));
printf "j2 = %o = %o\n", j2_val, Factorization(Integers() ! Numerator(j2_val));
printf "j1 * j2 = %o\n", j1_val * j2_val;
printf "j1 + j2 = %o\n", j1_val + j2_val;
printf "j1 / j2 = %o\n", j1_val / j2_val;

quit;
