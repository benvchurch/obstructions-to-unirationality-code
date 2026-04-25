// Check whether the two Z/2-quotient elliptic curves from Edge class 8
// are isogenous. Corrected sign: j2 = +3538944/25 (not negative).
//
// Also: verify the j-invariant formula directly from the Legendre lambda.

QQ := Rationals();

j1 := -11664/625;
j2 := 3538944/25;   // CORRECTED: positive

printf "j1 = %o\n", j1;
printf "j2 = %o\n", j2;
printf "j1 factored: %o / %o\n", Factorization(Abs(Numerator(j1))), Factorization(Denominator(j1));
printf "j2 factored: %o / %o\n", Factorization(Numerator(j2)), Factorization(Denominator(j2));

// Verify the formula: for lambda = -2/5, the TWO elliptic quotients
// come from t = lambda +/- sqrt(lambda^2 - 1).
// j(t) = 256*(t^4+t^2+1)^3 / (t^4*(t^2+1)^2)

// lambda = -2/5
lam := -2/5;
disc := lam^2 - 1;  // 4/25 - 1 = -21/25
printf "\nlambda = %o, lambda^2 - 1 = %o\n", lam, disc;

// Work in Q(sqrt(-21))
K<sq> := QuadraticField(-21);
PK<u> := PolynomialRing(K);

t_plus := K!lam + sq/5;     // -2/5 + sqrt(-21)/5
t_minus := K!lam - sq/5;    // -2/5 - sqrt(-21)/5

printf "t+ = %o\n", t_plus;
printf "t- = %o\n", t_minus;
printf "t+ * t- = %o (should be 1)\n", t_plus * t_minus;

function JFromT(t)
    return 256*(t^4+t^2+1)^3 / (t^4*(t^2+1)^2);
end function;

j_plus := JFromT(t_plus);
j_minus := JFromT(t_minus);

printf "\nj(t+) = %o\n", j_plus;
printf "j(t-) = %o\n", j_minus;
printf "AbsMinPoly j(t+) = %o\n", AbsoluteMinimalPolynomial(j_plus);
printf "AbsMinPoly j(t-) = %o\n", AbsoluteMinimalPolynomial(j_minus);

// Now do the same for lambda = -5/2
lam2 := -5/2;
disc2 := lam2^2 - 1;  // 25/4 - 1 = 21/4
printf "\nlambda = %o, lambda^2 - 1 = %o\n", lam2, disc2;

K2<sq2> := QuadraticField(21);

t2_plus := K2!lam2 + sq2/2;
t2_minus := K2!lam2 - sq2/2;

printf "t+ = %o\n", t2_plus;
printf "t- = %o\n", t2_minus;
printf "t+ * t- = %o (should be 1)\n", t2_plus * t2_minus;

j2_plus := JFromT(t2_plus);
j2_minus := JFromT(t2_minus);

printf "\nj(t+) = %o\n", j2_plus;
printf "j(t-) = %o\n", j2_minus;
printf "AbsMinPoly j(t+) = %o\n", AbsoluteMinimalPolynomial(j2_plus);
printf "AbsMinPoly j(t-) = %o\n", AbsoluteMinimalPolynomial(j2_minus);

// So for lambda=-2/5 we get two j-invariants j+ and j-.
// For lambda=-5/2 we get two j-invariants j2+ and j2-.
// The set {j+, j-} should equal the set {j2+, j2-} if the genus-2 curve
// is the same!

printf "\n=== Summary ===\n";
printf "From lambda = -2/5: j = %o and %o\n",
    AbsoluteMinimalPolynomial(j_plus), AbsoluteMinimalPolynomial(j_minus);
printf "From lambda = -5/2: j = %o and %o\n",
    AbsoluteMinimalPolynomial(j2_plus), AbsoluteMinimalPolynomial(j2_minus);

// Now build elliptic curves and check isogeny
function CurveFromJ(j)
    if j eq 0 then return EllipticCurve([QQ| 0, 1]); end if;
    if j eq 1728 then return EllipticCurve([QQ| 1, 0]); end if;
    c := j / (j - 1728);
    return EllipticCurve([QQ| -27*c, -54*c]);
end function;

// Get the rational j-invariants
j_vals := [];
for mp in [AbsoluteMinimalPolynomial(j_plus), AbsoluteMinimalPolynomial(j_minus),
           AbsoluteMinimalPolynomial(j2_plus), AbsoluteMinimalPolynomial(j2_minus)] do
    if Degree(mp) eq 1 then
        jv := -Coefficient(mp, 0) / Coefficient(mp, 1);
        Append(~j_vals, jv);
        printf "Rational j = %o\n", jv;
    else
        printf "Non-rational j, min poly = %o\n", mp;
    end if;
end for;

// Deduplicate
j_set := Setseq(Set(j_vals));
printf "\nDistinct rational j-values: %o\n", j_set;

if #j_set ge 2 then
    E1 := MinimalModel(CurveFromJ(j_set[1]));
    E2 := MinimalModel(CurveFromJ(j_set[2]));
    printf "\nE1 (j=%o): %o, cond = %o\n", j_set[1], aInvariants(E1), Factorization(Conductor(E1));
    printf "E2 (j=%o): %o, cond = %o\n", j_set[2], aInvariants(E2), Factorization(Conductor(E2));
    printf "IsIsogenous over Q: %o\n", IsIsogenous(E1, E2);

    // Check modular polynomials
    printf "\n=== Modular polynomial check ===\n";
    for N in [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25] do
        phi := ClassicalModularPolynomial(N);
        val := Evaluate(phi, [j_set[1], j_set[2]]);
        if val eq 0 then
            printf "  Phi_%o(j1, j2) = 0  =>  %o-isogeny!\n", N, N;
        end if;
    end for;

    // Twist search
    printf "\n=== Twist search ===\n";
    for d in [-200..200] do
        if d eq 0 then continue; end if;
        if not IsSquarefree(d) then continue; end if;
        Et := QuadraticTwist(E1, d);
        if IsIsogenous(Et, E2) then
            printf "  E2 ~ twist(E1, %o)  (cond = %o)\n", d, Conductor(Et);
        end if;
    end for;

    // a_p comparison
    printf "\n=== a_p data ===\n";
    printf "  p | a_p(E1) | a_p(E2)\n";
    for p in PrimesInInterval(2, 100) do
        if Conductor(E1) mod p eq 0 or Conductor(E2) mod p eq 0 then continue; end if;
        a1 := TraceOfFrobenius(E1, p);
        a2 := TraceOfFrobenius(E2, p);
        printf "%4o | %6o | %6o\n", p, a1, a2;
    end for;
end if;

printf "\nDone.\n";
quit;
