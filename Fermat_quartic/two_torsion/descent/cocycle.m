/*******************************************************************************
 * cocycle_char0.m
 *
 * Compute the descent cocycle lambda = f * sigma(f) over Q(sqrt(-3)).
 *
 * C: u^4 + t^4 + 1 = 0
 * q1 = 2t^2 + (1-w)u^2 + (1+w),  sigma(q1) = 2t^2 + (1+w)u^2 + (1-w)
 * q1 * sigma(q1) = 4g where g = t^2*u^2 + t^2 - u^2.
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<w> := NumberField(x^2 + 3);  // w = sqrt(-3)

// Function field of C over K
Kt<t> := FunctionField(K);
Ktu<u> := PolynomialRing(Kt);
ff := u^4 + t^4 + 1;
FF<uu> := FunctionField(ff);
elt_t := FF ! t;
elt_u := uu;

q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);
sq1 := 2*elt_t^2 + (1+w)*elt_u^2 + (1-w);
g := elt_t^2*elt_u^2 + elt_t^2 - elt_u^2;
printf "q1 * sigma(q1) = 4g? %o\n\n", q1*sq1 eq 4*g;

// Compute half-divisors
function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

D_q1 := Divisor(q1);
D_sq1 := Divisor(sq1);
ok1, D_half := HalfDiv(D_q1);
ok2, sD_half := HalfDiv(D_sq1);
printf "D all even? %o, sigma(D) all even? %o\n", ok1, ok2;

ddiff := D_half - sD_half;
printf "D - sigma(D):\n";
for pl in Support(ddiff) do
    v := Valuation(ddiff, pl);
    if v ne 0 then printf "  deg-%o place, mult %o\n", Degree(pl), v; end if;
end for;

// Find f with div(f) = D - sigma(D)
V, phi := RiemannRochSpace(sD_half - D_half);
printf "\ndim L(sigma(D) - D) = %o\n", Dimension(V);
f := phi(V.1);
printf "f = %o\n\n", f;

// Extract coefficients of f in K(t)[u]
coeffs_f := Eltseq(f);
printf "f coefficients [const, u, u^2, u^3]:\n";
for i in [1..#coeffs_f] do
    printf "  coeff[u^%o] = %o\n", i-1, coeffs_f[i];
end for;

// Apply sigma: w -> -w
// For K(t) elements, conjugate means w -> -w
// We construct sigma(f) by conjugating each coefficient
sigma := hom<K -> K | -w>;

function SigmaKt(elt)
    // Apply sigma to an element of K(t)
    // elt = num(t)/den(t) where coefficients are in K
    n := Numerator(elt);
    d := Denominator(elt);
    // n and d are in K[t]
    Kpol := Parent(n);
    sigma_n := Kpol ! [sigma(Coefficient(n, i)) : i in [0..Degree(n)]];
    sigma_d := Kpol ! [sigma(Coefficient(d, i)) : i in [0..Degree(d)]];
    return Parent(elt) ! (sigma_n / sigma_d);
end function;

sigma_coeffs := [SigmaKt(c) : c in coeffs_f];
printf "\nsigma(f) coefficients:\n";
for i in [1..#sigma_coeffs] do
    printf "  coeff[u^%o] = %o\n", i-1, sigma_coeffs[i];
end for;

sigma_f := &+[FF ! sigma_coeffs[i] * elt_u^(i-1) : i in [1..#sigma_coeffs]];
printf "\nsigma(f) = %o\n\n", sigma_f;

// Compute lambda = f * sigma(f)
lambda := f * sigma_f;
printf "lambda = f * sigma(f) = %o\n\n", lambda;

// lambda should be constant in Q*
lambda_coeffs := Eltseq(lambda);
printf "lambda coefficients:\n";
for i in [1..#lambda_coeffs] do
    printf "  coeff[u^%o] = %o\n", i-1, lambda_coeffs[i];
end for;

// Verify by hand computation:
// f * sigma(f) should equal -2/3 on C
printf "\nlambda = -2/3? %o\n", lambda eq FF!(-2/3);

quit;
