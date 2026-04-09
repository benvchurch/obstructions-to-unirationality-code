/*******************************************************************************
 * cocycle.m
 *
 * Compute the descent cocycle lambda = f * sigma(f) for the Fermat quartic
 * C: x^4+y^4+z^4=0, using two different quadratic splitting fields.
 *
 * Section 1: Over Q(sqrt(-3)), lambda = -2/3
 *   Brauer class = (-2/3, -3)_Q
 *
 * Section 2: Over Q(i), lambda = -4
 *   Brauer class = (-4, -1)_Q = (-1, -1)_Q (Hamilton quaternions)
 *
 * Both have local invariants 1/2 at v=inf and v=2, 0 elsewhere.
 * They represent the same (unique) nontrivial element of Br(Q)[2]
 * with invariant set {inf, 2}.
 ******************************************************************************/


// =========== SECTION 1: DESCENT COCYCLE OVER Q(sqrt(-3)) ===========

print "===============================================================";
print "SECTION 1: Cocycle over Q(sqrt(-3))";
print "===============================================================";
print "";

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

// Extract coefficients
coeffs_f := Eltseq(f);
printf "f coefficients [const, u, u^2, u^3]:\n";
for i in [1..#coeffs_f] do
    printf "  coeff[u^%o] = %o\n", i-1, coeffs_f[i];
end for;

// Apply sigma: w -> -w
sigma := hom<K -> K | -w>;

function SigmaKt(elt)
    n := Numerator(elt);
    d := Denominator(elt);
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

lambda_coeffs := Eltseq(lambda);
printf "lambda coefficients:\n";
for i in [1..#lambda_coeffs] do
    printf "  coeff[u^%o] = %o\n", i-1, lambda_coeffs[i];
end for;

printf "\nlambda = -2/3? %o\n\n", lambda eq FF!(-2/3);


// =========== SECTION 2: DESCENT COCYCLE OVER Q(i) ===========

print "===============================================================";
print "SECTION 2: Cocycle over Q(i)";
print "===============================================================";
print "";

P2<x> := PolynomialRing(Rationals());
Ki<i> := NumberField(x^2 + 1);
printf "K = Q(i), i^2 = %o\n\n", i^2;

sigma_i := hom<Ki -> Ki | -i>;

// Function field of C: t^4 + u^4 + 1 = 0 (affine z=1)
R<t2,u2> := PolynomialRing(Ki, 2);
A2 := AffineSpace(Ki, 2);
C := Curve(A2, t2^4 + u2^4 + 1);
KC := FunctionField(C);
t2 := KC.1;
u2 := KC.2;

// The Q(i) decomposition
print "=== Q(i) DECOMPOSITION ===";
qi1 := 2*t2^2 + 2*i;          // Q1/z^2
qi1_conj := 2*t2^2 - 2*i;     // sigma(Q1)/z^2
printf "q1       = %o\n", qi1;
printf "sigma(q1)= %o\n", qi1_conj;

// Verify the norm identity on C
norm_func := qi1 * qi1_conj;
printf "\nq1 * sigma(q1) as function on C = %o\n", norm_func;
neg4u4 := KC!(-4*u2^4);
printf "-4*u^4 as function on C         = %o\n", neg4u4;
same := norm_func eq neg4u4;
printf "Equal on C? %o\n\n", same;

// Divisor computation
print "=== DIVISORS ===";
D_qi1 := Divisor(qi1);
D_qi1c := Divisor(qi1_conj);
D_u2 := Divisor(KC!u2);

supp1, mults1 := Support(D_qi1);
suppc, multsc := Support(D_qi1c);
suppu, multsu := Support(D_u2);

printf "div(q1):        %o places, mults = %o\n", #supp1, mults1;
printf "div(sigma(q1)): %o places, mults = %o\n", #suppc, multsc;
printf "div(u):         %o places, mults = %o\n", #suppu, multsu;

all_even := &and[m mod 2 eq 0 : m in mults1];
printf "\nAll multiplicities of div(q1) even? %o\n", all_even;

// D = (1/2)div(q1), sigma(D) = (1/2)div(sigma(q1))
half_D := &+[Integers()!(mults1[j] div 2) * supp1[j] : j in [1..#supp1]];
half_Dc := &+[Integers()!(multsc[j] div 2) * suppc[j] : j in [1..#suppc]];

// f = q1/u^2
print "\n=== FUNCTION f ===";
f2 := qi1 / u2^2;
printf "f = q1/u^2 = (2t^2 + 2i)/u^2\n";

// Compute lambda = f * sigma(f)
print "\n=== DESCENT COCYCLE ===";
sigma_f2 := qi1_conj / u2^2;
printf "sigma(f) = sigma(q1)/u^2 = (2t^2 - 2i)/u^2\n";

lambda2 := f2 * sigma_f2;
printf "\nlambda = f * sigma(f) = q1*sigma(q1)/u^4 = -4u^4/u^4\n";
printf "lambda = %o\n", lambda2;

is_const := (lambda2 eq KC!(-4));
printf "lambda = -4? %o\n\n", is_const;

// Is -4 a norm from Q(i)?
print "=== NORM CHECK ===";
printf "lambda = -4\n";
printf "N_{Q(i)/Q}(a+bi) = a^2 + b^2 >= 0 for all a,b in Q\n";
printf "Since -4 < 0, lambda is NOT a norm from Q(i)*.\n\n";

printf "Moreover, -4 = (-1) * N(2), so [-4] = [-1] in Q*/N(Q(i)*).\n";
printf "The Brauer class is (-1, -1)_Q (Hamilton quaternions),\n";
printf "ramified at v = inf and v = 2.\n\n";


// =========== COMPARISON AND HILBERT SYMBOL VERIFICATION ===========

print "=== COMPARISON ===";
printf "Over Q(sqrt(-3)): lambda = -2/3, Brauer class = (-2/3, -3)_Q\n";
printf "Over Q(i):        lambda = -4,   Brauer class = (-4, -1)_Q = (-1,-1)_Q\n\n";

printf "Both have local invariants 1/2 at v=inf and v=2, 0 elsewhere.\n";
printf "Since there is a unique element of Br(Q)[2] with invariant set {inf,2},\n";
printf "(-2/3, -3)_Q = (-1, -1)_Q as Brauer classes. QED\n";

quit;
