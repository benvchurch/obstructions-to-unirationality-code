/*******************************************************************************
 * phantom_cocycle.m
 *
 * Compute the descent cocycle lambda = f * sigma(f) for the phantom quartic.
 *
 * C: 3x^4+4x^3+7x^2y^2-2x^2y+5x^2+2xy^2+2x+y^4+y^2+1 = 0  (affine z=1)
 *
 * Over K = Q(sqrt(-3)):
 *   Q1 = 2x^2+x+y^2+1 + w*xy    (w = sqrt(-3))
 *   Q3 = 2x^2+x+y^2+1 - w*xy
 *   Q2 = x^2+y
 *   On C: Q1*Q3 = Q2^2
 ******************************************************************************/

P<a> := PolynomialRing(Rationals());
K<w> := NumberField(a^2 + 3);  // w = sqrt(-3)

// Function field of C over K
// f(x,y,1) as polynomial in y over K(x):
// y^4 + (7x^2+2x+1)*y^2 + (-2x^2)*y + (3x^4+4x^3+5x^2+2x+1)
Kx<x> := FunctionField(K);
Kxy<y> := PolynomialRing(Kx);

fpoly := y^4 + (7*x^2+2*x+1)*y^2 + (-2*x^2)*y + (3*x^4+4*x^3+5*x^2+2*x+1);
printf "f(x,y,1) = %o\n\n", fpoly;

FF<yy> := FunctionField(fpoly);
elt_x := FF ! x;
elt_y := yy;

// q1 and q3 in function field
q1 := 2*elt_x^2 + elt_x + elt_y^2 + 1 + w*elt_x*elt_y;
q3 := 2*elt_x^2 + elt_x + elt_y^2 + 1 - w*elt_x*elt_y;
q2 := elt_x^2 + elt_y;

printf "q1 * q3 = q2^2 on C? %o\n\n", q1*q3 eq q2^2;

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

printf "Computing divisors...\n";
D_q1 := Divisor(q1);
D_q3 := Divisor(q3);

printf "div(q1):\n";
for pl in Support(D_q1) do
    printf "  deg-%o place, mult %o\n", Degree(pl), Valuation(D_q1, pl);
end for;

printf "\ndiv(q3):\n";
for pl in Support(D_q3) do
    printf "  deg-%o place, mult %o\n", Degree(pl), Valuation(D_q3, pl);
end for;

ok1, D_half1 := HalfDiv(D_q1);
ok2, D_half3 := HalfDiv(D_q3);
printf "\ndiv(q1) all even? %o\n", ok1;
printf "div(q3) all even? %o\n", ok2;

if ok1 and ok2 then
    ddiff := D_half1 - D_half3;
    printf "\n(1/2)div(q1) - (1/2)div(q3):\n";
    for pl in Support(ddiff) do
        v := Valuation(ddiff, pl);
        if v ne 0 then printf "  deg-%o place, mult %o\n", Degree(pl), v; end if;
    end for;
    printf "Degree: %o\n", Degree(ddiff);

    // Find f with div(f) = (1/2)div(q1) - (1/2)div(q3)
    V, phi := RiemannRochSpace(-ddiff);
    printf "\ndim L(sigma(D) - D) = %o\n", Dimension(V);
    if Dimension(V) ge 1 then
        fn := phi(V.1);
        printf "f = %o\n\n", fn;

        // Apply sigma: w -> -w
        sigma := hom<K -> K | -w>;

        function SigmaKx(elt)
            n := Numerator(elt);
            d := Denominator(elt);
            Kpol := Parent(n);
            sigma_n := Kpol ! [sigma(Coefficient(n, i)) : i in [0..Degree(n)]];
            sigma_d := Kpol ! [sigma(Coefficient(d, i)) : i in [0..Degree(d)]];
            return Parent(elt) ! (sigma_n / sigma_d);
        end function;

        coeffs_fn := Eltseq(fn);
        printf "f coefficients [const, y, y^2, y^3]:\n";
        for i in [1..#coeffs_fn] do
            printf "  coeff[y^%o] = %o\n", i-1, coeffs_fn[i];
        end for;

        sigma_coeffs := [SigmaKx(c) : c in coeffs_fn];
        printf "\nsigma(f) coefficients:\n";
        for i in [1..#sigma_coeffs] do
            printf "  coeff[y^%o] = %o\n", i-1, sigma_coeffs[i];
        end for;

        sigma_fn := &+[FF ! sigma_coeffs[i] * elt_y^(i-1) : i in [1..#sigma_coeffs]];

        lambda := fn * sigma_fn;
        printf "\nlambda = f * sigma(f) = %o\n\n", lambda;

        // Check if lambda is constant
        lambda_coeffs := Eltseq(lambda);
        printf "lambda coefficients:\n";
        for i in [1..#lambda_coeffs] do
            printf "  coeff[y^%o] = %o\n", i-1, lambda_coeffs[i];
        end for;

        // Check norm condition
        if #lambda_coeffs eq 1 and lambda_coeffs[1] in Rationals() then
            lam := Rationals() ! lambda_coeffs[1];
            printf "\nlambda = %o (rational constant)\n", lam;
            if lam lt 0 then
                printf "lambda < 0, so NOT a norm from Q(sqrt(-3))\n";
                printf "=> BRAUER OBSTRUCTION IS NONZERO\n";
                printf "=> eta is PHANTOM 2-torsion\n";
            else
                printf "lambda >= 0, need to check if it's a norm from Q(sqrt(-3))\n";
                printf "lambda is a norm iff it's a sum a^2 + 3b^2 for a,b in Q\n";
            end if;
        else
            printf "\nlambda is NOT a constant - something is wrong\n";
        end if;
    end if;
end if;

printf "\nDone.\n";
quit;
