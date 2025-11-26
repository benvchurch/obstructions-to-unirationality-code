/*******************************************************************************
 * test_jinvariant_cyclotomic.m
 *
 * Purpose:
 *   Compute j-invariants of elliptic curves arising from the cyclotomic field
 *   Q(zeta_7). This relates to understanding elliptic curve factors in
 *   Jacobians of curves with PSL(2,7) symmetry (e.g., the Klein quartic).
 *
 * Method:
 *   1. Define K = Q(w) where w is a root of x^6 + 2x^5 + 4x^4 + 8x^3 + 9x^2 + 4x + 1
 *   2. Verify K is isomorphic to Q(zeta_7)
 *   3. Construct a fractional linear transformation sending roots to 0, 1, infinity
 *   4. Compute the cross-ratio lambda using complex conjugate roots
 *   5. Derive j-invariant from lambda using the classical formula:
 *      j = 2^8 * (1 - s(1-s))^3 / (s^2 * (1-s)^2)
 *      where s depends on lambda
 *
 * Output:
 *   - Verification that K is Q(zeta_7)
 *   - The computed j-invariants and their minimal polynomial over Q(sqrt(7))
 *
 * Related files:
 *   - Klein_quartic.m: Studies the Klein quartic with PSL(2,7) symmetry
 *   - hilbert_modular_forms.m: Hecke eigenvalue data for j-invariant computation
 *
 * Mathematical background:
 *   The j-invariant computation uses the classical relationship between
 *   cross-ratios and elliptic curves. The formula s = (1-lambda)(lambda + sqrt(lambda^2-lambda+1))^2
 *   gives a parametrization related to the curve's Weierstrass form.
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
g := P![1,2,4,8,9,4,1];
K<w> := NumberField(g);
print "Check deg K = 6: ", Degree(K) eq 6;

ZK := RingOfIntegers(K);
print "Discriminant of K: ", Discriminant(ZK);
val, phi := IsIsomorphic(K, CyclotomicField(7));

print "Check K is isomorphic to CyclotomicField(7): ", val;
print "Root of g: ", phi(w);
print "Verify roots of g: ";
Evaluate(g, w), Evaluate(g, 1/(-w-1)), Evaluate(g, -(w+1)/w);

// write down a fractional linear transformation sending these roots to 0,1,inf
a := (1 + w)/(1 + w + w^2);
b := - w * (w+1)/(1 + w + w^2);
c := - w * (1 + w) / (1 + w + w^2);
d := (-1 - w)*(1 + w) / (1 + w + w^2);

trans := function(z)
  if c*z + d eq 0 then
    return Infinity();
  else
    return (a*z + b)/(c*z + d);
  end if;
end function;

print "Verify fractional linear transformation: ";
trans(w), trans(1/(-w-1)), trans(-(w+1)/w);

cw := ComplexConjugate(w);
lambda := trans(cw);

print "Verify the other roots: ";

trans(1/(-cw-1)) eq 1/(1-lambda);
trans((-cw-1)/cw) eq (lambda-1)/lambda;

print "Verify that lambda lies in Q(sqrt(-7)): ", Degree(sub<K | lambda>) eq 2;
print "Verify that lambda^2 - lambda + 1 == -lambda^2: ", lambda^2 - lambda + 1 eq -lambda^2;

K_i<a,b> := ext< K | Polynomial(K, [1, 0, 1]) >;  // x^2 + 1

ell := K_i ! lambda;

s := (1 - ell) * (ell + Sqrt(ell^2 - ell + 1))^2;
j := 2^8 * (1 - s*(1-s))^3 / (s^2 * (1 - s)^2); // j-invariant of the elliptic curve

p := MinimalPolynomial(j);
F := QuadraticField(7);
PF := PolynomialRing(F);

print "The j-invariants are: ", j;
Factorization(PF ! p);
