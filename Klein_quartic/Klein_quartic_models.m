/*******************************************************************************
 * Klein_quartic_models.m
 *
 * Purpose:
 *   Compare three different models of the Klein quartic and study their
 *   mod-2 arithmetic properties (L-polynomials, 2-rank of Jacobian).
 *
 * Models compared:
 *   - C: Classic Klein model x^3*y + y^3*z + z^3*x = 0
 *   - C_twist: Twisted model with more complex equation
 *   - X_0_49: Modular curve X_0(49) model
 *
 * Computations:
 *   - L-polynomial mod 2 at various primes
 *   - Kronecker symbols for -7 and -3
 *   - 2-rank of Jacobian Sylow-2 subgroup over F_p
 *   - Invariant structure of J(F_p)[2]
 *
 * Functions:
 *   - Lpoly_mod2(C, p): Compute L-polynomial mod 2 at prime p
 *   - TwoRankJacobian(C, p): Compute 2-rank of Jacobian over F_p
 *
 * Dependencies:
 *   None (standalone computation)
 *
 * Mathematical background:
 *   The Klein quartic has Jacobian isogenous to E^3 where E has CM by
 *   Q(sqrt(-7)). This affects the L-polynomial and torsion structure.
 ******************************************************************************/

Q := Rationals();
P2<x,y,z> := ProjectiveSpace(Q, 2);
C := Curve(P2, x^3*y + y^3 * z + z^3 * x); // Klein model
C_twist := Curve(P2, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3) - 3 * (x^2 *y^2 + y^2 * z^2 + z^2 * x^2) + 3 *x*y*z*(x+y+z)); // twisted model
X_0_49 := Curve(P2, y^2*z + x*y*z - x^3 + x^2 * z + 2 * x * z^2 + z^3); // X_0(49) model
//C := Curve(P2, y^2*z + x*y*z - x^3 + x^2 * z + 2 * x * z^2 + z^3); // X_0(49)
K<x> := PolynomialRing(Integers());

function Lpoly_mod2(C, p)
  Cp := ChangeRing(C, GF(p));
  Z := ZetaFunction(Cp);
  L := Numerator(Z);
  return ChangeRing(L, GF(2));
end function;


function TwoRankJacobian(C, p)
    Fp := GF(p);
    Cp := ChangeRing(C, Fp);
    Cl, mp := ClassGroup(Cp);      // Pic^0(F_p) via divisor class group
    Syl2 := SylowSubgroup(Cl, 2);

    inv := Invariants(Syl2);       // [2^a1, 2^a2, ...]
    // 2-torsion rank = number of invariant factors (each contributes one F2 generator to Syl2[2])
    return #inv, inv;
end function;


for p in [5,11,13,17,19,23,29,31,37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] do
  print "p = ", p, "KroneckerSymbol(-7, p): ", KroneckerSymbol(-7, p), "KroneckerSymbol(-3, p): ", KroneckerSymbol(-3, p);
  print "mod-2 L-polynomial of C: ", Lpoly_mod2(C, p);
  print "mod-2 L-polynomial of C_twist: ", Lpoly_mod2(C_twist, p);
  print "mod-2 L-polynomial of X_0_49: ", Lpoly_mod2(X_0_49, p);
  r, inv := TwoRankJacobian(C, p);
  printf "C: 2-rank(J(F_p)[2])=%o  inv=%o\n", r, inv;
  r, inv := TwoRankJacobian(C_twist, p);
  printf "C_twist: 2-rank(J(F_p)[2])=%o  inv=%o\n", r, inv;
  r, inv := TwoRankJacobian(X_0_49, p);
  printf "X_0_49: 2-rank(J(F_p)[2])=%o  inv=%o\n", r, inv;
end for;

F2 := GF(2);
S<U> := PolynomialRing(F2);
print "target=", (1+U)^2;
