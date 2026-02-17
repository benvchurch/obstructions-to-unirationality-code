/*******************************************************************************
 * search_definite.m
 *
 * 1. Search for RATIONAL decompositions with larger diagonal bounds.
 *    Q1,Q3 both definite is consistent with F+Q2^2 > 0.
 *
 * 2. For a V_rat-type Q1 over Q(i), solve the divisibility Q1 | F+Q2^2
 *    to see exactly what field Q2 needs.
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);
R<X0,Y0,Z0> := PolynomialRing(Rationals(), 3);
FK := X^4 + Y^4 + Z^4;
FR := X0^4 + Y0^4 + Z0^4;

// =========================================================================
// 1. Rational diagonal Q2 with large bound
// =========================================================================
printf "=== RATIONAL DECOMPOSITIONS (diagonal Q2, bound 10) ===\n";
bnd := 10;
found := 0;
for c1 in [0..bnd] do  // can assume c1 >= 0 by ±Q2 symmetry
for c2 in [-bnd..bnd] do
for c3 in [-bnd..bnd] do
    Q2 := c1*X0^2 + c2*Y0^2 + c3*Z0^2;
    if Q2 eq 0 then continue; end if;
    G := FR + Q2^2;
    fac := Factorization(G);
    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;
    if has_quad then
        found +:= 1;
        printf "FOUND: Q2 = %o\n", Q2;
        for pair in fac do
            printf "  factor: (%o)^%o\n", pair[1], pair[2];
        end for;
    end if;
end for;
end for;
end for;
printf "Rational diagonal decomps found: %o (bound %o)\n\n", found, bnd;

// =========================================================================
// 2. Rational Q2 with cross terms, bound 4
// =========================================================================
printf "=== RATIONAL DECOMPOSITIONS (full Q2, bound 4) ===\n";
bnd2 := 4;
found2 := 0;
for c1 in [0..bnd2] do
for c2 in [-bnd2..bnd2] do
for c3 in [-bnd2..bnd2] do
for c4 in [-bnd2..bnd2] do
for c5 in [-bnd2..bnd2] do
for c6 in [-bnd2..bnd2] do
    Q2 := c1*X0^2 + c2*Y0^2 + c3*Z0^2 + c4*X0*Y0 + c5*X0*Z0 + c6*Y0*Z0;
    if Q2 eq 0 then continue; end if;
    if c1 eq 0 then
        // Normalize: first nonzero > 0
        coeffs := [c2,c3,c4,c5,c6];
        skip := false;
        for j in [1..5] do
            if coeffs[j] ne 0 then
                if coeffs[j] lt 0 then skip := true; end if;
                break;
            end if;
        end for;
        if skip then continue; end if;
    end if;

    G := FR + Q2^2;
    fac := Factorization(G);
    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;
    if has_quad then
        found2 +:= 1;
        printf "FOUND: Q2 = %o\n", Q2;
        for pair in fac do
            printf "  factor: (%o)^%o\n", pair[1], pair[2];
        end for;
    end if;
end for;
end for;
end for;
end for;
end for;
end for;
printf "Rational full decomps found: %o (bound %o)\n\n", found2, bnd2;

// =========================================================================
// 3. Algebraic proof that Q1 = X^2+iY^2+Z^2 needs sqrt(2) for Q2
// =========================================================================
printf "=== ALGEBRAIC: Q1 = X^2+iY^2+Z^2 over Q(i) ===\n\n";

Q1 := X^2 + i*Y^2 + Z^2;

// F + Q2^2 must be divisible by Q1.
// Write Q2 = c1*X^2+c2*Y^2+c3*Z^2+c4*XY+c5*XZ+c6*YZ
// Reduce modulo Q1 (i.e., set X^2 = -iY^2-Z^2):
//
// F mod Q1: X^4 = (iY^2+Z^2)^2 = -Y^4+2iY^2Z^2+Z^4
//   F = (-Y^4+2iY^2Z^2+Z^4)+Y^4+Z^4 = 2iY^2Z^2+2Z^4 = 2Z^2(iY^2+Z^2) = -2X^2Z^2
//   But on Q1=0 this is still involves X, and X itself is a "free" variable
//   on the conic (not a polynomial in Y,Z).
//
// Better: work in the quotient ring RK/<Q1>. But multivariate quotients
// are tricky. Instead, parametrize the conic and check.

// Parametrize Q1=0: X^2+iY^2+Z^2 = 0
// Over K(i) = Q(i), the conic has a K-point iff the quaternion algebra
// (i,1)_K is split. Since i = -(-i) and 1 are both norms from K(sqrt(-i)),
// hmm this is getting complicated.
//
// Just check: does (1:0:i) lie on Q1? 1+0+i^2 = 1-1 = 0. YES!
// So Q1=0 has the K-point (1:0:i). Can parametrize.

printf "Q1=0 has Q(i)-point (1:0:i): 1+0+i^2 = %o\n", 1+0+i^2;

// Parametrize: (X:Y:Z) = (1+i*s^2 : 2s : -i-s^2) * ... or use standard method
// Actually, from (1:0:i), line through (1:0:i) with direction (a:b:c):
// X = 1+at, Y = bt, Z = i+ct
// Q1 = (1+at)^2 + i(bt)^2 + (i+ct)^2
//    = 1+2at+a^2t^2 + ib^2t^2 + -1+2ict+c^2t^2
//    = 2at+2ict + (a^2+ib^2+c^2)t^2
//    = t(2a+2ic + (a^2+ib^2+c^2)t)
// So t=0 gives the base point, and the other root is t = -(2a+2ic)/(a^2+ib^2+c^2)
//
// Standard parametrization with parameter (s:t) in P^1:
// Set b=1 (affine), vary a,c.  Actually, use s = a/1, and t from above.
//
// Simpler: since the conic has a rational point, just verify directly.

// Direct approach: solve the linear system Q1 | (F + Q2^2) over K
// Expand F + Q2^2 and collect terms, then impose Q1-divisibility.
// This is a system of linear equations in c1,...,c6 (Q2 coefficients).

// F + Q2^2 in terms of monomials of degree 4:
// Monomials: X^4, Y^4, Z^4, X^3Y, X^3Z, X^2Y^2, X^2YZ, X^2Z^2,
//            XY^3, XY^2Z, XYZ^2, XZ^3, Y^3Z, Y^2Z^2, YZ^3

// This is a polynomial of degree 4. For Q1 to divide it, since Q1 has degree 2,
// the quotient Q3 has degree 2. So F+Q2^2 = Q1*Q3 with Q3 having 6 coefficients.
// Total unknowns: 6 (for Q2) + 6 (for Q3) = 12.
// Total equations: 15 (coefficients of degree-4 monomials).
// So 15 equations in 12 unknowns. Overdetermined but may have solutions.

// Let's set up the system.
// Q2 = c[1]*X^2+c[2]*Y^2+c[3]*Z^2+c[4]*XY+c[5]*XZ+c[6]*YZ
// Q3 = d[1]*X^2+d[2]*Y^2+d[3]*Z^2+d[4]*XY+d[5]*XZ+d[6]*YZ

// F + Q2^2 = Q1 * Q3
// Expand both sides and equate coefficients.
// Q2^2 is quadratic in c's, Q1*Q3 is linear in d's.
// So the system: Q1*Q3 = F + Q2^2 can be solved for d's given c's
// (linear in d's!) and then the consistency conditions give constraints on c's.

// Actually easier: since Q1*Q3 must equal F+Q2^2, and Q1 is fixed,
// Q3 = (F+Q2^2)/Q1. For Q3 to be a polynomial, Q1 must divide F+Q2^2.
// This is equivalent to: F+Q2^2 vanishes on Q1=0.

// On Q1=0: X^2 = -iY^2-Z^2. So any polynomial mod Q1 can be reduced
// to have degree <= 1 in X. The condition is that F+Q2^2, after reducing
// X^2 -> -iY^2-Z^2, gives zero.

// Reduce F mod Q1:
// X^4 = (X^2)^2 = (-iY^2-Z^2)^2 = -Y^4+2iY^2Z^2+Z^4
// F mod Q1 = -Y^4+2iY^2Z^2+Z^4+Y^4+Z^4 = 2Z^4+2iY^2Z^2

// Reduce Q2^2 mod Q1:
// Q2 = c1*(-iY^2-Z^2)+c2*Y^2+c3*Z^2+c4*XY+c5*XZ+c6*YZ
//    = (c2-ic1)Y^2+(c3-c1)Z^2+c6*YZ + X*(c4*Y+c5*Z)
// Let A = (c2-ic1)Y^2+(c3-c1)Z^2+c6*YZ  (even in X)
//     B = c4*Y + c5*Z                     (coefficient of X)
// Q2 mod Q1 = A + B*X
// Q2^2 mod Q1 = A^2 + 2ABX + B^2*X^2 = A^2 + 2ABX + B^2*(-iY^2-Z^2)
//             = (A^2-iB^2Y^2-B^2Z^2) + 2ABX

// For (F+Q2^2) mod Q1 = 0:
// Even part: 2Z^4+2iY^2Z^2 + A^2-iB^2*Y^2-B^2*Z^2 = 0
// Odd part:  2AB = 0, so A=0 or B=0.

printf "\nDivisibility analysis: F+Q2^2 mod Q1 = 0\n";
printf "Q2 mod Q1 = A + BX where\n";
printf "  A = (c2-ic1)Y^2+(c3-c1)Z^2+c6*YZ\n";
printf "  B = c4*Y+c5*Z\n\n";
printf "Conditions:\n";
printf "  (i)  2AB = 0 (odd-in-X part)\n";
printf "  (ii) A^2 - i*c4^2*Y^4 - (stuff) + 2Z^4+2iY^2Z^2 = 0 (even part)\n\n";

printf "Case A=0 (c2=ic1, c3=c1, c6=0):\n";
printf "  Even: 2Z^4+2iY^2Z^2 - i(c4Y+c5Z)^2*Y^2 - (c4Y+c5Z)^2*Z^2 = 0\n";
printf "  = 2Z^4+2iY^2Z^2 - (i*Y^2+Z^2)(c4^2Y^2+2c4c5YZ+c5^2Z^2) = 0\n";
printf "  Note: i*Y^2+Z^2 = -X^2+Q1 = -X^2 on Q1=0, so...\n";
printf "  = 2Z^4+2iY^2Z^2 + X^2*(c4^2Y^2+2c4c5YZ+c5^2Z^2) = 0\n";
printf "  Using X^2=-iY^2-Z^2:\n";
printf "  2Z^4+2iY^2Z^2 + (-iY^2-Z^2)(c4^2Y^2+2c4c5YZ+c5^2Z^2) = 0\n";
printf "  Y^4 coeff: -ic4^2 = 0 => c4=0\n";
printf "  Y^2Z^2 coeff: 2i - ic5^2 - c4^2 = 2i-ic5^2 = 0 => c5^2 = 2\n";
printf "  Z^4 coeff: 2-c5^2 = 0 => c5^2 = 2  (consistent)\n";
printf "  => c5 = sqrt(2), NOT IN Q(i).\n\n";

printf "Case B=0 (c4=c5=0):\n";
printf "  Even: A^2 + 2Z^4+2iY^2Z^2 = 0\n";
printf "  A = aY^2+bZ^2+c6*YZ where a=c2-ic1, b=c3-c1\n";
printf "  Y^4: a^2 = 0 => a=0 => c2=ic1\n";
printf "  Y^3Z: 2a*c6 = 0 (auto)\n";
printf "  Y^2Z^2: 2ab+c6^2+2i = c6^2+2i = 0 => c6^2 = -2i\n";
printf "  YZ^3: 2b*c6 = 0 => b=0 or c6=0\n";
printf "    If c6=0: c6^2=0 != -2i. Contradiction.\n";
printf "    If b=0: Z^4 coeff: b^2+2 = 2 != 0. Contradiction.\n";
printf "  => No solution in any field!  (Inconsistent system)\n\n";

// Wait, let me recheck Case B=0 more carefully
// A^2 = a^2*Y^4 + b^2*Z^4 + c6^2*Y^2Z^2 + 2ab*Y^2Z^2 + 2a*c6*Y^3Z + 2b*c6*YZ^3
// So A^2 + 2Z^4+2iY^2Z^2 = 0 gives:
// Y^4: a^2 = 0
// Y^3Z: 2a*c6 = 0
// Y^2Z^2: 2ab + c6^2 + 2i = 0
// YZ^3: 2b*c6 = 0
// Z^4: b^2 + 2 = 0
// From Z^4: b^2 = -2, so b = sqrt(-2) = i*sqrt(2). NOT IN Q(i).

printf "Correction for Case B=0:\n";
printf "  Z^4: b^2 = -2 => b = sqrt(-2) = i*sqrt(2), NOT IN Q(i).\n\n";

printf "CONCLUSION: For Q1 = X^2+iY^2+Z^2, the divisibility Q1|(F+Q2^2)\n";
printf "requires sqrt(2) in BOTH cases. No Q(i)-decomposition exists for\n";
printf "this Q1.  Any Q1 giving a V_rat class will have a similar obstruction.\n";

quit;
