/*******************************************************************************
 * conic_residue.m
 *
 * For a decomposition F = Q1*Q3 - Q2^2, restricting to Q1=0 gives F = -Q2^2.
 * So -F must be a perfect square on the conic Q1=0.
 * This constrains which field Q2 lives over.
 *
 * Check this for several Q1's giving different J[2] classes.
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2+1);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

printf "=== CONIC RESIDUE ANALYSIS ===\n";
printf "On Q1=0: F+Q2^2 = Q1*Q3 => F = -Q2^2\n";
printf "So -F|_{Q1=0} must be a perfect square in k[vars]/Q1\n\n";

// =========================================================================
// 1. eta via Q(i): Q1 = 2X^2 + 2iZ^2
// =========================================================================
printf "--- Q1 = 2X^2 + 2iZ^2 (gives eta) ---\n";
printf "On Q1=0: X^2 = -iZ^2, so X^4 = -Z^4\n";
printf "F|_{Q1=0} = -Z^4+Y^4+Z^4 = Y^4\n";
printf "Need: Q2^2 = -Y^4,  so Q2 = i*Y^2\n";
printf "=> Q2 = iY^2 is in Q(i)[X,Y,Z].  WORKS OVER Q(i). ✓\n\n";

// Verify explicitly
Q1 := 2*X^2 + 2*i*Z^2;
Q2 := i*Y^2;
G := FK + Q2^2;  // Should be divisible by Q1
printf "F + Q2^2 = %o\n", G;
Q3 := G div Q1;
printf "Q3 = (F+Q2^2)/Q1 = %o\n", Q3;
printf "Verify F = Q1*Q3-Q2^2: %o\n\n", Q1*Q3 - Q2^2 eq FK;

// =========================================================================
// 2. V_rat via bitangent product: Q1 = (X+Y+Z)(X+Y-Z) = (X+Y)^2-Z^2
// =========================================================================
printf "--- Q1 = (X+Y)^2-Z^2 (bitangent product, gives v2) ---\n";
printf "On Q1=0: Z^2=(X+Y)^2, so Z^4=(X+Y)^4\n";
printf "F|_{Q1=0} = X^4+Y^4+(X+Y)^4 = 2(X^2+XY+Y^2)^2\n";
printf "Need: Q2^2 = -2(X^2+XY+Y^2)^2\n";
printf "So Q2 = sqrt(-2)*(X^2+XY+Y^2) = i*sqrt(2)*(X^2+XY+Y^2)\n";
printf "=> sqrt(2) not in Q(i)!  FAILS OVER Q(i).\n";
printf "=> WORKS OVER Q(sqrt(-2)) or Q(zeta_8) = Q(i,sqrt(2)).\n\n";

// =========================================================================
// 3. v1: try Q1 = X^2+iY^2+Z^2 (gave v1 over F_73)
// =========================================================================
printf "--- Q1 = X^2+iY^2+Z^2 (gives v1 over F_73) ---\n";
printf "On Q1=0: X^2 = -iY^2-Z^2, X^4 = (iY^2+Z^2)^2 = -Y^4+2iY^2Z^2+Z^4\n";
printf "F|_{Q1=0} = (-Y^4+2iY^2Z^2+Z^4)+Y^4+Z^4 = 2Z^4+2iY^2Z^2 = 2Z^2(Z^2+iY^2)\n";
printf "On Q1=0: Z^2+iY^2 = -X^2, so F = 2Z^2*(-X^2) = -2X^2Z^2\n";
printf "Need: Q2^2 = 2X^2Z^2 = (sqrt(2)*XZ)^2\n";
printf "=> Q2 = sqrt(2)*XZ.  Needs sqrt(2) not in Q(i).  FAILS OVER Q(i).\n\n";

// =========================================================================
// 4. eta+v1: try Q1 = X^2+iY^2-Z^2 (gave eta+v1 over F_73)
// =========================================================================
printf "--- Q1 = X^2+iY^2-Z^2 (gives eta+v1 over F_73) ---\n";
printf "On Q1=0: X^2 = Z^2-iY^2, X^4 = (Z^2-iY^2)^2 = Z^4-2iY^2Z^2-Y^4\n";
printf "F|_{Q1=0} = Z^4-2iY^2Z^2-Y^4+Y^4+Z^4 = 2Z^4-2iY^2Z^2 = 2Z^2(Z^2-iY^2)\n";
printf "On Q1=0: Z^2-iY^2 = X^2, so F = 2X^2Z^2\n";
printf "Need: Q2^2 = -2X^2Z^2 = (i*sqrt(2)*XZ)^2.  Needs sqrt(2).  FAILS.\n\n";

// =========================================================================
// 5. Check: Q(sqrt(-3)) decomposition (eta)
// =========================================================================
printf "--- Q1 = 2X^2+(1-w)Y^2+(1+w)Z^2, w=sqrt(-3) (gives eta) ---\n";
printf "On Q1=0: F = ((1-w)/2)Y^4 + 2Y^2Z^2 + ((1+w)/2)Z^4\n";
printf "Key: (1-w)/2 = -zeta_3, and sqrt(-zeta_3) = zeta_6 = (1+w)/2 in Q(w)!\n";
printf "So F|_{Q1=0} = (zeta_6*Y^2 - zeta_6bar*Z^2)^2  [using zeta_6*zeta_6bar=1]\n";
printf "Q2 = ±i*(zeta_6*Y^2 - zeta_6bar*Z^2)... but need i*zeta_6.\n";
printf "Actually Q2 just needs to satisfy Q2^2 = -F:\n";
printf "  -F|_{Q1=0} = -(zeta_6*Y^2-zeta_6bar*Z^2)^2\n";
printf "  This needs a square root of -1, i.e. i... but i not in Q(sqrt(-3))!\n";
printf "  Wait: directly compute Q2 from the decomposition search.\n\n";

// =========================================================================
// 6. Actually verify which Q2 works for the Q(sqrt(-3)) decomposition
// =========================================================================
printf "--- DIRECT: find Q2 for Q(sqrt(-3)) decomposition ---\n";
P2<y> := PolynomialRing(Rationals());
L<w> := NumberField(y^2+3);
RL<X,Y,Z> := PolynomialRing(L, 3);
FL := X^4 + Y^4 + Z^4;
Q1L := 2*X^2 + (1-w)*Y^2 + (1+w)*Z^2;

// Search for Q2 with small coefficients in Q(sqrt(-3))
bnd := 2;
printf "Searching Q2 over Q(sqrt(-3)), coefficient bound %o...\n", bnd;
found := false;
for a1 in [-bnd..bnd] do for b1 in [-bnd..bnd] do
for a2 in [-bnd..bnd] do for b2 in [-bnd..bnd] do
for a3 in [-bnd..bnd] do for b3 in [-bnd..bnd] do
for a4 in [-bnd..bnd] do for b4 in [-bnd..bnd] do
for a5 in [-bnd..bnd] do for b5 in [-bnd..bnd] do
for a6 in [-bnd..bnd] do for b6 in [-bnd..bnd] do
    c1 := a1+b1*w; c2 := a2+b2*w; c3 := a3+b3*w;
    c4 := a4+b4*w; c5 := a5+b5*w; c6 := a6+b6*w;
    Q2L := c1*X^2 + c2*Y^2 + c3*Z^2 + c4*X*Y + c5*X*Z + c6*Y*Z;
    if Q2L eq 0 then continue; end if;
    GL := FL + Q2L^2;
    if GL mod Q1L eq 0 then
        Q3L := GL div Q1L;
        if TotalDegree(Q3L) eq 2 then
            printf "FOUND: Q2 = %o\n", Q2L;
            printf "  Q3 = %o\n", Q3L;
            printf "  Verify: %o\n", Q1L*Q3L - Q2L^2 eq FL;
            found := true;
            break a1;
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
if not found then
    printf "No Q(sqrt(-3)) decomposition with bound %o\n", bnd;
end if;

printf "\n";

// =========================================================================
// 7. Summary
// =========================================================================
printf "=== SUMMARY ===\n\n";
printf "The J[2] class from a decomposition F=Q1Q3-Q2^2 is determined by Q1.\n";
printf "The field of definition of Q2 depends on F|_{Q1=0}:\n\n";
printf "  Class     | F|_{Q1=0}              | Q2 needs          | Min field\n";
printf "  ----------|------------------------|-------------------|----------\n";
printf "  eta       | Y^4 (perfect 4th power)| Q2 = iY^2        | Q(i)\n";
printf "  V_rat     | 2(quadratic)^2         | Q2 = sqrt(-2)*..  | Q(sqrt(-2))\n";
printf "  eta+V_rat | 2X^2Z^2               | Q2 = i*sqrt(2)*XZ | Q(zeta_8)\n\n";
printf "Over Q(i): only eta is accessible (have i, no sqrt(2)).\n";
printf "Over Q(sqrt(-2)): only V_rat classes (have sqrt(-2), no i for eta).\n";
printf "Over Q(zeta_8)=Q(i,sqrt(2)): all classes accessible.\n";

quit;
