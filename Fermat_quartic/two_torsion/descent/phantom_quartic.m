// Verify candidate #8 from phantom search:
// A = 2x^2+xz+y^2+z^2, B = xy, Q2 = x^2+yz
// f = A^2 + 3*B^2 - Q2^2
//   = 3x^4 + 4x^3z + 7x^2y^2 - 2x^2yz + 5x^2z^2 + 2xy^2z + 2xz^3
//     + y^4 + y^2z^2 + z^4

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);

A := 2*x^2 + x*z + y^2 + z^2;
B := x*y;
Q2 := x^2 + y*z;

f := A^2 + 3*B^2 - Q2^2;
printf "f = %o\n\n", f;

// Verify the decomposition
Q1 := A + B;  // over Q(sqrt(-3)), this would be A + sqrt(-3)*B
Q3 := A - B;
printf "Check: A^2+3*B^2-Q2^2 = %o\n", A^2 + 3*B^2 - Q2^2 eq f;
printf "A = %o\nB = %o\nQ2 = %o\n\n", A, B, Q2;

// === 1. Basic properties ===
P2<X,Y,Z> := ProjectiveSpace(Q, 2);
C := Curve(P2, Evaluate(f, [X, Y, Z]));
printf "Smooth: %o\n", IsNonsingular(C);
printf "Genus: %o\n", Genus(C);
printf "Irreducible: %o\n\n", IsIrreducible(C);

// === 2. Positive definiteness (fine grid) ===
R := RealField(20);
pi := Pi(R);
min_val := R!100;
min_pt := [R|0,0,1];
N := 150;
for i := 0 to N do
    phi := pi * R!i / R!N;
    sp := Sin(phi); cp := Cos(phi);
    for j := 0 to 2*N-1 do
        theta := 2*pi*R!j / (2*R!N);
        xv := sp*Cos(theta); yv := sp*Sin(theta); zv := cp;
        val := Evaluate(f, [xv, yv, zv]);
        if val lt min_val then
            min_val := val;
            min_pt := [xv, yv, zv];
        end if;
    end for;
end for;
printf "Min on sphere (N=%o): %o\n", N, min_val;
printf "  at (%o, %o, %o)\n", min_pt[1], min_pt[2], min_pt[3];
printf "Positive definite: %o\n\n", min_val gt 0;

// === 3. Geometric automorphisms at many primes ===
printf "Geometric automorphisms:\n";
all_aut1 := true;
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "  p=%o: bad reduction\n", p;
        continue;
    end if;
    Ap := AutomorphismGroup(Cp);
    printf "  p=%o: |Aut|=%o\n", p, #Ap;
    if #Ap ne 1 then all_aut1 := false; end if;
end for;
printf "All |Aut|=1: %o\n\n", all_aut1;

// === 4. L-polynomial and #J(F_p) ===
printf "L-polynomial data:\n";
all_even := true;
min_v2 := 100;
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then continue; end if;

    n1 := #RationalPoints(Cp);
    Cp2 := BaseChange(Cp, GF(p^2));
    n2 := #RationalPoints(Cp2);
    Cp3 := BaseChange(Cp, GF(p^3));
    n3 := #RationalPoints(Cp3);

    a1 := p + 1 - n1;
    a2 := (a1^2 - (p^2 + 1 - n2)) div 2;
    a3 := (a1^3 - 3*a1*a2 - (p^3 + 1 - n3)) div 3;
    Jp := 1 + a1 + a2 + a3 + p*a2 + p^2*a1 + p^3;
    v2 := Valuation(Jp, 2);
    printf "  p=%o: #C=%o, L=[1,%o,%o,%o], #J=%o, v2=%o\n",
        p, n1, a1, a2, a3, Jp, v2;
    if v2 eq 0 then all_even := false; end if;
    if v2 lt min_v2 then min_v2 := v2; end if;
end for;
printf "All #J even: %o, min v2 = %o\n\n", all_even, min_v2;

// === 5. Search for rational bitangent lines ===
// A bitangent line aX+bY+cZ=0 satisfies: f restricted to the line is a perfect square.
// Search: for each (a:b:c) in P^2(Q) with small coefficients, check if f|_{line} = g^2.
printf "Searching for rational bitangent lines:\n";
bt_count := 0;
Qu<u> := PolynomialRing(Q);
bound := 5;
for a := -bound to bound do
for b := -bound to bound do
for c := -bound to bound do
    if a eq 0 and b eq 0 and c eq 0 then continue; end if;
    // Normalize: first nonzero coeff positive
    first := 0;
    if a ne 0 then first := a; elif b ne 0 then first := b; else first := c; end if;
    if first lt 0 then continue; end if;
    // GCD normalize
    g := GCD(GCD(Abs(a), Abs(b)), Abs(c));
    if g ne 1 then continue; end if;

    // Parametrize the line aX+bY+cZ = 0
    // Choose parametrization based on which coeff is nonzero
    if c ne 0 then
        // Z = -(a*u+b*v)/c, set v=1
        fu := Evaluate(f, [u, Q!1, Q!(-a)/Q!(c)*u + Q!(-b)/Q!(c)]);
    elif b ne 0 then
        fu := Evaluate(f, [u, Q!(-a)/Q!(b)*u + Q!(-c)/Q!(b), Q!1]);
    else
        fu := Evaluate(f, [Q!(-b)/Q!(a) + Q!(-c)/Q!(a)*u, u, Q!1]);
    end if;

    if Degree(fu) ne 4 then continue; end if;

    // Check if fu is a perfect square
    disc := Discriminant(fu);
    if disc eq 0 then
        // Might have a repeated factor
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then
            bt_count +:= 1;
            printf "  Bitangent: %o*X + %o*Y + %o*Z = 0\n", a, b, c;
            printf "    f|_line = %o\n", fu;
        end if;
    end if;
end for; end for; end for;
printf "Total rational bitangent lines found (|coeff| <= %o): %o\n\n", bound, bt_count;

// === 6. Check if decomposition f = Q1*Q3 - Q2^2 exists over Q ===
// Over Q(sqrt(-3)): Q1 = A + sqrt(-3)*B, Q3 = A - sqrt(-3)*B
// Over Q: we'd need Q1, Q3 conjugate quadrics over Q
// The decomposition f = Q1*Q3 - Q2^2 over Q means Q1, Q3, Q2 all have Q-coefficients
// Check: can we write f = q1*q3 - q2^2 with q1,q3,q2 quadrics over Q?
// Parametrize q1 = sum a_ij x_i x_j, q2 = sum b_ij x_i x_j, q3 = sum c_ij x_i x_j
// f = q1*q3 - q2^2 gives quadratic equations in the a,b,c coefficients.
// This is a large system; instead check mod p.
printf "Checking if decomposition exists over Q (via mod-p tests):\n";
for p in [5, 7, 11, 13] do
    Fp := GF(p);
    P3<a1,a2,a3,a4,a5,a6, b1,b2,b3,b4,b5,b6, c1,c2,c3,c4,c5,c6> := PolynomialRing(Fp, 18);
    // q1 = a1*x^2+a2*y^2+a3*z^2+a4*xy+a5*xz+a6*yz
    // q2 = b1*x^2+b2*y^2+b3*z^2+b4*xy+b5*xz+b6*yz
    // q3 = c1*x^2+c2*y^2+c3*z^2+c4*xy+c5*xz+c6*yz
    // f = q1*q3 - q2^2

    // Coefficient of x^4: a1*c1 - b1^2 = 3
    // Coefficient of y^4: a2*c2 - b2^2 = 1
    // Coefficient of z^4: a3*c3 - b3^2 = 1
    // Coefficient of x^2*y^2: a1*c2+a2*c1+a4*c4 - 2*b1*b2-b4^2 = 7
    // Coefficient of x^2*z^2: a1*c3+a3*c1+a5*c5 - 2*b1*b3-b5^2 = 5
    // Coefficient of y^2*z^2: a2*c3+a3*c2+a6*c6 - 2*b2*b3-b6^2 = 1
    // Coefficient of x^3*z: a1*c5+a5*c1 - 2*b1*b5 = 4  (from x^3z)
    // Coefficient of x^2*yz: a1*c6+a6*c1+a4*c5+a5*c4 - 2*b1*b6-2*b4*b5 = -2
    // Coefficient of xy^2*z: a2*c5+a5*c2+a4*c6+a6*c4 - 2*b2*b5-2*b4*b6 = 0
    // Coefficient of xyz^2: a3*c4+a4*c3+a5*c6+a6*c5 - 2*b3*b4-2*b5*b6 = 0
    // Coefficient of xz^3: a3*c5+a5*c3 - 2*b3*b5 = 2  (from xz^3)
    // Coefficient of x^2*y*z: wait, x^2yz already done
    // Actually, x^3z and xz^3 are odd-degree terms. Let me recount monomials of degree 4:
    // x^4, y^4, z^4, x^3y, x^3z, x^2y^2, x^2yz, x^2z^2, xy^3, xy^2z, xyz^2, xz^3, y^3z, y^2z^2, yz^3

    // For f = 3x^4 + 4x^3z + 7x^2y^2 - 2x^2yz + 5x^2z^2 + 2xy^2z + 2xz^3 + y^4 + y^2z^2 + z^4

    // This approach is getting complex. Skip for now.
    printf "  p=%o: (skipping full decomposition check)\n", p;
end for;

printf "\nDone.\n";
quit;
