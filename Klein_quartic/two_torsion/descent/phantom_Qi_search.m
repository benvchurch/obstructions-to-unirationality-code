/*******************************************************************************
 * phantom_Qi_search.m
 *
 * Search for a quadric decomposition of
 *   f = 4x^4-2x^3y-2x^3z+6x^2y^2-3x^2z^2-2xy^3-2xz^3
 *       +y^4-2y^3z+3y^2z^2-2yz^3+4z^4
 * over Q(i), i.e., find Q1' = C+iE, Q3' = C-iE, Q2' such that
 *   f = Q1'*Q3' - Q2'^2 = C^2+E^2 - Q2'^2
 *
 * Strategy: search over F_p for p = 13 (where i, sqrt(-3) both exist),
 * find all decompositions, identify those that are i-conjugate.
 * Then try to lift to Q(i).
 *
 * Also compute the descent cocycle for any Q(i)-decomposition found.
 ******************************************************************************/

Q := Rationals();
Poly3<x,y,z> := PolynomialRing(Q, 3);

A := x^2-x*y-x*z+y^2-y*z+z^2;
B := x*y;
D := x^2-z^2;
f := A^2 + 3*B^2 + 3*D^2;

printf "f = %o\n\n", f;

// Work over F_13 where i=5, sqrt(-3)=7
p := 13;
Fp := GF(p);
ii := Fp!5;   // i in F_13: 5^2=25=12=-1
w := Fp!7;    // sqrt(-3) in F_13: 7^2=49=10=-3
printf "p=%o: i=%o (i^2=%o), w=%o (w^2=%o)\n\n", p, ii, ii^2, w, w^2;

P2<X,Y,Z> := ProjectiveSpace(Fp, 2);
fp := Evaluate(f, [X, Y, Z]);
Cp := Curve(P2, fp);
printf "C mod %o: smooth=%o, genus=%o\n\n", p, IsNonsingular(Cp), Genus(Cp);

// A quadric over F_p has 6 coefficients: [x^2, y^2, z^2, xy, xz, yz]
// Search: enumerate Q2' and check if f + Q2'^2 = C^2+E^2 for some C, E
// Equivalently: f + Q2'^2 is a sum of two squares mod p

// For F_p with p=1 mod 4: every element of F_p is a sum of two squares
// So the question is about QUADRATIC FORMS being a sum of two squares

// Alternative approach: directly enumerate decompositions
// f = q1*q3 - q2^2 where q1,q3 are quadrics conjugate under some involution
// For i-conjugation: q1 = C + i*E, q3 = C - i*E

// A quadric Q = sum a_ij X_i X_j has 6 coefficients
// C has 6 coefficients, E has 6 coefficients -> 12 free params
// Q2 has 6 coefficients -> 18 params total
// f = C^2+E^2-Q2^2 gives 15 equations (# monomials of degree 4)
// So 18-15 = 3 degrees of freedom

// More efficient: search over Q2 (6 params), check if f+Q2^2 = C^2+E^2

// For small search, parametrize Q2 and check
Poly3p<xp,yp,zp> := PolynomialRing(Fp, 3);

// Our known decomposition over Q(sqrt(-3)):
// Q1 = A+wB, Q3 = A-wB, Q2 = wD
// Over F_13: w=7
Q1_known := Evaluate(A,[xp,yp,zp]) + w*Evaluate(B,[xp,yp,zp]);
Q3_known := Evaluate(A,[xp,yp,zp]) - w*Evaluate(B,[xp,yp,zp]);
Q2_known := w*Evaluate(D,[xp,yp,zp]);
fp_poly := Evaluate(f,[xp,yp,zp]);

printf "Known decomposition (sqrt(-3)):\n";
printf "  Q1 = %o\n", Q1_known;
printf "  Q3 = %o\n", Q3_known;
printf "  Q2 = %o\n", Q2_known;
printf "  Q1*Q3-Q2^2 = f? %o\n\n", Q1_known*Q3_known - Q2_known^2 eq fp_poly;

// Now search for i-conjugate decompositions
// Q1' = C + i*E, Q3' = C - i*E = C + (p-i)*E (mod p)
// f = C^2 + E^2 - Q2'^2 (since i*(-i) = 1 mod p, and (C+iE)(C-iE) = C^2+E^2)
// Wait: (C+iE)(C-iE) = C^2 - (iE)(-iE) = C^2 - (-i^2)E^2 = C^2 - E^2 (since i^2=-1)
// NO! (C+iE)(C-iE) = C^2 - i^2 E^2 = C^2 + E^2. Yes.

printf "Searching for i-conjugate decompositions f = C^2+E^2-Q2^2 mod %o...\n", p;

// Represent quadrics as vectors [x^2,y^2,z^2,xy,xz,yz]
mons := [xp^2, yp^2, zp^2, xp*yp, xp*zp, yp*zp];

function QuadFromVec(v)
    return &+[v[i]*mons[i] : i in [1..6]];
end function;

// Instead of 18-dim search, fix Q2 and solve for C, E
// f + Q2^2 = C^2 + E^2
// This is a sum-of-two-squares problem for a quartic form

// Actually, the most efficient approach: enumerate decompositions
// f = Q1*Q3 - Q2^2 where Q1 is conjugate to Q3 under SOME automorphism

// Let me instead use the function field approach
// Work in FF of C over F_p(i) = F_{p^2} (but p=13 has i in F_p)

// Since i ∈ F_13, we can just search over F_13
// Enumerate Q2 with small coefficients, check if f+Q2^2 factors as (C+iE)(C-iE)

// Better: enumerate C and E directly
found := 0;
for c1 in Fp do for c2 in Fp do for c3 in Fp do
for c4 in Fp do for c5 in Fp do for c6 in Fp do
    C := QuadFromVec([c1,c2,c3,c4,c5,c6]);
    // f = C^2+E^2-Q2^2 => E^2 = f-C^2+Q2^2
    // For given C: need to check if f-C^2 can be written as E^2-Q2^2 = (E-Q2)(E+Q2)
    // Easier: for given C, check all E
    remC := fp_poly - C^2;
    // remC = E^2 - Q2^2 => for each E, Q2^2 = E^2 - remC
    for e1 in Fp do for e2 in Fp do for e3 in Fp do
    for e4 in Fp do for e5 in Fp do for e6 in Fp do
        E := QuadFromVec([e1,e2,e3,e4,e5,e6]);
        Q2sq := E^2 - remC;  // should equal Q2^2
        // Check if Q2sq is a perfect square
        // Q2sq is degree 4: need it to be the square of a degree-2 form
        // Quick check: coefficient of x^4 should be a perfect square
        coeff_x4 := MonomialCoefficient(Q2sq, xp^4);
        if not IsSquare(coeff_x4) then continue; end if;
        sq_x4 := Sqrt(coeff_x4);
        // Try Q2 = sq_x4*x^2 + ... and work out
        // This is expensive. Let me use a smarter check.
        // A quartic is a perfect square of a quadric iff it equals q^2 for some q
        // Just try: sqrt of x^4 coeff determines leading term
        // Then subtract and continue
        if Q2sq eq Poly3p!0 then
            Q2test := Poly3p!0;
            // f = C^2 + E^2, Q2=0
            found +:= 1;
            printf "  #%o: C=%o, E=%o, Q2=0\n", found, C, E;
            continue;
        end if;
        // Check by trying both signs of sqrt
        for sign in [1, -1] do
            q2_0 := Fp!(sign) * sq_x4;
            partial := Q2sq - (q2_0*xp^2)^2;
            // Get xy coefficient
            coeff_x3y := MonomialCoefficient(partial, xp^3*yp);
            if q2_0 eq 0 then continue; end if;  // handle separately
            q2_xy := coeff_x3y / (2*q2_0);
            partial -:= 2*q2_0*xp^2 * q2_xy*xp*yp;
            partial -:= (q2_xy*xp*yp)^2;
            // Get xz coefficient
            coeff_x3z := MonomialCoefficient(partial, xp^3*zp);
            q2_xz := coeff_x3z / (2*q2_0);
            partial -:= 2*q2_0*xp^2 * q2_xz*xp*zp;
            partial -:= 2*q2_xy*xp*yp * q2_xz*xp*zp;
            partial -:= (q2_xz*xp*zp)^2;
            // Now check y^4 coefficient for y^2 term
            coeff_y4 := MonomialCoefficient(partial, yp^4);
            if not IsSquare(coeff_y4) then continue; end if;
            q2_y2 := Sqrt(coeff_y4);
            // ... this is getting very tedious
            // Let me just check if Q2sq = (q2_0*x^2+q_xy*xy+q_xz*xz+q_y2*y^2+q_yz*yz+q_z2*z^2)^2
            // by direct comparison
            break;
        end for;
    end for; end for; end for;
    end for; end for; end for;
    break c1; // This is way too slow (13^12 iterations)
end for; end for; end for;
end for; end for; end for;

// MUCH better approach: use the function field
printf "\n=== Function field approach ===\n";
printf "Computing (1/2)div(q1) over F_%o and checking via i-decomposition...\n\n", p;

// Over F_p, compute the known decomposition's half-divisor
// Then look for an i-based function with the same half-divisor

Fpx<t> := FunctionField(Fp);
Fpxy<u> := PolynomialRing(Fpx);

fp_aff := Evaluate(fp_poly, [t, u, Fp!1]);
FF<uu> := FunctionField(fp_aff);
elt_t := FF ! t;
elt_u := uu;

// Known decomposition: q1 = A+wB, q2 = wD
Aval := elt_t^2 - elt_t*elt_u - elt_t + elt_u^2 - elt_u + 1;
Bval := elt_t*elt_u;
Dval := elt_t^2 - 1;

q1_w := Aval + w*Bval;
q2_w := w*Dval;
q3_w := Aval - w*Bval;

printf "q1*q3 = q2^2? %o\n", q1_w*q3_w eq q2_w^2;

D_q1 := Divisor(q1_w);
printf "div(q1_w):\n";
for pl in Support(D_q1) do
    printf "  deg-%o, mult %o\n", Degree(pl), Valuation(D_q1, pl);
end for;

// Half divisor
function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

ok, D_half := HalfDiv(D_q1);
printf "All even? %o\n\n", ok;

// Now try to construct q1' using i instead of w
// q1' = C + i*E where C,E are quadrics over F_p
// On C: q1'*q3' = q2'^2

// Key insight: we need (1/2)div(q1') ~ (1/2)div(q1_w) in Pic^0
// Equivalently: (1/2)div(q1'/q1_w) ~ 0, i.e., q1'/q1_w is a square on C
// So q1' = q1_w * h^2 for some function h

// Or more precisely: div(q1') = div(q1_w) + 2*div(h)
// So q1' = c * q1_w * h^2 for some constant c and function h

// The simplest case: q1' = c * q1_w for some c in F_p*
// Then Q1' = c*Q1. Let's check: if c = w/i (so that Q1' = (w/i)*Q1, which converts
// the sqrt(-3) decomposition to an i-decomposition)
// w/i = 7/5 = 7*5^{-1}. 5^{-1} mod 13: 5*8=40=1 mod 13, so 5^{-1}=8.
// w/i = 7*8 = 56 = 4 mod 13.

c_conv := w * Fp!8;  // w/i = 7*8 = 56 = 4 mod 13
printf "w/i = %o\n", c_conv;

// q1'_test = c_conv * q1_w
q1_i_test := c_conv * q1_w;

// Check: is q1_i_test = C + i*E for real C, E?
// q1_w = A + w*B, so c_conv*q1_w = c_conv*A + c_conv*w*B
// Need c_conv*A to be real (it is, since c_conv, A are in F_p)
// Need c_conv*w*B = i*E for real E: c_conv*w = i*? So E = (c_conv*w/i)*B = c_conv^2*B
// Actually: c_conv*w = 4*7 = 28 = 2 mod 13. And i = 5.
// Need c_conv*w = i * E_coeff, so E_coeff = c_conv*w/i = 2/5 = 2*8 = 16 = 3 mod 13.

// So q1'_test = 4*A + i*3*B? Let's verify: 4*A + 5*3*B = 4A + 15B = 4A + 2B mod 13
// And c_conv*q1_w = 4*(A+7B) = 4A + 28B = 4A + 2B. ✓

// So Q1' = 4A + i*3B (over Q(i)), Q3' = 4A - i*3B
// Q2' = ? We need Q1'*Q3' - f = Q2'^2
// Q1'*Q3' = (4A)^2 + (3B)^2 = 16A^2 + 9B^2 = 3A^2 + 9B^2 (mod 13)
// f = A^2 + 3B^2 + 3D^2 (mod 13: 3B^2+3D^2 = 3(B^2+D^2))
// Wait, f = A^2+3B^2+3D^2. Over F_13: f = A^2+3B^2+3D^2.
// Q1'*Q3' = 16A^2+9B^2 = 3A^2+9B^2 mod 13.
// Q2'^2 = Q1'*Q3' - f = 3A^2+9B^2 - A^2-3B^2-3D^2 = 2A^2+6B^2-3D^2 mod 13
//        = 2A^2+6B^2+10D^2 mod 13

// Hmm, need to check if 2A^2+6B^2+10D^2 is a perfect square mod 13.
// This is probably not going to be a perfect square in general.

// The issue: scaling q1 by a constant changes the decomposition but also changes Q2.
// The correct approach is: q1' = c * q1_w, so q3' = sigma_i(q1') where sigma_i: i->-i.
// But sigma_i(q1_w) is NOT q3_w (since q1_w involves w, not i).

// Let me think differently.
// Over F_p = F_13, both i and w exist. So F_p(i) = F_p(w) = F_p.
// Any decomposition f = q1*q3 - q2^2 over F_p is valid.
// The question is: which decompositions are "i-conjugate" vs "w-conjugate"?

// An "i-conjugate" decomposition: q3 = sigma_i(q1) where sigma_i is the F_p-automorphism
// sending i -> -i. But over F_p, sigma_i is the identity (i is in F_p).
// So this doesn't make sense over F_p.

// The correct framework: over Q(i), find Q1', Q3' = conj_i(Q1'), Q2' with
// Q-rational coefficients for the "real parts" and "imaginary parts".
// Over F_p, this means: Q1' = C + i*E where C, E have F_p-coefficients
// (representing "Q-rational" quadrics), and Q3' = C - i*E.

// So Q1'*Q3' = C^2 + E^2. f = C^2+E^2 - Q2'^2.

// Search for C, E, Q2 over F_13 with C^2+E^2-Q2^2 = f AND
// (1/2)div(Q1') = (1/2)div(q1_w) in Pic

printf "\n=== Systematic search for i-decompositions mod %o ===\n", p;
// Enumerate Q2 (6 params over F_p, but only need representative)
// For each Q2: check if f+Q2^2 = C^2+E^2
// f+Q2^2 = (C+iE)(C-iE) means f+Q2^2 factors over F_p (since i in F_p)

// Factoring a degree-4 form as product of two degree-2 forms:
// f+Q2^2 = L1*L2 where L1,L2 are quadrics
// With L1 = C+iE, L2 = C-iE

// Direct search: for each Q2, compute g = f+Q2^2, try to factor g
count := 0;
decomps := [];
for q1c in Fp do for q2c in Fp do for q3c in Fp do
for q4c in Fp do for q5c in Fp do for q6c in Fp do
    Q2test := QuadFromVec([q1c,q2c,q3c,q4c,q5c,q6c]);
    g := fp_poly + Q2test^2;
    // g should factor as L1*L2 where L1 = C+iE, L2 = C-iE
    // This means g = (C+iE)(C-iE) with C,E quadrics
    // In F_p[x,y,z], we need g to factor as product of two quadrics

    // Try to factor g: if g = L1*L2 with L1 ≠ L2 (both degree 2)
    // Use Magma's Factorization if available for multivariate polys
    // Actually, checking factorization of ternary quartics is hard
    // Instead: evaluate on random points to screen

    // Quick screen: g(1,0,0) should be a^2+b^2 for some a,b
    g_100 := Evaluate(g, [Fp!1,Fp!0,Fp!0]);
    if not IsSquare(g_100) and g_100 ne 0 then
        // g(1,0,0) = c^2+e^2. Since i in F_p, c^2+e^2 = (c+ie)(c-ie)
        // is always factorable. Skip this screen.
    end if;

    // g(1,0,0) = product of L1(1,0,0)*L2(1,0,0)
    // More useful: if g = L1*L2, then g restricted to any line factors
    // Check: g(t,1,0) should factor as product of two quadratics in t
    Fpt<tt> := PolynomialRing(Fp);
    g_line := Evaluate(g, [tt, Fp!1, Fp!0]);
    if Degree(g_line) ne 4 then continue; end if;
    facts := Factorization(g_line);
    has_quad_factor := false;
    for fa in facts do
        if Degree(fa[1]) eq 2 and fa[2] ge 1 then
            has_quad_factor := true;
            break;
        end if;
    end for;
    if not has_quad_factor then continue; end if;

    // Also check g(t,0,1) and g(0,t,1)
    g_line2 := Evaluate(g, [tt, Fp!0, Fp!1]);
    if Degree(g_line2) ge 4 then
        facts2 := Factorization(g_line2);
        ok2 := false;
        for fa in facts2 do
            if Degree(fa[1]) eq 2 then ok2 := true; break; end if;
        end for;
        if not ok2 then continue; end if;
    end if;

    g_line3 := Evaluate(g, [Fp!0, tt, Fp!1]);
    if Degree(g_line3) ge 4 then
        facts3 := Factorization(g_line3);
        ok3 := false;
        for fa in facts3 do
            if Degree(fa[1]) eq 2 then ok3 := true; break; end if;
        end for;
        if not ok3 then continue; end if;
    end if;

    // Passed all screens. Try to actually factor g = L1*L2
    // Extract L1 from g(t,1,0) factorization
    for fa in facts do
        if Degree(fa[1]) ne 2 then continue; end if;
        L1_10 := fa[1];  // L1(t,1,0)
        L2_10 := g_line / (L1_10^fa[2]);
        if fa[2] ge 2 then
            L2_10 := L1_10;  // double root
        end if;
        if Degree(L2_10) ne 2 then continue; end if;

        // L1(x,y,0) = l1*x^2 + l2*xy + l3*y^2
        l1_10 := Coefficient(L1_10, 2);
        l2_10 := Coefficient(L1_10, 1);
        l3_10 := Coefficient(L1_10, 0);

        // Similarly from g(t,0,1): L1(t,0,1) = l1*t^2 + l5*t + l4
        // where L1 = l1*x^2 + l3*y^2 + l4*z^2 + l2*xy + l5*xz + l6*yz
        for fa2 in facts2 do
            if Degree(fa2[1]) ne 2 then continue; end if;
            L1_01 := fa2[1];
            l1_01 := Coefficient(L1_01, 2);
            if l1_01 ne l1_10 then continue; end if;  // same x^2 coeff
            l5_01 := Coefficient(L1_01, 1);
            l4_01 := Coefficient(L1_01, 0);

            // From g(0,t,1): L1(0,t,1) = l3*t^2 + l6*t + l4
            for fa3 in facts3 do
                if Degree(fa3[1]) ne 2 then continue; end if;
                L1_11 := fa3[1];
                l3_11 := Coefficient(L1_11, 2);
                if l3_11 ne l3_10 then continue; end if;
                l4_11 := Coefficient(L1_11, 0);
                if l4_11 ne l4_01 then continue; end if;
                l6_11 := Coefficient(L1_11, 1);

                // Reconstruct L1
                L1_full := l1_10*xp^2 + l3_10*yp^2 + l4_01*zp^2
                           + l2_10*xp*yp + l5_01*xp*zp + l6_11*yp*zp;
                L2_full := g / L1_full;
                // Check if L2_full is actually a polynomial
                if L1_full eq 0 then continue; end if;

                // Verify
                test := L1_full * L2_full;
                if test eq g then
                    // Check L2 is also degree 2
                    if TotalDegree(L2_full) ne 2 then continue; end if;

                    // Found! L1, L2 with g = L1*L2
                    // Q1' = L1, Q3' = L2
                    // Check: is this an i-conjugate pair?
                    // C = (L1+L2)/2, E = (L1-L2)/(2i)
                    C_test := (L1_full + L2_full) / 2;
                    E_num := L1_full - L2_full;
                    // E_num = 2*i*E, so E = E_num/(2*i)
                    inv2i := (2*ii)^(-1);  // 1/(2i) mod 13
                    E_test := E_num * inv2i;

                    count +:= 1;
                    if count le 10 then
                        printf "Decomposition #%o: Q2=%o\n", count, Q2test;
                        printf "  L1=%o, L2=%o\n", L1_full, L2_full;
                        printf "  C=%o, E=%o\n", C_test, E_test;

                        // Check the half-divisor matches
                        L1_ff := Evaluate(L1_full, [elt_t, elt_u, Fp!1]);
                        D_L1 := Divisor(L1_ff);
                        ok_L1, D_half_L1 := HalfDiv(D_L1);
                        if ok_L1 then
                            diff := D_half_L1 - D_half;
                            V, phi := RiemannRochSpace(diff);
                            printf "  L((1/2)div(L1)-(1/2)div(q1_w)) dim = %o", Dimension(V);
                            if Dimension(V) ge 1 then
                                printf " => SAME CLASS";
                            else
                                printf " => different class";
                            end if;
                            printf "\n";
                        else
                            printf "  L1 divisor not all even\n";
                        end if;
                        printf "\n";
                    end if;

                    Append(~decomps, <Q2test, L1_full, L2_full, C_test, E_test>);
                end if;
            end for;
        end for;
    end for;
end for; end for; end for;
end for; end for; end for;

printf "Total i-decompositions found: %o\n", count;

printf "\nDone.\n";
quit;
