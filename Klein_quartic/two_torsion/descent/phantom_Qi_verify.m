/*******************************************************************************
 * phantom_Qi_verify.m
 *
 * For f = A^2+3B^2+3D^2 (our phantom quartic), the Brauer class is
 *   delta(eta) = (-1, -3)_Q.
 *
 * Local invariants: inv_infty = 1/2 (both neg), inv_3 = 1/2 (checked),
 * inv_2 = 0 (product formula), inv_p = 0 for p >= 5.
 *
 * Q(i) splits this: Q_3(i)/Q_3 is unramified quad ext, kills inv_3.
 *
 * Verify: work over Q(i), check that (1/2)div(q1) is principal
 * (i.e., eta is representable by a Q(i)-rational divisor).
 * This confirms the Brauer class splits over Q(i).
 *
 * Then try to find explicit Q(i)-decomposition.
 ******************************************************************************/

Q := Rationals();
Poly3<x,y,z> := PolynomialRing(Q, 3);

A := x^2-x*y-x*z+y^2-y*z+z^2;
B := x*y;
D := x^2-z^2;
f := A^2 + 3*B^2 + 3*D^2;

printf "=== Brauer class of phantom quartic ===\n";
printf "f = A^2 + 3*B^2 + 3*D^2\n";
printf "Over Q(sqrt(-3)): Q1=A+wB, Q3=A-wB, Q2=wD, cocycle lambda=-1\n";
printf "Brauer class: (-1, -3)_Q\n\n";

printf "Local invariants of (-1, -3)_Q:\n";
printf "  inf: both neg => inv = 1/2\n";
printf "  3: -x^2-3y^2=z^2 over Q_3: over F_3, x^2+z^2=0 has no nontrivial soln\n";
printf "     (since -1 is QNR mod 3) => inv_3 = 1/2\n";
printf "  2: by product formula sum inv_v = 0, inv_2 = 0\n";
printf "  p>=5: both units, Chevalley-Warning => inv_p = 0\n";
printf "  => Ramified at infinity and 3\n\n";

// === Verify Q(i) kills the Brauer class ===
// Work over Q(i,sqrt(-3)) = Q(zeta_12) via F_p computation
// At p = 13: i = 5, w = sqrt(-3) = 7

p := 13;
Fp := GF(p);
ii := Fp!5;
w := Fp!7;

printf "=== Verification over F_%o (i=%o, w=%o) ===\n\n", p, ii, w;

// Set up function field of C over F_p
Fpx<t> := FunctionField(Fp);
Fpxy<u> := PolynomialRing(Fpx);
fp_aff := u^4 + (-2*t-2)*u^3 + (6*t^2+3)*u^2 + (-2*t^3-2)*u + (4*t^4-2*t^3-3*t^2-2*t+4);
FF<uu> := FunctionField(fp_aff);
elt_t := FF ! t;
elt_u := uu;

// Known Q(sqrt(-3)) decomposition
Aval := elt_t^2 - elt_t*elt_u - elt_t + elt_u^2 - elt_u + 1;
Bval := elt_t*elt_u;
Dval := elt_t^2 - 1;

q1_w := Aval + w*Bval;
q2_w := w*Dval;

// Half divisor of q1_w
function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

D_q1w := Divisor(q1_w);
ok, D_half_w := HalfDiv(D_q1w);
printf "D = (1/2)div(q1_w): defined=%o\n", ok;

// Check if D is principal (should NOT be, since eta != 0)
V0, phi0 := RiemannRochSpace(D_half_w);
printf "dim L(D) = %o (should be 0, meaning eta != 0)\n\n", Dimension(V0);

// Now: can we find a DIFFERENT decomposition whose Q1' involves i instead of w?
// Search: enumerate pairs (Q1', Q2') over F_p where Q1' = C + i*E
// such that f = Q1'*Q3' - Q2'^2 on C and (1/2)div(Q1') ~ D

// Parametrize: Q1' = sum a_j * mons_j where a_j in F_p
// This is a 6-dimensional search for Q1' coefficients
// For each Q1', set Q3' = conjugate (i -> -i), check Q1'*Q3' - f = Q2'^2

printf "=== Searching for i-conjugate decompositions mod %o ===\n", p;
printf "(Looking for Q1'=C+i*E with (1/2)div(q1') ~ (1/2)div(q1_w))\n\n";

// Over F_p, "i-conjugation" means: write Q1' = C + i*E where C, E have
// coefficients decomposed as "real" and "imaginary" parts relative to i.
// But since i ∈ F_p, this decomposition is:
// C = (Q1' + Q3')/2, E = (Q1' - Q3')/(2i)
// The KEY constraint: C and E should be "defined over Q", meaning their
// coefficients should NOT depend on i. Over F_p this means: the coeffs of
// C and E should be in the "real" subfield = F_p (trivially).

// Actually, the constraint is that C and E should lift to Q-rational quadrics.
// Over F_p, every element is "rational", so we need to be more careful.

// Better approach: directly search for decompositions f = Q1*Q3 - Q2^2
// over F_p and check which give the same half-divisor as our known one.

Poly3p<xp,yp,zp> := PolynomialRing(Fp, 3);
fp_hom := Evaluate(f, [xp,yp,zp]);

// Enumerate Q2 with coefficients in F_p
mons := [xp^2, yp^2, zp^2, xp*yp, xp*zp, yp*zp];

count := 0;
same_class_count := 0;

for q1c in Fp do for q2c in Fp do for q3c in Fp do
for q4c in Fp do for q5c in Fp do for q6c in Fp do
    Q2_test := q1c*xp^2+q2c*yp^2+q3c*zp^2+q4c*xp*yp+q5c*xp*zp+q6c*yp*zp;

    // g = f + Q2^2 should factor as Q1*Q3 (product of two quadrics)
    g := fp_hom + Q2_test^2;

    // Quick check: g(t,1,0) must factor into two quadratics in t
    Fpt<tt> := PolynomialRing(Fp);
    g10 := Evaluate(g, [tt, Fp!1, Fp!0]);
    if Degree(g10) ne 4 then continue; end if;

    facts := Factorization(g10);
    // Need a degree-2 factor
    has_d2 := false;
    for fa in facts do
        if Degree(fa[1]) eq 2 then has_d2 := true; break; end if;
    end for;
    if not has_d2 then continue; end if;

    // Now try to reconstruct the full factorization
    // g = Q1 * Q3 where Q1, Q3 are quadrics
    // Use g(t,1,0), g(t,0,1), g(0,t,1) to determine Q1

    g01 := Evaluate(g, [tt, Fp!0, Fp!1]);
    g11 := Evaluate(g, [Fp!0, tt, Fp!1]);

    if Degree(g01) ne 4 or Degree(g11) ne 4 then continue; end if;

    facts01 := Factorization(g01);
    facts11 := Factorization(g11);

    // For each combination of degree-2 factors
    for fa10 in facts do
        if Degree(fa10[1]) ne 2 then continue; end if;
        // Q1(t,1,0) = this factor
        a_x2 := Coefficient(fa10[1], 2);
        a_xy := Coefficient(fa10[1], 1);
        a_y2 := Coefficient(fa10[1], 0);

        for fa01 in facts01 do
            if Degree(fa01[1]) ne 2 then continue; end if;
            // Q1(t,0,1) = this factor
            if Coefficient(fa01[1], 2) ne a_x2 then continue; end if;
            a_xz := Coefficient(fa01[1], 1);
            a_z2 := Coefficient(fa01[1], 0);

            for fa11 in facts11 do
                if Degree(fa11[1]) ne 2 then continue; end if;
                // Q1(0,t,1) = this factor
                if Coefficient(fa11[1], 2) ne a_y2 then continue; end if;
                if Coefficient(fa11[1], 0) ne a_z2 then continue; end if;
                a_yz := Coefficient(fa11[1], 1);

                Q1_test := a_x2*xp^2+a_y2*yp^2+a_z2*zp^2+a_xy*xp*yp+a_xz*xp*zp+a_yz*yp*zp;
                if Q1_test eq 0 then continue; end if;

                // Check: g = Q1_test * Q3_test
                rem := g div Q1_test;
                if g ne Q1_test * rem then continue; end if;
                if TotalDegree(rem) ne 2 then continue; end if;
                Q3_test := rem;

                // Valid decomposition! f = Q1*Q3 - Q2^2
                count +:= 1;

                // Check half-divisor
                q1_ff := Evaluate(Q1_test, [elt_t, elt_u, Fp!1]);
                D_q1_test := Divisor(q1_ff);
                ok_test, D_half_test := HalfDiv(D_q1_test);

                if ok_test then
                    // Compare with known half-divisor
                    ddiff := D_half_test - D_half_w;
                    Vtest, _ := RiemannRochSpace(ddiff);
                    if Dimension(Vtest) ge 1 then
                        same_class_count +:= 1;
                        if same_class_count le 5 then
                            printf "MATCH #%o: Q2=%o\n", same_class_count, Q2_test;
                            printf "  Q1=%o\n  Q3=%o\n", Q1_test, Q3_test;
                            // Decompose: C = (Q1+Q3)/2, E = (Q1-Q3)/(2i)
                            C_part := (Q1_test+Q3_test)/2;
                            E_num := Q1_test - Q3_test;
                            inv2i := (2*ii)^(-1);
                            E_part := E_num * inv2i;
                            printf "  C=(Q1+Q3)/2 = %o\n", C_part;
                            printf "  E=(Q1-Q3)/(2i) = %o\n", E_part;
                            // Check: is Q2 of the form i*H?
                            // Q2/i = Q2 * i^(-1)
                            inv_i := ii^(-1);
                            Q2_div_i := Q2_test * inv_i;
                            printf "  Q2/i = %o\n", Q2_div_i;

                            // Compute cocycle for this decomposition
                            q2_ff := Evaluate(Q2_test, [elt_t, elt_u, Fp!1]);
                            q3_ff := Evaluate(Q3_test, [elt_t, elt_u, Fp!1]);

                            // sigma'(Q2) (i -> -i): replace i=5 by -i=8
                            // sigma'(q2) where Q2 has i-coefficients...
                            // Over F_p, sigma_i(a) for a in F_p:
                            // We need to decompose Q2 = G + i*H and apply G - i*H
                            // But over F_p, every element is "real" since i in F_p
                            // We need to know the Q-lift to do this properly

                            printf "\n";
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end for;
end for; end for; end for;
end for; end for; end for;

printf "Total decompositions found: %o\n", count;
printf "With same eta class: %o\n\n", same_class_count;

// === Also verify: over Q(i), check if eta is principal ===
printf "=== Checking eta representability over Q(i) ===\n";
// Over F_p where i in F_p: if eta is representable over Q(i),
// then it should be principal when we "allow i-rational functions"
// But over F_p, everything is F_p-rational, so we can just check
// if eta is principal over F_p (which it isn't if eta != 0).

// The real test: check over F_{p^2} for p where i NOT in F_p
// Use p = 7 (where i not in F_7, since -1 is QNR mod 7... wait,
// 7 ≡ 3 mod 4, so -1 is QNR mod 7. So i not in F_7.
// F_7(i) = F_49.

printf "Working over F_7 (i not in F_7) and F_49 = F_7(i):\n";
p2 := 7;
Fp2 := GF(p2);
Fp2x<t2> := FunctionField(Fp2);
Fp2xy<u2> := PolynomialRing(Fp2x);
fp2_aff := u2^4+(-2*t2-2)*u2^3+(6*t2^2+3)*u2^2+(-2*t2^3-2)*u2+(4*t2^4-2*t2^3-3*t2^2-2*t2+4);
FF2<uu2> := FunctionField(fp2_aff);
elt_t2 := FF2!t2;
elt_u2 := uu2;

// sqrt(-3) over F_7: need s^2 = -3 = 4 mod 7. s = 2 or 5.
w7 := Fp2!2;
printf "F_7: sqrt(-3) = %o (check: %o^2 = %o)\n", w7, w7, w7^2;

q1_w7 := (elt_t2^2-elt_t2*elt_u2-elt_t2+elt_u2^2-elt_u2+1) + w7*(elt_t2*elt_u2);
D_q1_7 := Divisor(q1_w7);
ok7, D_half_7 := HalfDiv(D_q1_7);
printf "F_7: (1/2)div(q1) defined: %o\n", ok7;

V7, _ := RiemannRochSpace(D_half_7);
printf "F_7: dim L((1/2)div(q1)) = %o => eta %o over F_7\n",
    Dimension(V7), Dimension(V7) ge 1 select "=0" else "!=0";

// Now over F_49 = F_7(i)
Fq := GF(p2^2);  // F_49
printf "\nF_49 = F_7(i): ";
// Find i in F_49
for a in Fq do
    if a^2 eq Fq!(-1) then
        printf "i = %o\n", a;
        break;
    end if;
end for;

Fqx<t3> := FunctionField(Fq);
Fqxy<u3> := PolynomialRing(Fqx);
fp3_aff := u3^4+(-2*t3-2)*u3^3+(6*t3^2+3)*u3^2+(-2*t3^3-2)*u3+(4*t3^4-2*t3^3-3*t3^2-2*t3+4);
FF3<uu3> := FunctionField(fp3_aff);
elt_t3 := FF3!t3;
elt_u3 := uu3;

// sqrt(-3) in F_49: since -3 = 4 mod 7, sqrt(-3) = 2 in F_7 ⊂ F_49
w49 := Fq!2;
q1_w49 := (elt_t3^2-elt_t3*elt_u3-elt_t3+elt_u3^2-elt_u3+1) + w49*(elt_t3*elt_u3);
D_q1_49 := Divisor(q1_w49);
ok49, D_half_49 := HalfDiv(D_q1_49);
printf "F_49: (1/2)div(q1) defined: %o\n", ok49;

V49, _ := RiemannRochSpace(D_half_49);
printf "F_49: dim L((1/2)div(q1)) = %o => eta %o over F_49\n",
    Dimension(V49), Dimension(V49) ge 1 select "=0 (REPRESENTABLE)" else "!=0";

printf "\nIf eta=0 over F_49 but eta!=0 over F_7:\n";
printf "  => eta becomes principal over F_7(i) but not F_7\n";
printf "  => confirms Brauer class splits over Q(i)\n";

printf "\nDone.\n";
quit;
