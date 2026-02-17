/*******************************************************************************
 * phantom_Qi_quick.m
 *
 * Quick check: can f = A^2+3B^2+3D^2 be decomposed as (P+iR)(P-iR) - Q2^2?
 * Theory: (-1,-3)_{Q(i)} = 0 since -1 = i^2. So eta IS representable over Q(i).
 * But does a quadric decomposition exist?
 *
 * Approach 1: Check if specific Q2 values work (guided by structure)
 * Approach 2: Brute force over small prime
 ******************************************************************************/

Q := Rationals();
Poly3<x,y,z> := PolynomialRing(Q, 3);
A := x^2-x*y-x*z+y^2-y*z+z^2;
B := x*y;
D := x^2-z^2;
f := A^2 + 3*B^2 + 3*D^2;

function HalfDiv(Dv)
    Bv := Dv - Dv;
    for pl in Support(Dv) do
        v := Valuation(Dv, pl);
        if v mod 2 ne 0 then return false, Bv; end if;
        Bv := Bv + (v div 2) * pl;
    end for;
    return true, Bv;
end function;

// Use p=13 where i=5, sqrt(-3)=7
p := 13;
Fp := GF(p);
ip := Fp!5;
wp := Fp!7;
printf "p=%o: i=%o, sqrt(-3)=%o\n\n", p, ip, wp;

P3p<xp,yp,zp> := PolynomialRing(Fp, 3);
fpp := Evaluate(f, [xp,yp,zp]);

Fpx<t> := FunctionField(Fp);
Fpxy<u> := PolynomialRing(Fpx);
fp_aff := Evaluate(fpp, [t, u, Fp!1]);
FF<uu> := FunctionField(fp_aff);
elt_t := FF!t;
elt_u := uu;

Aval := elt_t^2-elt_t*elt_u-elt_t+elt_u^2-elt_u+1;
Bval := elt_t*elt_u;
Dval := elt_t^2-1;
q1_w := Aval + wp*Bval;
D_q1w := Divisor(q1_w);
ok_w, D_half_w := HalfDiv(D_q1w);
printf "Known eta from sqrt(-3): defined=%o\n", ok_w;

Vw, _ := RiemannRochSpace(D_half_w);
printf "dim L(D_half_w) = %o (eta != 0)\n\n", Dimension(Vw);

// Strategy: over F_13, the known decomposition is
// Q1 = A+7B, Q3 = A-7B = A+6B, Q2 = 7D
// ANY other decomposition giving the same eta has Q1' = c*Q1*h^2 for some
// constant c and function h. For h=1: Q1'=c*Q1.
//
// For Q1' to be i-conjugate (Q1'=P+5R, Q3'=P-5R=P+8R):
// We need c*Q1 = P+5R and c*Q3 = P+8R = P-5R
// From these: c*(Q1+Q3) = 2P => P = c*(A+7B+A+6B)/2 = c*(2A+0B)/2 = c*A
//   Wait: Q1+Q3 = (A+7B)+(A+6B) = 2A+13B = 2A (mod 13)
//   Q1-Q3 = (A+7B)-(A+6B) = B
// So P = c*A, 2*5*R = c*B => R = c*B/10 = c*B*(10^{-1}) mod 13
// 10^{-1} mod 13: 10*4=40=1 mod 13. So 10^{-1}=4.
// R = 4cB

// Then Q2'^2 = Q1'*Q3' - f = c^2*Q1*Q3 - f = c^2*(A^2+3B^2) - (A^2+3B^2+3D^2)
//            = (c^2-1)*(A^2+3B^2) - 3D^2

// For c=1: Q2'^2 = -3D^2 = 10D^2 mod 13. sqrt(10) mod 13: need a^2=10.
//   3^2=9, 4^2=3, 6^2=10. YES! Q2' = 6D or 7D.
// But c=1 gives P=A, R=4B. And the Q(i) decomposition has Q2'=6D.
// Check lift to Q: P=A, R=aB for some a in Q. Then:
//   f = (A+iaB)(A-iaB) - Q2'^2 = A^2+a^2B^2 - Q2'^2
//   => Q2'^2 = A^2+a^2B^2-f = a^2B^2 - 3B^2 - 3D^2 = (a^2-3)B^2 - 3D^2
// Need a^2-3 and -3 to combine into a perfect square.
// (a^2-3)B^2 - 3D^2 = Q2'^2. This is a norm form; for Q2' rational we need
// (a^2-3)B^2 = Q2'^2 + 3D^2, a sum of two "squares" with weight 3.
// If a^2 = 3: Q2'^2 = -3D^2 => no rational solution.
// If a^2 = 4: Q2'^2 = B^2-3D^2 = x^2y^2-3(x^2-z^2)^2
//   = x^2y^2-3x^4+6x^2z^2-3z^4. Degree 4, not necessarily a perfect square.

printf "=== Approach: scale q1 by constants ===\n";
printf "Over F_13: Q1=A+7B, P=cA, R=4cB, Q2'^2=(c^2-1)(A^2+3B^2)-3D^2\n\n";

// Check which c in F_13 give a perfect square Q2'^2
Ap := Evaluate(A, [xp,yp,zp]);
Bp := Evaluate(B, [xp,yp,zp]);
Dp := Evaluate(D, [xp,yp,zp]);

for c in [Fp!1..Fp!(p-1)] do
    Q2sq := (c^2-1)*(Ap^2+3*Bp^2) - 3*Dp^2;
    // Check if Q2sq = Q^2 for some quadratic Q
    // Try: evaluate at a few points to get Q, then verify
    Fpt<tt> := PolynomialRing(Fp);
    q10 := Evaluate(Q2sq, [tt, Fp!1, Fp!0]);  // Q2sq(t,1,0)
    if Degree(q10) ne 4 then
        printf "c=%o: degenerate\n", c;
        continue;
    end if;
    // If Q2sq = Q^2, then q10 = Q(t,1,0)^2, so q10 should be a perfect square
    facts := Factorization(q10);
    is_sq := true;
    for fa in facts do
        if fa[2] mod 2 ne 0 then is_sq := false; break; end if;
    end for;
    if not is_sq then
        //printf "c=%o: q(t,1,0) not a perfect square\n", c;
        continue;
    end if;
    // Construct Q from sqrt of q10
    Q_10 := &*[fa[1]^(fa[2] div 2) : fa in facts];
    // Sign ambiguity: check both signs
    for sgn in [Fp!1, Fp!(-1)] do
        Qcand_10 := sgn * Q_10;
        // Get more data from q01 = Q2sq(t,0,1)
        q01 := Evaluate(Q2sq, [tt, Fp!0, Fp!1]);
        facts01 := Factorization(q01);
        is_sq01 := true;
        for fa in facts01 do
            if fa[2] mod 2 ne 0 then is_sq01 := false; break; end if;
        end for;
        if not is_sq01 then continue; end if;
        Q_01 := &*[fa[1]^(fa[2] div 2) : fa in facts01];

        for sgn2 in [Fp!1, Fp!(-1)] do
            Qcand_01 := sgn2 * Q_01;
            // Q(t,1,0) = a_x2*t^2 + a_xy*t + a_y2 => get a_x2, a_xy, a_y2
            if Degree(Qcand_10) ne 2 then continue; end if;
            a_x2 := Coefficient(Qcand_10, 2);
            a_xy := Coefficient(Qcand_10, 1);
            a_y2 := Coefficient(Qcand_10, 0);
            // Q(t,0,1) = a_x2*t^2 + a_xz*t + a_z2
            if Degree(Qcand_01) ne 2 then continue; end if;
            if Coefficient(Qcand_01, 2) ne a_x2 then continue; end if;
            a_xz := Coefficient(Qcand_01, 1);
            a_z2 := Coefficient(Qcand_01, 0);
            // Need a_yz: check Q2sq(0,t,1) = a_y2*t^2 + a_yz*t + a_z2 squared
            q_0t1 := Evaluate(Q2sq, [Fp!0, tt, Fp!1]);
            facts_0t1 := Factorization(q_0t1);
            is_sq_0t1 := true;
            for fa in facts_0t1 do
                if fa[2] mod 2 ne 0 then is_sq_0t1 := false; break; end if;
            end for;
            if not is_sq_0t1 then continue; end if;
            Q_0t1 := &*[fa[1]^(fa[2] div 2) : fa in facts_0t1];
            for sgn3 in [Fp!1, Fp!(-1)] do
                Qcand_0t1 := sgn3 * Q_0t1;
                if Degree(Qcand_0t1) ne 2 then continue; end if;
                if Coefficient(Qcand_0t1, 2) ne a_y2 then continue; end if;
                if Coefficient(Qcand_0t1, 0) ne a_z2 then continue; end if;
                a_yz := Coefficient(Qcand_0t1, 1);

                Q2_cand := a_x2*xp^2+a_y2*yp^2+a_z2*zp^2+a_xy*xp*yp+a_xz*xp*zp+a_yz*yp*zp;
                if Q2_cand^2 eq Q2sq then
                    printf "c=%o: Q2' = %o\n", c, Q2_cand;
                    printf "  L1 = %o*(%o) = %o\n", c, Ap+wp*Bp, c*(Ap+wp*Bp);
                    printf "  P = %o*A = %o\n", c, c*Ap;
                    printf "  R = %o*B = %o\n", 4*c, 4*c*Bp;
                    printf "  Decomp: f = (%o + %o*%o)(%o - %o*%o) - (%o)^2\n",
                        c*Ap, ip, 4*c*Bp, c*Ap, ip, 4*c*Bp, Q2_cand;

                    // What rational a would give P=A, R=aB?
                    // Over F_13: R = 4c*B. Lift: R = (some rational)*B.
                    // P = cA: lift c to Q. But c is just a F_13 element.
                    // For the lift to work over Q(i): f = (cA+i*4cB)(cA-i*4cB) - Q2'^2
                    // = c^2(A^2+16B^2) - Q2'^2
                    // Wait: (P+iR)(P-iR) = P^2+R^2 = c^2*A^2+16c^2*B^2
                    // Need: c^2*A^2+16c^2*B^2-Q2'^2 = A^2+3B^2+3D^2
                    // => (c^2-1)A^2+(16c^2-3)B^2-3D^2 = Q2'^2
                    // For c=1 over Q: 0+13B^2-3D^2 = Q2'^2. Need 13B^2-3D^2 to be a perfect sq.
                    // Hmm, not obvious.

                    printf "\n";
                end if;
            end for;
        end for;
    end for;
end for;

// === Approach 2: brute force over F_5 (smaller search space) ===
printf "\n=== F_5 brute force (5^6 = %o candidates) ===\n", 5^6;
p2 := 5;
Fp2 := GF(p2);
ip2 := Fp2!2;  // 2^2=4=-1 mod 5
printf "p=%o: i=%o\n", p2, ip2;

// Check sqrt(-3) mod 5: -3=2, is 2 QR mod 5? QR={1,4}. No.
// So we can't compare with the sqrt(-3) decomposition at p=5.
// Instead, just find all i-conjugate decompositions and count.

P3p2<xp2,yp2,zp2> := PolynomialRing(Fp2, 3);
fpp2 := Evaluate(f, [xp2,yp2,zp2]);
P2_5<X5,Y5,Z5> := ProjectiveSpace(Fp2, 2);
C5 := Curve(P2_5, Evaluate(f,[X5,Y5,Z5]));
printf "F_5 smooth: %o\n", IsNonsingular(C5);

// Function field over F_5
Fp2x<t2> := FunctionField(Fp2);
Fp2y<u2> := PolynomialRing(Fp2x);
fp2_aff := Evaluate(fpp2, [t2, u2, Fp2!1]);
FF2<uu2> := FunctionField(fp2_aff);
elt_t2 := FF2!t2;
elt_u2 := uu2;

Fp2t<tt2> := PolynomialRing(Fp2);
count2 := 0;
decomps := [];

for c1 in Fp2 do for c2 in Fp2 do for c3 in Fp2 do
for c4 in Fp2 do for c5 in Fp2 do for c6 in Fp2 do
    Q2test := c1*xp2^2+c2*yp2^2+c3*zp2^2+c4*xp2*yp2+c5*xp2*zp2+c6*yp2*zp2;
    g := fpp2 + Q2test^2;

    g10 := Evaluate(g, [tt2, Fp2!1, Fp2!0]);
    if Degree(g10) ne 4 then continue; end if;
    facts10 := Factorization(g10);
    has_d2 := false;
    for fa in facts10 do
        if Degree(fa[1]) eq 2 then has_d2 := true; break; end if;
    end for;
    if not has_d2 then continue; end if;

    g01 := Evaluate(g, [tt2, Fp2!0, Fp2!1]);
    g_0t1 := Evaluate(g, [Fp2!0, tt2, Fp2!1]);
    if Degree(g01) ne 4 or Degree(g_0t1) ne 4 then continue; end if;
    facts01 := Factorization(g01);
    facts_0t1 := Factorization(g_0t1);

    for fa10 in facts10 do
        if Degree(fa10[1]) ne 2 then continue; end if;
        ax2 := Coefficient(fa10[1], 2);
        axy := Coefficient(fa10[1], 1);
        ay2 := Coefficient(fa10[1], 0);

        for fa01 in facts01 do
            if Degree(fa01[1]) ne 2 then continue; end if;
            if Coefficient(fa01[1], 2) ne ax2 then continue; end if;
            axz := Coefficient(fa01[1], 1);
            az2 := Coefficient(fa01[1], 0);

            for fa_0t1 in facts_0t1 do
                if Degree(fa_0t1[1]) ne 2 then continue; end if;
                if Coefficient(fa_0t1[1], 2) ne ay2 then continue; end if;
                if Coefficient(fa_0t1[1], 0) ne az2 then continue; end if;
                ayz := Coefficient(fa_0t1[1], 1);

                L1 := ax2*xp2^2+ay2*yp2^2+az2*zp2^2+axy*xp2*yp2+axz*xp2*zp2+ayz*yp2*zp2;
                if L1 eq 0 then continue; end if;
                L2_cand := g div L1;
                if g ne L1 * L2_cand then continue; end if;
                if TotalDegree(L2_cand) ne 2 then continue; end if;

                // Check i-conjugacy
                inv2 := (Fp2!2)^(-1);
                P_test := (L1+L2_cand) * inv2;
                inv2i := (2*ip2)^(-1);
                R_test := (L1-L2_cand) * inv2i;
                if L1 ne P_test + ip2*R_test then continue; end if;

                count2 +:= 1;
                if count2 le 5 then
                    printf "Decomp #%o (mod 5): Q2=%o, P=%o, R=%o\n", count2, Q2test, P_test, R_test;
                end if;
            end for;
        end for;
    end for;
end for; end for; end for;
end for; end for; end for;

printf "Total i-conjugate decompositions mod %o: %o\n", p2, count2;

// === Now use p=13 with guided search (only Q2 with small structure) ===
printf "\n=== F_13 guided search ===\n";
// Only search Q2 = linear combinations of A, B, D (reduces to 13^3)
printf "Searching Q2 = aA+bB+cD over F_13 (%o combos)...\n", p^3;

Fpt13<tt13> := PolynomialRing(Fp);
count3 := 0;
same_eta := 0;

for ca in Fp do for cb in Fp do for cc in Fp do
    Q2test := ca*Ap + cb*Bp + cc*Dp;
    g := fpp + Q2test^2;

    g10 := Evaluate(g, [tt13, Fp!1, Fp!0]);
    if Degree(g10) ne 4 then continue; end if;
    facts10 := Factorization(g10);
    has_d2 := false;
    for fa in facts10 do
        if Degree(fa[1]) eq 2 then has_d2 := true; break; end if;
    end for;
    if not has_d2 then continue; end if;

    g01 := Evaluate(g, [tt13, Fp!0, Fp!1]);
    g_0t1 := Evaluate(g, [Fp!0, tt13, Fp!1]);
    if Degree(g01) ne 4 or Degree(g_0t1) ne 4 then continue; end if;
    facts01 := Factorization(g01);
    facts_0t1 := Factorization(g_0t1);

    for fa10 in facts10 do
        if Degree(fa10[1]) ne 2 then continue; end if;
        ax2 := Coefficient(fa10[1], 2);
        axy := Coefficient(fa10[1], 1);
        ay2 := Coefficient(fa10[1], 0);

        for fa01 in facts01 do
            if Degree(fa01[1]) ne 2 then continue; end if;
            if Coefficient(fa01[1], 2) ne ax2 then continue; end if;
            axz := Coefficient(fa01[1], 1);
            az2 := Coefficient(fa01[1], 0);

            for fa_0t1 in facts_0t1 do
                if Degree(fa_0t1[1]) ne 2 then continue; end if;
                if Coefficient(fa_0t1[1], 2) ne ay2 then continue; end if;
                if Coefficient(fa_0t1[1], 0) ne az2 then continue; end if;
                ayz := Coefficient(fa_0t1[1], 1);

                L1 := ax2*xp^2+ay2*yp^2+az2*zp^2+axy*xp*yp+axz*xp*zp+ayz*yp*zp;
                if L1 eq 0 then continue; end if;
                L2_cand := g div L1;
                if g ne L1 * L2_cand then continue; end if;
                if TotalDegree(L2_cand) ne 2 then continue; end if;

                inv2 := (Fp!2)^(-1);
                P_test := (L1+L2_cand) * inv2;
                inv2i := (2*ip)^(-1);
                R_test := (L1-L2_cand) * inv2i;
                if L1 ne P_test + ip*R_test then continue; end if;

                count3 +:= 1;

                // Check same eta
                L1_ff := Evaluate(L1, [elt_t, elt_u, Fp!1]);
                if L1_ff eq 0 then continue; end if;
                D_L1 := Divisor(L1_ff);
                ok_L1, D_half_L1 := HalfDiv(D_L1);
                if not ok_L1 then continue; end if;

                ddiff := D_half_L1 - D_half_w;
                Vt, _ := RiemannRochSpace(ddiff);
                Vt2, _ := RiemannRochSpace(-ddiff);
                is_same := Dimension(Vt) ge 1 or Dimension(Vt2) ge 1;
                if is_same then
                    same_eta +:= 1;
                    printf "MATCH #%o (eta): Q2=%o*A+%o*B+%o*D\n", same_eta, ca, cb, cc;
                    printf "  Q2 = %o\n", Q2test;
                    printf "  P  = %o\n", P_test;
                    printf "  R  = %o\n\n", R_test;
                end if;
            end for;
        end for;
    end for;
end for; end for; end for;

printf "F_13 guided: %o i-decomps, %o with same eta\n", count3, same_eta;

printf "\nDone.\n";
quit;
