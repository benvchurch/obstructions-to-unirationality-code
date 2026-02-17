/*******************************************************************************
 * phantom_Qi_quick2.m
 *
 * Search for i-conjugate decompositions of f = A^2+3B^2+3D^2
 * over F_5 (brute force, 5^6 = 15625 candidates) and F_13 (guided).
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

// === F_5 brute force ===
printf "=== F_5 brute force (5^6 = 15625 Q2 candidates) ===\n";
p := 5;
Fp := GF(p);
ip := Fp!2;  // 2^2=4=-1 mod 5
printf "i=%o (i^2=%o)\n", ip, ip^2;

P2_5<X5,Y5,Z5> := ProjectiveSpace(Fp, 2);
C5 := Curve(P2_5, Evaluate(f,[X5,Y5,Z5]));
printf "Smooth: %o\n", IsNonsingular(C5);

P3p<xp,yp,zp> := PolynomialRing(Fp, 3);
fpp := Evaluate(f, [xp,yp,zp]);

Fpt<tt> := PolynomialRing(Fp);
count := 0;

for c1 in Fp do for c2 in Fp do for c3 in Fp do
for c4 in Fp do for c5v in Fp do for c6 in Fp do
    Q2test := c1*xp^2+c2*yp^2+c3*zp^2+c4*xp*yp+c5v*xp*zp+c6*yp*zp;
    g := fpp + Q2test^2;

    g10 := Evaluate(g, [tt, Fp!1, Fp!0]);
    if Degree(g10) ne 4 then continue; end if;
    facts10 := Factorization(g10);
    has_d2 := false;
    for fa in facts10 do
        if Degree(fa[1]) eq 2 then has_d2 := true; break; end if;
    end for;
    if not has_d2 then continue; end if;

    g01 := Evaluate(g, [tt, Fp!0, Fp!1]);
    g_0t1 := Evaluate(g, [Fp!0, tt, Fp!1]);
    if Degree(g01) lt 3 or Degree(g_0t1) lt 3 then continue; end if;
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
                divok, L2_cand := IsDivisibleBy(g, L1);
                if not divok then continue; end if;
                if TotalDegree(L2_cand) ne 2 then continue; end if;

                // Check i-conjugacy
                inv2 := (Fp!2)^(-1);
                P_test := (L1+L2_cand) * inv2;
                inv2i := (2*ip)^(-1);
                R_test := (L1-L2_cand) * inv2i;
                if L1 ne P_test + ip*R_test then continue; end if;

                count +:= 1;
                if count le 10 then
                    printf "  #%o: Q2=%o\n    P=%o, R=%o\n", count, Q2test, P_test, R_test;
                end if;
            end for;
        end for;
    end for;
end for; end for; end for;
end for; end for; end for;

printf "Total i-conjugate decompositions mod 5: %o\n\n", count;

// === F_13 guided search: Q2 = linear combo of simple forms ===
printf "=== F_13 guided search ===\n";
p2 := 13;
Fp2 := GF(p2);
ip2 := Fp2!5;
wp2 := Fp2!7;
printf "i=%o, sqrt(-3)=%o\n", ip2, wp2;

P3p2<xp2,yp2,zp2> := PolynomialRing(Fp2, 3);
fpp2 := Evaluate(f, [xp2,yp2,zp2]);
Ap2 := Evaluate(A, [xp2,yp2,zp2]);
Bp2 := Evaluate(B, [xp2,yp2,zp2]);
Dp2 := Evaluate(D, [xp2,yp2,zp2]);

// Function field for eta comparison
Fp2x<t2> := FunctionField(Fp2);
Fp2y<u2> := PolynomialRing(Fp2x);
fp2_aff := Evaluate(fpp2, [t2, u2, Fp2!1]);
FF2<uu2> := FunctionField(fp2_aff);
elt_t2 := FF2!t2;
elt_u2 := uu2;

Aval := elt_t2^2-elt_t2*elt_u2-elt_t2+elt_u2^2-elt_u2+1;
Bval := elt_t2*elt_u2;
q1_w := Aval + wp2*Bval;
D_q1w := Divisor(q1_w);
ok_w, D_half_w := HalfDiv(D_q1w);
printf "Known eta: %o\n", ok_w;

// Search Q2 as general quadratic form over F_13
// This is 13^6 ~ 4.8M, too slow.
// Instead search structured Q2: combinations of x^2, y^2, z^2, xy, xz, yz
// with coefficients in {0, +-1, +-2}
printf "Structured search: coefficients in {0,+-1,+-2,+-3}...\n";

Fp2t<tt2> := PolynomialRing(Fp2);
count2 := 0;
same_eta := 0;
coeffs := [Fp2!c : c in [-3..3]];

for c1 in coeffs do for c2 in coeffs do for c3 in coeffs do
for c4 in coeffs do for c5v in coeffs do for c6 in coeffs do
    Q2test := c1*xp2^2+c2*yp2^2+c3*zp2^2+c4*xp2*yp2+c5v*xp2*zp2+c6*yp2*zp2;
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
    if Degree(g01) lt 3 or Degree(g_0t1) lt 3 then continue; end if;
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
                divok2, L2_cand := IsDivisibleBy(g, L1);
                if not divok2 then continue; end if;
                if TotalDegree(L2_cand) ne 2 then continue; end if;

                inv2 := (Fp2!2)^(-1);
                P_test := (L1+L2_cand) * inv2;
                inv2i := (2*ip2)^(-1);
                R_test := (L1-L2_cand) * inv2i;
                if L1 ne P_test + ip2*R_test then continue; end if;

                count2 +:= 1;

                // Check same eta
                L1_ff := Evaluate(L1, [elt_t2, elt_u2, Fp2!1]);
                if L1_ff eq 0 then continue; end if;
                D_L1 := Divisor(L1_ff);
                ok_L1, D_half_L1 := HalfDiv(D_L1);
                if not ok_L1 then continue; end if;

                ddiff := D_half_L1 - D_half_w;
                Vt, _ := RiemannRochSpace(ddiff);
                Vt2, _ := RiemannRochSpace(-ddiff);
                if Dimension(Vt) ge 1 or Dimension(Vt2) ge 1 then
                    same_eta +:= 1;
                    if same_eta le 10 then
                        printf "MATCH #%o:\n", same_eta;
                        printf "  Q2 = %o\n", Q2test;
                        printf "  P  = %o\n", P_test;
                        printf "  R  = %o\n\n", R_test;
                    end if;
                end if;
            end for;
        end for;
    end for;
end for; end for; end for;
end for; end for; end for;

printf "F_13 structured: %o i-decomps, %o with same eta\n\n", count2, same_eta;

// === Summary ===
printf "=== THEORETICAL ANALYSIS ===\n";
printf "Brauer class: (-1,-3)_Q, ramified at inf and 3\n";
printf "Over Q(i): -1 = i^2 is a SQUARE, so (-1,-3)_{Q(i)} = (i^2,-3) = 0\n";
printf "Therefore eta IS representable over Q(i)\n";
printf "The conic -x^2-3y^2=z^2 has solution (x,y,z)=(i,0,1) over Q(i)\n";
printf "This splitting does NOT require sqrt(-3) — it works because i^2 = -1\n\n";
printf "Comparison with Fermat quartic:\n";
printf "  Fermat: delta(eta) = (-2/3,-3) = (-1,-1), ramified at inf and 2\n";
printf "  Phantom: delta(eta) = (-1,-3), ramified at inf and 3\n";
printf "  Both split over Q(i), but for different reasons:\n";
printf "    Fermat: 2 ramifies in Q(i), killing inv_2\n";
printf "    Phantom: -1 is a square in Q(i), killing the whole class\n";

printf "\nDone.\n";
quit;
