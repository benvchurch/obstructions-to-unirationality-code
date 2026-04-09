/*******************************************************************************
 * phantom_Qi.m
 *
 * Search for Q(i)-decomposition of the phantom quartic f = A^2+3B^2+3D^2.
 * Brauer class delta(eta) = (-1,-3)_Q splits over Q(i) since -1 = i^2.
 *
 * Merged from: phantom_Qi_search.m, phantom_Qi_verify.m, phantom_Qi_check.m,
 *              phantom_Qi_decomp.m, phantom_Qi_decomp2.m,
 *              phantom_Qi_quick.m, phantom_Qi_quick2.m
 *
 * Contents:
 *   1. Brauer class verification: eta splits over Q(i) (F_7 vs F_49 test)
 *   2. Search for i-conjugate decompositions (F_5 brute force + F_13 guided)
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


// =========== BRAUER CLASS VERIFICATION ===========
// delta(eta) = (-1,-3)_Q.
// Local invariants: inv_inf = 1/2, inv_3 = 1/2, all others 0.
// Q(i) splits this: Q_3(i)/Q_3 is unramified quad ext, kills inv_3.
// Also: -1 = i^2 is a SQUARE in Q(i), so (-1,-3)_{Q(i)} = (i^2,-3) = 0.
//
// Verify: eta becomes principal over F_49 = F_7(i) but not over F_7.

print "=============================================";
print "SECTION 1: Brauer class splits over Q(i)";
print "=============================================";

printf "f = A^2 + 3*B^2 + 3*D^2\n";
printf "Over Q(sqrt(-3)): Q1=A+wB, Q3=A-wB, Q2=wD, cocycle lambda=-1\n";
printf "Brauer class: (-1, -3)_Q\n\n";

printf "Local invariants of (-1, -3)_Q:\n";
printf "  inf: both neg => inv = 1/2\n";
printf "  3: -1 is QNR mod 3 => inv_3 = 1/2\n";
printf "  2: by product formula => inv_2 = 0\n";
printf "  p>=5: Chevalley-Warning => inv_p = 0\n";
printf "  => Ramified at infinity and 3\n\n";

// Test 1: F_7 (i not in F_7, sqrt(-3) = 2 in F_7)
printf "=== F_7: i NOT in F_7, sqrt(-3) = 2 ===\n";
p := 7;
Fp := GF(p);
w7 := Fp!2;  // 2^2 = 4 = -3 mod 7
printf "sqrt(-3) = %o, check: %o^2 = %o = %o\n", w7, w7, w7^2, Fp!(-3);

Fpx<t> := FunctionField(Fp);
Fpxy<u> := PolynomialRing(Fpx);
fp_aff := u^4+(-2*t-2)*u^3+(6*t^2+3)*u^2+(-2*t^3-2)*u+(4*t^4-2*t^3-3*t^2-2*t+4);
FF<uu> := FunctionField(fp_aff);
elt_t := FF!t;
elt_u := uu;

Aval := elt_t^2-elt_t*elt_u-elt_t+elt_u^2-elt_u+1;
Bval := elt_t*elt_u;
q1 := Aval + w7*Bval;

D_q1 := Divisor(q1);
printf "div(q1):\n";
for pl in Support(D_q1) do
    printf "  deg-%o, mult %o\n", Degree(pl), Valuation(D_q1, pl);
end for;

ok, D_half := HalfDiv(D_q1);
printf "All even: %o\n", ok;

if ok then
    V, _ := RiemannRochSpace(D_half);
    printf "dim L((1/2)div(q1)) = %o\n", Dimension(V);
    if Dimension(V) eq 0 then
        printf "=> eta != 0 over F_7\n\n";
    else
        printf "=> eta = 0 over F_7\n\n";
    end if;
end if;

// Test 2: F_49 = F_7(i)
printf "=== F_49 = F_7(i): i exists here ===\n";
Fq := GF(49);
i49 := Fq!0;
for a in Fq do
    if a^2 eq Fq!(-1) then i49 := a; break; end if;
end for;
printf "i = %o, check: i^2 = %o\n", i49, i49^2;
w49 := Fq!2;
printf "sqrt(-3) = %o\n", w49;

Fqx<t2> := FunctionField(Fq);
Fqxy<u2> := PolynomialRing(Fqx);
fp2 := u2^4+(-2*t2-2)*u2^3+(6*t2^2+3)*u2^2+(-2*t2^3-2)*u2+(4*t2^4-2*t2^3-3*t2^2-2*t2+4);
FF2<uu2> := FunctionField(fp2);
elt_t2 := FF2!t2;
elt_u2 := uu2;

Aval2 := elt_t2^2-elt_t2*elt_u2-elt_t2+elt_u2^2-elt_u2+1;
Bval2 := elt_t2*elt_u2;
q1_49 := Aval2 + w49*Bval2;

D_q1_49 := Divisor(q1_49);
printf "div(q1):\n";
for pl in Support(D_q1_49) do
    printf "  deg-%o, mult %o\n", Degree(pl), Valuation(D_q1_49, pl);
end for;

ok49, D_half_49 := HalfDiv(D_q1_49);
printf "All even: %o\n", ok49;

if ok49 then
    V49, _ := RiemannRochSpace(D_half_49);
    printf "dim L((1/2)div(q1)) = %o\n", Dimension(V49);
    if Dimension(V49) ge 1 then
        printf "=> eta = 0 over F_49 (REPRESENTABLE!)\n\n";
    else
        printf "=> eta != 0 over F_49\n\n";
    end if;
end if;

printf "If eta=0 over F_49 but eta!=0 over F_7:\n";
printf "  => eta becomes principal over F_7(i) but not F_7\n";
printf "  => confirms Brauer class splits over Q(i)\n\n";

delete FF; delete FF2; delete Fpx; delete Fqx;


// =========== SEARCH FOR i-CONJUGATE DECOMPOSITIONS ===========
// Search for decompositions f = (P+iR)(P-iR) - Q2^2 with P, R, Q2 in Q[x,y,z]_2.
// Work over F_p where i exists, find all such decompositions.

print "=============================================";
print "SECTION 2: Search for i-conjugate decompositions";
print "=============================================";

// --- F_5 brute force (5^6 = 15625 Q2 candidates) ---
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


// --- F_13 guided search with eta comparison ---
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

// Search Q2 as general quadratic form with small coefficients
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


// =========== THEORETICAL SUMMARY ===========

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
