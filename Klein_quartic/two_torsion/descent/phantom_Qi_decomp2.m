/*******************************************************************************
 * phantom_Qi_decomp2.m
 *
 * Search over F_p for i-conjugate decompositions f = (P+iR)(P-iR) - Q2^2
 * giving the same eta as the Q(sqrt(-3)) decomposition.
 * Use p = 17 (i and sqrt(-3) both exist).
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

p := 17;  // 17 = 1 mod 4 (i exists) and 17 = 2 mod 3, need -3 to be QR
Fp := GF(p);

// Find i and sqrt(-3)
ip := Fp!0;
for a in Fp do if a^2 eq Fp!(-1) then ip := a; break; end if; end for;
wp := Fp!0;
for a in Fp do if a^2 eq Fp!(-3) then wp := a; break; end if; end for;
printf "p=%o: i=%o (i^2=%o), sqrt(-3)=%o (w^2=%o)\n", p, ip, ip^2, wp, wp^2;

P3p<xp,yp,zp> := PolynomialRing(Fp, 3);
fpp := Evaluate(f, [xp,yp,zp]);

// Function field setup
Fpx<t> := FunctionField(Fp);
Fpxy<u> := PolynomialRing(Fpx);
fp_aff := Evaluate(fpp, [t, u, Fp!1]);
FF<uu> := FunctionField(fp_aff);
elt_t := FF!t;
elt_u := uu;

// Known eta from Q(sqrt(-3)) decomposition
Aval := elt_t^2-elt_t*elt_u-elt_t+elt_u^2-elt_u+1;
Bval := elt_t*elt_u;
q1_w := Aval + wp*Bval;
D_q1w := Divisor(q1_w);
ok_w, D_half_w := HalfDiv(D_q1w);
printf "Known eta defined: %o\n", ok_w;

// Enumerate Q2 over F_p, check if f+Q2^2 factors as L1*L2 with L2=conj_i(L1)
Fpt<tt> := PolynomialRing(Fp);
count := 0;
same_class := 0;

printf "Searching %o^6 = %o Q2 candidates...\n", p, p^6;

for c1 in Fp do for c2 in Fp do for c3 in Fp do
for c4 in Fp do for c5 in Fp do for c6 in Fp do
    Q2test := c1*xp^2+c2*yp^2+c3*zp^2+c4*xp*yp+c5*xp*zp+c6*yp*zp;
    g := fpp + Q2test^2;

    // Factor g(t,1,0) over F_p
    g10 := Evaluate(g, [tt, Fp!1, Fp!0]);
    if Degree(g10) ne 4 then continue; end if;
    facts10 := Factorization(g10);

    // Need a degree-2 factor
    has_d2 := false;
    for fa in facts10 do
        if Degree(fa[1]) eq 2 then has_d2 := true; break; end if;
    end for;
    if not has_d2 then continue; end if;

    // Also check g(t,0,1) and g(0,t,1)
    g01 := Evaluate(g, [tt, Fp!0, Fp!1]);
    g_0t1 := Evaluate(g, [Fp!0, tt, Fp!1]);
    if Degree(g01) ne 4 or Degree(g_0t1) ne 4 then continue; end if;

    facts01 := Factorization(g01);
    facts_0t1 := Factorization(g_0t1);

    // Try to build L1 from compatible factors
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

                // Verify g = L1 * L2 exactly
                L2_cand := g div L1;
                if g ne L1 * L2_cand then continue; end if;
                if TotalDegree(L2_cand) ne 2 then continue; end if;

                // Check i-conjugacy: L2 = P - iR, L1 = P + iR
                // So L1+L2 = 2P (should have coefficients divisible by 2)
                // and L1-L2 = 2iR
                inv2 := (Fp!2)^(-1);
                P_test := (L1+L2_cand) * inv2;
                inv2i := (2*ip)^(-1);
                R_test := (L1-L2_cand) * inv2i;

                if L1 ne P_test + ip*R_test then continue; end if;

                count +:= 1;

                // Check if this gives the same eta
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
                    same_class +:= 1;
                    if same_class le 10 then
                        printf "MATCH #%o:\n", same_class;
                        printf "  Q2 = %o\n", Q2test;
                        printf "  L1 = P+iR = %o\n", L1;
                        printf "  L2 = P-iR = %o\n", L2_cand;
                        printf "  P  = %o\n", P_test;
                        printf "  R  = %o\n\n", R_test;
                    end if;
                end if;
            end for;
        end for;
    end for;

end for; end for; end for;
end for; end for; end for;

printf "Total i-conjugate decompositions: %o\n", count;
printf "Same eta class: %o\n", same_class;

printf "\nDone.\n";
quit;
