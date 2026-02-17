/*******************************************************************************
 * phantom_Qi_decomp.m
 *
 * Search for Q(i)-conjugate quadric decomposition of the phantom quartic
 *   f = A^2 + 3*B^2 + 3*D^2
 * where A = x^2-xy-xz+y^2-yz+z^2, B = xy, D = x^2-z^2.
 *
 * Want: f = (P+iR)(P-iR) - Q2^2 = P^2+R^2-Q2^2 with P,R,Q2 in Q[x,y,z]_2.
 * (Case Q2' = S+iT with ST=0, taking T=0 case.)
 *
 * Equivalently: P^2 + R^2 = f + Q2^2, search for Q2 s.t. f+Q2^2 = sum of 2 squares.
 ******************************************************************************/

Q := Rationals();
Poly3<x,y,z> := PolynomialRing(Q, 3);

A := x^2-x*y-x*z+y^2-y*z+z^2;
B := x*y;
D := x^2-z^2;
f := A^2 + 3*B^2 + 3*D^2;

printf "f = %o\n\n", f;

// The 15 monomials of degree 4
mons4 := MonomialsOfDegree(Poly3, 4);
mons2 := MonomialsOfDegree(Poly3, 2);

printf "Searching f = P^2+R^2-Q2^2 with P,R,Q2 integer quadratic forms...\n";
printf "Search bound on Q2 coefficients: [-3,3]\n\n";

// Strategy: enumerate Q2, compute g = f + Q2^2, check if g = P^2+R^2
// g is a sum of 2 squares iff it factors over Q(i) as L1*L2 with L2 = conj(L1)
// Over Q(i), g = (P+iR)(P-iR)

// Work over Z[i] modulo a prime to screen candidates
// At p=5 (where i=2): check if f+Q2^2 factors as L*conj(L) mod 5

// Actually, just do a direct search with Magma factorization over Q(i)
Pa<a> := PolynomialRing(Q);
Ki<ii> := NumberField(a^2+1);
P3i<xi,yi,zi> := PolynomialRing(Ki, 3);

fi := Evaluate(f, [xi,yi,zi]);

bound := 3;
found := 0;
for c1 in [-bound..bound] do
for c2 in [-bound..bound] do
for c3 in [-bound..bound] do
for c4 in [-bound..bound] do
for c5 in [-bound..bound] do
for c6 in [-bound..bound] do
    Q2 := c1*x^2+c2*y^2+c3*z^2+c4*x*y+c5*x*z+c6*y*z;
    Q2i := Evaluate(Q2, [xi,yi,zi]);
    g := fi + Q2i^2;  // need g = P^2+R^2 = (P+iR)(P-iR)

    // Over Q(i), factor g = (P+iR)(P-iR)
    // Test: does g factor into two quadrics over Q(i)?
    // Quick screen: evaluate at (t,1,0) and check if quartic in t factors over Q(i)

    // Use polynomial ring over Ki
    Kt<t> := PolynomialRing(Ki);
    g10 := Evaluate(g, [t, Ki!1, Ki!0]);
    if Degree(g10) ne 4 then continue; end if;

    facts := Factorization(g10);
    has_quad := false;
    for fa in facts do
        if Degree(fa[1]) eq 2 then has_quad := true; break; end if;
    end for;
    if not has_quad then continue; end if;

    // Also check (t,0,1)
    g01 := Evaluate(g, [t, Ki!0, Ki!1]);
    if Degree(g01) ne 4 then continue; end if;
    facts01 := Factorization(g01);
    has_quad01 := false;
    for fa in facts01 do
        if Degree(fa[1]) eq 2 then has_quad01 := true; break; end if;
    end for;
    if not has_quad01 then continue; end if;

    // Check (0,t,1)
    g11 := Evaluate(g, [Ki!0, t, Ki!1]);
    if Degree(g11) ne 4 then continue; end if;
    facts11 := Factorization(g11);
    has_quad11 := false;
    for fa in facts11 do
        if Degree(fa[1]) eq 2 then has_quad11 := true; break; end if;
    end for;
    if not has_quad11 then continue; end if;

    // Passed all screens. Try to reconstruct L1 from the three specializations.
    for fa10 in facts do
        if Degree(fa10[1]) ne 2 then continue; end if;
        lc10 := LeadingCoefficient(fa10[1]);
        L10 := fa10[1] / lc10;  // monic
        a_x2 := Ki!1; // after making monic
        a_xy := Coefficient(L10, 1);
        a_y2 := Coefficient(L10, 0);

        for fa01v in facts01 do
            if Degree(fa01v[1]) ne 2 then continue; end if;
            lc01 := LeadingCoefficient(fa01v[1]);
            L01 := fa01v[1] / lc01;
            if Coefficient(L01, 2) ne 1 then continue; end if;
            // L1(t,0,1): x^2 coeff should match
            // L1 = a_x2*x^2 + a_y2*y^2 + a_z2*z^2 + a_xy*xy + a_xz*xz + a_yz*yz
            // L1(t,0,1) = a_x2*t^2 + a_xz*t + a_z2
            // Already set a_x2=1
            a_xz := Coefficient(L01, 1);
            a_z2 := Coefficient(L01, 0);

            for fa11v in facts11 do
                if Degree(fa11v[1]) ne 2 then continue; end if;
                lc11 := LeadingCoefficient(fa11v[1]);
                L11 := fa11v[1] / lc11;
                // L1(0,t,1) = a_y2*t^2 + a_yz*t + a_z2
                if Coefficient(L11, 2) ne a_y2 then continue; end if;
                if Coefficient(L11, 0) ne a_z2 then continue; end if;
                a_yz := Coefficient(L11, 1);

                // Reconstruct L1 (monic in x^2)
                L1 := xi^2 + a_y2*yi^2 + a_z2*zi^2 + a_xy*xi*yi + a_xz*xi*zi + a_yz*yi*zi;

                // Scale: L1 should have leading coefficient lc10 for g(t,1,0) match
                L1_scaled := lc10 * L1;

                // Check if g / L1_scaled is a polynomial
                // Magma can check this in the polynomial ring
                if L1_scaled eq P3i!0 then continue; end if;

                // Direct check: compute L2 = g / L1_scaled
                // Since Magma's multivariate division is exact for our purpose,
                // multiply out and compare

                // Actually, let's just check numerically
                // Evaluate at several points and see if L1_scaled divides g
                test_ok := true;
                for xv in [Ki!1, Ki!2, Ki!(-1)] do
                for yv in [Ki!1, Ki!(-1), Ki!2] do
                for zv in [Ki!1, Ki!2, Ki!(-1)] do
                    gv := Evaluate(g, [xv,yv,zv]);
                    l1v := Evaluate(L1_scaled, [xv,yv,zv]);
                    if l1v ne 0 then
                        qv := gv / l1v;
                        // Check qv is consistent with a quadratic form
                    end if;
                end for; end for; end for;

                // Better: verify g - L1_scaled * L2_candidate = 0
                // Compute L2 from g(t,1,0)/L10 etc.
                L2_10 := g10 / (lc10 * L10);
                if Degree(L2_10) ne 2 then continue; end if;
                lc2 := LeadingCoefficient(L2_10);
                L2_10n := L2_10 / lc2;
                b_x2 := lc2;
                b_xy := Coefficient(L2_10n, 1) * lc2;
                // Wait this is getting messy with scaling. Let me just check directly.

                b_y2 := Coefficient(L2_10, 0);
                b_xy_raw := Coefficient(L2_10, 1);

                L2_01_needed := g01 / (lc10 * (a_z2 + a_xz*t + t^2));
                // Hmm, this doesn't work cleanly.

                // Let me use exact polynomial division
                L2_cand := b_x2*xi^2 + b_y2*yi^2;  // incomplete

                break;  // give up on this triple
            end for;
            break;  // simplify
        end for;
        break;
    end for;

end for;
end for;
end for;
end for;
end for;
end for;

// Better approach: work over F_p for p with i in F_p
// Use F_5 (i=2), F_13 (i=5), F_17 (i=4)
// Search all decompositions f = L1*L2 - Q2^2 over F_p
// with L2 = conj_i(L1), and check which give eta

printf "\n=== Approach 2: Search over F_p ===\n";

for p in [17] do  // 17 = 1 mod 4, good reduction
    Fp := GF(p);
    // Find i in F_p
    ip := Fp!0;
    for a in Fp do if a^2 eq Fp!(-1) then ip := a; break; end if; end for;
    printf "p=%o: i=%o\n", p, ip;

    // Also check sqrt(-3)
    wp := Fp!0;
    has_w := false;
    for a in Fp do if a^2 eq Fp!(-3) then wp := a; has_w := true; break; end if; end for;
    printf "  sqrt(-3) exists: %o", has_w;
    if has_w then printf " = %o", wp; end if;
    printf "\n";

    P2<X,Y,Z> := ProjectiveSpace(Fp, 2);
    fp := Evaluate(f, [X,Y,Z]);
    Cp := Curve(P2, fp);
    if not IsNonsingular(Cp) then printf "  BAD reduction\n"; continue; end if;

    P3p<xp,yp,zp> := PolynomialRing(Fp, 3);
    fpp := Evaluate(f, [xp,yp,zp]);

    // Function field
    Fpx<t> := FunctionField(Fp);
    Fpxy<u> := PolynomialRing(Fpx);
    fp_aff := Evaluate(fpp, [t, u, Fp!1]);
    FF<uu> := FunctionField(fp_aff);
    elt_t := FF!t;
    elt_u := uu;

    // Known eta from Q(sqrt(-3)) decomposition (if sqrt(-3) exists)
    if has_w then
        Aval := elt_t^2-elt_t*elt_u-elt_t+elt_u^2-elt_u+1;
        Bval := elt_t*elt_u;
        q1_w := Aval + wp*Bval;

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
        ok_w, D_half_w := HalfDiv(D_q1w);
        printf "  Known eta (sqrt(-3) decomp): defined=%o\n", ok_w;
    end if;

    // Search i-conjugate decompositions: Q2 over F_p, Q1 = P+iR
    // f + Q2^2 = Q1*Q3 = (P+iR)(P-iR) = P^2+R^2
    // Over F_p: P^2+R^2 = (P+ip*R)(P-ip*R)

    count := 0;
    same_class := 0;
    Fpt<tt> := PolynomialRing(Fp);
    mons := [xp^2, yp^2, zp^2, xp*yp, xp*zp, yp*zp];

    for c1 in Fp do for c2 in Fp do for c3 in Fp do
    for c4 in Fp do for c5 in Fp do for c6 in Fp do
        Q2test := c1*xp^2+c2*yp^2+c3*zp^2+c4*xp*yp+c5*xp*zp+c6*yp*zp;
        g := fpp + Q2test^2;

        // Factor g(t,1,0) over F_p
        g10 := Evaluate(g, [tt, Fp!1, Fp!0]);
        if Degree(g10) ne 4 then continue; end if;
        facts10 := Factorization(g10);

        for fa in facts10 do
            if Degree(fa[1]) ne 2 then continue; end if;

            // L1(t,1,0) = fa[1] (a quadratic in t)
            ax2 := Coefficient(fa[1], 2);
            axy := Coefficient(fa[1], 1);
            ay2 := Coefficient(fa[1], 0);

            // Factor g(t,0,1) and g(0,t,1)
            g01 := Evaluate(g, [tt, Fp!0, Fp!1]);
            if Degree(g01) ne 4 then continue fa; end if;
            facts01 := Factorization(g01);

            g11 := Evaluate(g, [Fp!0, tt, Fp!1]);
            if Degree(g11) ne 4 then continue fa; end if;
            facts11 := Factorization(g11);

            for fa01 in facts01 do
                if Degree(fa01[1]) ne 2 then continue; end if;
                if Coefficient(fa01[1], 2) ne ax2 then continue; end if;
                axz := Coefficient(fa01[1], 1);
                az2 := Coefficient(fa01[1], 0);

                for fa11 in facts11 do
                    if Degree(fa11[1]) ne 2 then continue; end if;
                    if Coefficient(fa11[1], 2) ne ay2 then continue; end if;
                    if Coefficient(fa11[1], 0) ne az2 then continue; end if;
                    ayz := Coefficient(fa11[1], 1);

                    L1 := ax2*xp^2+ay2*yp^2+az2*zp^2+axy*xp*yp+axz*xp*zp+ayz*yp*zp;
                    if L1 eq 0 then continue; end if;

                    // Check g = L1 * L2 exactly
                    rem := g - L1 * (g div L1);
                    if rem ne 0 then continue; end if;
                    L2 := g div L1;
                    if TotalDegree(L2) ne 2 then continue; end if;

                    // Check L2 = conj_i(L1): L1 = P+iR, L2 = P-iR
                    // C = (L1+L2)/2, E = (L1-L2)/(2*ip)
                    Lsum := L1+L2;
                    Ldiff := L1-L2;

                    // Check 2 | Lsum and 2*ip | Ldiff coefficient-wise
                    inv2 := (Fp!2)^(-1);
                    P_test := Lsum * inv2;
                    inv2i := (2*ip)^(-1);
                    R_test := Ldiff * inv2i;

                    // Verify: L1 = P_test + ip*R_test
                    if L1 ne P_test + ip*R_test then continue; end if;
                    // Verify: L2 = P_test - ip*R_test
                    if L2 ne P_test - ip*R_test then continue; end if;

                    count +:= 1;

                    // Check same eta class (if sqrt(-3) available)
                    if has_w and ok_w then
                        L1_ff := Evaluate(L1, [elt_t, elt_u, Fp!1]);
                        if L1_ff eq 0 then continue; end if;
                        D_L1 := Divisor(L1_ff);
                        ok_L1, D_half_L1 := HalfDiv(D_L1);
                        if ok_L1 then
                            ddiff := D_half_L1 - D_half_w;
                            Vt, _ := RiemannRochSpace(ddiff);
                            Vt2, _ := RiemannRochSpace(-ddiff);
                            if Dimension(Vt) ge 1 or Dimension(Vt2) ge 1 then
                                same_class +:= 1;
                                if same_class le 10 then
                                    printf "  MATCH #%o:\n", same_class;
                                    printf "    Q2 = %o\n", Q2test;
                                    printf "    L1 = %o\n", L1;
                                    printf "    L2 = %o\n", L2;
                                    printf "    P  = %o\n", P_test;
                                    printf "    R  = %o\n", R_test;
                                end if;
                            end if;
                        end if;
                    end if;
                end for;
            end for;
        end for;
    end for; end for; end for;
    end for; end for; end for;

    printf "  Total i-conjugate decompositions: %o\n", count;
    printf "  Same eta class: %o\n\n", same_class;
end for;

printf "Done.\n";
quit;
