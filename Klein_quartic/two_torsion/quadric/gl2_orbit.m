/*******************************************************************************
 * gl2_orbit.m
 *
 * Check: do all decompositions F = Q1*Q3 - Q2^2 over F_p (p = 1 mod 4)
 * form a single orbit under the GL2 action M -> g*M*g^T on the symmetric
 * matrix M = [[Q1,Q2],[Q2,Q3]]?
 *
 * GL2 action on (Q1,Q2,Q3):
 *   Q1' = a^2*Q1 + 2ab*Q2 + b^2*Q3
 *   Q2' = ac*Q1 + (ad+bc)*Q2 + bd*Q3
 *   Q3' = c^2*Q1 + 2cd*Q2 + d^2*Q3
 * Preserves det(M) = Q1*Q3-Q2^2 up to det(g)^2.
 ******************************************************************************/

for p in [5, 13] do
    printf "============================================\n";
    printf "p = %o\n", p;
    printf "============================================\n";
    Fp := GF(p);
    R<x,y,z> := PolynomialRing(Fp, 3);
    F := x^4 + y^4 + z^4;
    im := Sqrt(Fp!-1);
    printf "i = %o\n", im;

    // Check smoothness / factorization of F
    fF := Factorization(F);
    printf "F factors into %o piece(s)\n", #fF;
    for pair in fF do
        printf "  (%o)^%o  deg %o\n", pair[1], pair[2], TotalDegree(pair[1]);
    end for;

    mons := [x^2, y^2, z^2, x*y, x*z, y*z];

    function QtoV(Q)
        return [MonomialCoefficient(Q, m) : m in mons];
    end function;

    // Reference decomposition
    Q1r := x^2 + im*z^2;
    Q2r := im*y^2;
    Q3r := x^2 - im*z^2;
    assert Q1r*Q3r - Q2r^2 eq F;

    v1 := QtoV(Q1r); v2 := QtoV(Q2r); v3 := QtoV(Q3r);

    // Generate GL2 orbit (det(g)^2 = 1)
    orbit_Q2_set := {};
    orbit_count := 0;
    for a in Fp do for b in Fp do for c in Fp do for d in Fp do
        det := a*d - b*c;
        if det eq 0 or det^2 ne Fp!1 then continue; end if;

        nv2 := [a*c*v1[k] + (a*d+b*c)*v2[k] + b*d*v3[k] : k in [1..6]];
        Include(~orbit_Q2_set, nv2);
        orbit_count +:= 1;
    end for; end for; end for; end for;

    printf "GL2 elements with det^2=1: %o\n", orbit_count;
    printf "Distinct Q2 in orbit: %o\n", #orbit_Q2_set;
    printf "|SL2(F_%o)| = %o\n\n", p, p*(p^2-1);

    // Exhaustive search over all Q2
    total := 0;
    in_orb := 0;
    out_orb := 0;

    for a1 in Fp do for a2 in Fp do for a3 in Fp do
    for a4 in Fp do for a5 in Fp do for a6 in Fp do
        Q2 := a1*x^2+a2*y^2+a3*z^2+a4*x*y+a5*x*z+a6*y*z;
        G := F + Q2^2;

        fac := Factorization(G);
        // Collect degree-2 factors with multiplicity 1
        deg2 := [pair : pair in fac | TotalDegree(pair[1]) eq 2];

        is_decomp := false;
        if #deg2 eq 2 and deg2[1][2] eq 1 and deg2[2][2] eq 1 then
            // Check product accounts for full G
            prod := deg2[1][1]*deg2[2][1];
            lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
            if lc*prod eq G then is_decomp := true; end if;
        elif #deg2 eq 1 and deg2[1][2] eq 2 then
            prod := deg2[1][1]^2;
            lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
            if lc*prod eq G then is_decomp := true; end if;
        end if;

        if is_decomp then
            total +:= 1;
            coeffs := [Fp!a1,Fp!a2,Fp!a3,Fp!a4,Fp!a5,Fp!a6];
            if coeffs in orbit_Q2_set then
                in_orb +:= 1;
            else
                out_orb +:= 1;
                if out_orb le 3 then
                    printf "  NOT in orbit: Q2 = %o\n", Q2;
                end if;
            end if;
        end if;
    end for; end for; end for;
    end for; end for; end for;

    printf "Total Q2 giving decomposition: %o\n", total;
    printf "  In orbit: %o\n  Outside orbit: %o\n", in_orb, out_orb;
    printf "SINGLE GL2 ORBIT? %o\n\n", out_orb eq 0;

    // Also check: if F itself factors into two quadrics, those give
    // "degenerate" decompositions (Q2=0)
    zero_vec := [Fp!0 : k in [1..6]];
    if zero_vec in orbit_Q2_set then
        printf "Q2=0 is in the orbit.\n";
    else
        printf "Q2=0 is NOT in the orbit.\n";
        // Check if F factors into two quadrics
        if #[pair : pair in fF | TotalDegree(pair[1]) eq 2] ge 2 then
            printf "  But F does factor into quadrics!\n";
        end if;
    end if;
    printf "\n";
end for;

quit;
