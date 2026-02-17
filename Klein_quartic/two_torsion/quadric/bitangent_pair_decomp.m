/*******************************************************************************
 * bitangent_pair_decomp.m
 *
 * Strategy: set Q1 = l_i * l_j (product of two rational bitangent lines).
 * Find all quadrics through the 4 tangency points, parametrize Q2 from that
 * 2-dim space, and check the divisibility condition F + Q2^2 ≡ 0 mod Q1.
 ******************************************************************************/

R<x,y,z> := PolynomialRing(Rationals(), 3);
F := x^4 + y^4 + z^4;

lines := [x+y+z, x+y-z, x-y+z, x-y-z];
names := ["x+y+z", "x+y-z", "x-y+z", "x-y-z"];

printf "=== BITANGENT PAIR DECOMPOSITIONS FOR x^4+y^4+z^4 ===\n\n";

// Helper: restrict a polynomial to a line l=0 by eliminating a variable
function RestrictToLine(poly, lin)
    cx := MonomialCoefficient(lin, x);
    cy := MonomialCoefficient(lin, y);
    cz := MonomialCoefficient(lin, z);
    if cz ne 0 then
        return Evaluate(poly, [x, y, -(cx*x + cy*y)/cz]);
    elif cy ne 0 then
        return Evaluate(poly, [x, -(cx*x + cz*z)/cy, z]);
    else
        return Evaluate(poly, [-(cy*y + cz*z)/cx, y, z]);
    end if;
end function;

for i in [1..4] do for j in [i+1..4] do
    l1 := lines[i]; l2 := lines[j];
    Q1 := l1 * l2;
    printf "--- Pair (%o, %o) ---\n", names[i], names[j];
    printf "Q1 = %o\n", Q1;

    // Tangency: F restricted to l=0, then factored
    F_on_l1 := RestrictToLine(F, l1);
    F_on_l2 := RestrictToLine(F, l2);

    // Print the actual value (including the factor of 2)
    printf "  F|_{%o=0} = %o\n", names[i], F_on_l1;
    printf "  F|_{%o=0} = %o\n", names[j], F_on_l2;

    // Factor to find tangency quadratics
    fac1 := Factorization(F_on_l1);
    t1 := R!0;
    c1 := Rationals()!1;
    for pair in fac1 do
        if TotalDegree(pair[1]) eq 2 and pair[2] eq 2 then
            t1 := pair[1];
            c1 := LeadingCoefficient(F_on_l1) / LeadingCoefficient(t1^2);
        end if;
    end for;
    printf "  So F|_{l_%o=0} = %o * (%o)^2\n", i, c1, t1;

    fac2 := Factorization(F_on_l2);
    t2 := R!0;
    c2 := Rationals()!1;
    for pair in fac2 do
        if TotalDegree(pair[1]) eq 2 and pair[2] eq 2 then
            t2 := pair[1];
            c2 := LeadingCoefficient(F_on_l2) / LeadingCoefficient(t2^2);
        end if;
    end for;
    printf "  So F|_{l_%o=0} = %o * (%o)^2\n", j, c2, t2;

    // =====================================================================
    // Find 2-dim space of quadrics through 4 tangency points.
    // q ∈ (l_k, t_k) at degree 2 iff q = (linear)*l_k + (scalar)*t_k.
    // Intersection (l1,t1) ∩ (l2,t2) at degree 2.
    // =====================================================================
    mons := [x^2, y^2, z^2, x*y, x*z, y*z];
    gens1 := [x*l1, y*l1, z*l1, t1];
    gens2 := [x*l2, y*l2, z*l2, t2];

    V := VectorSpace(Rationals(), 6);
    S1 := sub<V | [V![MonomialCoefficient(g, m) : m in mons] : g in gens1]>;
    S2 := sub<V | [V![MonomialCoefficient(g, m) : m in mons] : g in gens2]>;
    S := S1 meet S2;
    printf "  Quadric space dim = %o\n", Dimension(S);

    basis_quads := [];
    for k in [1..Dimension(S)] do
        v := Basis(S)[k];
        q := &+[v[m] * mons[m] : m in [1..6]];
        Append(~basis_quads, q);
        printf "    q_%o = %o\n", k, q;
    end for;

    // =====================================================================
    // Key analysis: on Q1=0 (i.e., on l1=0 ∪ l2=0), compute restrictions.
    //
    // Q2 = alpha*q_1 + beta*q_2.  On l_k=0:
    //   Q2|_{l_k} = alpha*r_{k,1}*t_k + beta*r_{k,2}*t_k = (alpha*r1 + beta*r2)*t_k
    //   F|_{l_k} = c_k * t_k^2
    // So (F+Q2^2)|_{l_k} = c_k*t_k^2 + (alpha*r1+beta*r2)^2*t_k^2
    //                     = [c_k + (alpha*r1+beta*r2)^2] * t_k^2
    // For this to vanish: (alpha*r1+beta*r2)^2 = -c_k
    // =====================================================================

    printf "  Restrictions:\n";
    for k in [1..#basis_quads] do
        q := basis_quads[k];
        q_on_l1 := RestrictToLine(q, l1);
        q_on_l2 := RestrictToLine(q, l2);

        // Compute ratio q|_{l}/t|_{l}
        // They should be proportional (both degree 2, vanish at same 2 points)
        if t1 ne 0 then
            t1_on_l1 := RestrictToLine(t1, l1);
            if t1_on_l1 ne 0 then
                ratio1 := LeadingCoefficient(q_on_l1) / LeadingCoefficient(t1_on_l1);
                printf "    q_%o|_{l_%o} / t_%o|_{l_%o} = %o\n", k, i, i, i, ratio1;
            end if;
        end if;
        if t2 ne 0 then
            t2_on_l2 := RestrictToLine(t2, l2);
            if t2_on_l2 ne 0 then
                ratio2 := LeadingCoefficient(q_on_l2) / LeadingCoefficient(t2_on_l2);
                printf "    q_%o|_{l_%o} / t_%o|_{l_%o} = %o\n", k, j, j, j, ratio2;
            end if;
        end if;
    end for;

    // Compute the condition: (alpha*r1 + beta*r2)^2 = -c on each line
    // Extract ratios for each basis quad on each line
    r := [];
    for k in [1..#basis_quads] do
        q := basis_quads[k];
        q_on_l1 := RestrictToLine(q, l1);
        t1_on_l1 := RestrictToLine(t1, l1);
        r1k := LeadingCoefficient(q_on_l1) / LeadingCoefficient(t1_on_l1);
        Append(~r, r1k);
    end for;

    printf "  Condition on l_%o: (", i;
    for k in [1..#r] do
        if k gt 1 then printf " + "; end if;
        if r[k] eq 1 then
            printf "alpha_%o", k;
        else
            printf "%o*alpha_%o", r[k], k;
        end if;
    end for;
    printf ")^2 = %o\n", -c1;

    // Check on l2 as well
    r2_list := [];
    for k in [1..#basis_quads] do
        q := basis_quads[k];
        q_on_l2 := RestrictToLine(q, l2);
        t2_on_l2 := RestrictToLine(t2, l2);
        r2k := LeadingCoefficient(q_on_l2) / LeadingCoefficient(t2_on_l2);
        Append(~r2_list, r2k);
    end for;

    printf "  Condition on l_%o: (", j;
    for k in [1..#r2_list] do
        if k gt 1 then printf " + "; end if;
        if r2_list[k] eq 1 then
            printf "alpha_%o", k;
        else
            printf "%o*alpha_%o", r2_list[k], k;
        end if;
    end for;
    printf ")^2 = %o\n", -c2;

    // Check if -c1 (or -c2) is a rational square
    is_sq := IsSquare(Rationals()!(-c1));
    printf "  Is %o a rational square? %o\n", -c1, is_sq;

    printf "\n";
end for; end for;

// =========================================================================
// Summary
// =========================================================================
printf "=== SUMMARY ===\n";
printf "For ALL pairs of Q-rational bitangent lines of x^4+y^4+z^4:\n";
printf "  F|_{l=0} = 2*(tangency)^2 for every bitangent line l.\n";
printf "  The divisibility condition requires (linear combo)^2 = -2.\n";
printf "  -2 is NOT a rational square => no rational decomposition exists\n";
printf "  with Q1 = product of two rational bitangent lines.\n";

quit;
