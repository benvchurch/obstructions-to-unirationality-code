/*******************************************************************************
 * ss_jacobian.m
 *
 * For each of the three quartics:
 *   1. Compute L-polynomials at small primes to determine the Jacobian
 *      decomposition (factor L(t) over Q).
 *   2. Once the elliptic factors are identified, use them to efficiently
 *      compute ss primes of J up to BOUND.
 *   3. Cross-reference Jacobian ss primes with Prym elliptic-curve ss primes.
 ******************************************************************************/

SetColumns(0);
BOUND := 10000;
SMALL_BOUND := 500;  // for L-poly sampling

// =====================================================================
// IsSupersingularLPoly: check from L-polynomial coefficients
// =====================================================================
function IsSupersingularLPoly(Lpoly, p)
    coeffs := Coefficients(Lpoly);
    a1 := coeffs[2];
    a2 := coeffs[3];
    a3 := coeffs[4];
    return (a1 mod p eq 0) and (a2 mod p eq 0) and (a3 mod (p^2) eq 0);
end function;

// =====================================================================
// SSPrimes for elliptic j-classes
// =====================================================================
function ClearDenominators(f)
    coeffs := Coefficients(f);
    denoms := [Denominator(c) : c in coeffs];
    L := LCM(denoms);
    R := PolynomialRing(Integers());
    return R ! [Integers() ! (c * L) : c in coeffs];
end function;

function SSPrimesElliptic(m_poly, BOUND)
    ss := {};
    lc := LeadingCoefficient(m_poly);
    for p in PrimesInInterval(5, BOUND) do
        if lc mod p eq 0 then continue; end if;
        Fp := GF(p);
        Rp<tp> := PolynomialRing(Fp);
        mp := Rp ! [Fp ! (Integers() ! c) : c in Coefficients(m_poly)];
        roots := Roots(mp);
        for pair in roots do
            j0 := pair[1];
            if j0 eq Fp ! 0 then
                if p mod 3 eq 2 then Include(~ss, p); end if;
                continue;
            end if;
            if j0 eq Fp ! 1728 then
                if p mod 4 eq 3 then Include(~ss, p); end if;
                continue;
            end if;
            E := EllipticCurveWithjInvariant(j0);
            ap := p + 1 - #E;
            if ap eq 0 then
                Include(~ss, p);
                break;
            end if;
        end for;
    end for;
    return ss;
end function;

// =====================================================================
// Phase 1: L-polynomial sampling at small primes
// =====================================================================
procedure SampleLPolys(label, F_form)
    printf "\n%o\n%o\n%o\n", "=" ^ 70, label, "=" ^ 70;

    QQ := Rationals();
    RQ<xq,yq,zq> := PolynomialRing(QQ, 3);
    F_poly := Evaluate(F_form, [xq, yq, zq]);

    printf "\nL-polynomial factorizations at small primes:\n";
    for p in PrimesInInterval(5, SMALL_BOUND) do
        Fp := GF(p);
        P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
        fp := Evaluate(F_poly, [xp, yp, zp]);
        Cp := Curve(P2p, fp);
        if not IsNonsingular(Cp) then
            printf "  p=%o: SINGULAR\n", p;
            continue;
        end if;
        Lp := Numerator(ZetaFunction(Cp));
        fac := Factorization(Lp);

        // Print factorization
        printf "  p=%o: ", p;
        for i in [1..#fac] do
            if i gt 1 then printf " * "; end if;
            if fac[i][2] gt 1 then
                printf "(%o)^%o", fac[i][1], fac[i][2];
            else
                printf "(%o)", fac[i][1];
            end if;
        end for;
        if IsSupersingularLPoly(Lp, p) then printf "  [SS]"; end if;
        printf "\n";

        // For degree-2 factors, identify the elliptic curve
        for f in fac do
            if Degree(f[1]) eq 2 then
                coeffs_f := Coefficients(f[1]);
                // L_E(t) = 1 + a_p*t + p*t^2
                a_p_ell := coeffs_f[2];
                E := EllipticCurveWithjInvariant(GF(p)!0);  // placeholder
                // Try to identify via a_p
                printf "        deg-2 factor: a_p=%o", a_p_ell;
                if f[2] gt 1 then printf " (mult %o)", f[2]; end if;
                printf "\n";
            end if;
        end for;
    end for;
end procedure;

// =====================================================================
// Phase 2: Full analysis using known Jacobian decompositions
// =====================================================================
procedure AnalyzeWithDecomposition(label, elliptic_factors, ell_labels, j_polys, j_labels)
    printf "\n%o\n%o -- Jacobian decomposition analysis\n%o\n",
        "=" ^ 70, label, "=" ^ 70;

    PQ<t> := PolynomialRing(Rationals());
    n_ell := #elliptic_factors;
    printf "\nJacobian ~ ";
    for i in [1..n_ell] do
        if i gt 1 then printf " x "; end if;
        printf "%o", ell_labels[i];
    end for;
    printf "\n";

    // Compute ss primes for each Jacobian factor
    jac_ss_sets := [];
    for i in [1..n_ell] do
        m_int := ClearDenominators(elliptic_factors[i]);
        ss := SSPrimesElliptic(m_int, BOUND);
        Append(~jac_ss_sets, ss);
        printf "\n  Jac factor [%o] %o: %o ss primes up to %o\n",
            i, ell_labels[i], #ss, BOUND;
        if #ss le 30 then
            printf "    primes: %o\n", Sort(Setseq(ss));
        else
            sorted := Sort(Setseq(ss));
            printf "    first 20: %o ...\n", sorted[1..20];
        end if;
    end for;

    // Jacobian is ss iff ALL factors are ss
    ss_jac := jac_ss_sets[1];
    for i in [2..n_ell] do
        ss_jac := ss_jac meet jac_ss_sets[i];
    end for;
    printf "\nJacobian supersingular primes (all factors ss): %o\n", #ss_jac;
    if #ss_jac le 50 then
        printf "  primes: %o\n", Sort(Setseq(ss_jac));
    end if;

    // ss primes where ANY factor is ss
    ss_any := jac_ss_sets[1];
    for i in [2..n_ell] do
        ss_any := ss_any join jac_ss_sets[i];
    end for;
    printf "Primes where at least one Jac factor is ss: %o\n", #ss_any;

    // Cross-reference with Prym elliptic curves
    printf "\n--- Cross-reference: Prym elliptic curves vs Jacobian factors ---\n";
    n_prym := #j_polys;
    for i in [1..n_prym] do
        m_int := ClearDenominators(j_polys[i]);
        ss_prym := SSPrimesElliptic(m_int, BOUND);

        // vs each Jacobian factor
        printf "\n  Prym [%o] %o (%o ss primes):\n", i, j_labels[i], #ss_prym;
        for j in [1..n_ell] do
            inter := ss_prym meet jac_ss_sets[j];
            printf "    vs Jac[%o] %o: |inter|=%o / |ss(Prym)|=%o",
                j, ell_labels[j], #inter, #ss_prym;
            if #ss_prym gt 0 then
                ratio := 1.0 * #inter / #ss_prym;
                printf "  (%.1o%%)", ratio * 100;
                if ratio gt 0.9 then printf " ***"; end if;
            end if;
            printf "\n";
            if inter eq ss_prym and #ss_prym gt 0 then
                printf "      *** FULL INCLUSION: ss(Prym) ⊂ ss(Jac factor) ***\n";
            end if;
        end for;

        // vs full Jacobian
        inter_jac := ss_prym meet ss_jac;
        inter_any := ss_prym meet ss_any;
        printf "    vs Jac (all ss): |inter|=%o / |ss(Prym)|=%o", #inter_jac, #ss_prym;
        if #ss_prym gt 0 then
            printf "  (%.1o%%)", 1.0 * #inter_jac / #ss_prym * 100;
        end if;
        printf "\n";
        printf "    vs Jac (any ss): |inter|=%o / |ss(Prym)|=%o", #inter_any, #ss_prym;
        if #ss_prym gt 0 then
            printf "  (%.1o%%)", 1.0 * #inter_any / #ss_prym * 100;
        end if;
        printf "\n";
    end for;
end procedure;

// =====================================================================
// Setup
// =====================================================================
QQ := Rationals();
P2Q<x,y,z> := ProjectiveSpace(QQ, 2);
PQ<t> := PolynomialRing(Rationals());

// Quartic equations
klein_F := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
           - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
fermat_F := x^4 + y^4 + z^4;
edge_F := 25*(x^4 + y^4 + z^4) - 34*(x^2*y^2 + x^2*z^2 + y^2*z^2);

// Prym j min polys (from ss_coincidences.m)
klein_prym_polys := [
    t^2 + 13856*t - 26578688,
    t^4 - 103439*t^3 + 6670405329*t^2 + 31128229267744*t + 148381159092130048,
    t^2 + 7184*t + 16777216
];
klein_prym_labels := [
    "Z/3 class 1 (28 cpx)",
    "Z/3 classes 3,4 (14 cpx)",
    "Z/2 class 2 (21 cpx)"
];

fermat_prym_polys := [
    t^4 + 73216*t^3 + 1533640704*t^2 + 6119514701824*t - 15081210455785472,
    t - 8000,
    t - 128
];
fermat_prym_labels := [
    "Z/3 classes 2,3 (32 cpx)",
    "Z/3+Z/2 class 5 (j=8000, CM sqrt-2)",
    "Z/2 class 4 (j=128, D4 curve)"
];

edge_prym_polys := [
    t - 54000,
    t^2 - 775180000/729*t + 40873252000000/6561,
    t^2 - 541157005431/15625*t + 25745806977673041/390625,
    t + 11664/625,
    t - 3538944/25
];
edge_prym_labels := [
    "Z/3+Z/2 class 6 (j=54000, CM sqrt-3)",
    "Z/3 class 7 (4 cpx)",
    "Z/3 class 10 (1 cpx, singleton)",
    "Z/2 class 9 (j=-11664/625)",
    "Z/2 class 9 (j=3538944/25)"
];

// =====================================================================
// Phase 1: Sample L-polys to identify Jacobian decomposition
// =====================================================================
SetOutputFile("results/ss_jacobian.log" : Overwrite := true);

RQ<xq,yq,zq> := PolynomialRing(QQ, 3);
SampleLPolys("KLEIN TWIST", Evaluate(klein_F, [xq,yq,zq]));
SampleLPolys("FERMAT", Evaluate(fermat_F, [xq,yq,zq]));
SampleLPolys("EDGE", Evaluate(edge_F, [xq,yq,zq]));

// =====================================================================
// Phase 2: Known decompositions
//
// Klein twist: J ~ E^3 where E = 49a1 (j = -3375)
// Fermat: J ~ E_1 x E_2 x E_3  -- to be determined from Phase 1
// Edge: to be determined from Phase 1
//
// For now, identify the elliptic factors from the L-poly factorizations.
// We'll extract j-invariants and min polys from the data.
// =====================================================================

// Klein twist: J ~ E^3, E = 49a1 has j = -3375
// Cremona label 49a1: y^2 + x*y = x^3 - x^2 - 2*x - 1, j = -3375
// Actually let's verify: compute j of 49a1
E_49a1 := EllipticCurve("49a1");
printf "\n\n49a1: j = %o, conductor = %o\n", jInvariant(E_49a1), Conductor(E_49a1);
printf "49a1 min eq: %o\n", E_49a1;

klein_jac_polys := [t - jInvariant(E_49a1)];
klein_jac_labels := ["E=49a1 (mult 3)"];

// For Fermat and Edge, we need to identify the factors from the L-poly data.
// Fermat x^4+y^4+z^4: the Jacobian has CM.  The three elliptic factors
// correspond to the three Hecke characters of Q(i).
// Let's identify them by computing a_p for the first few primes and matching
// to known CM curves.

printf "\n--- Identifying Fermat Jacobian factors ---\n";
// Compute L-poly at p=5 and factor
Fp5 := GF(5);
P2_5<x5,y5,z5> := ProjectiveSpace(Fp5, 2);
C5 := Curve(P2_5, x5^4 + y5^4 + z5^4);
L5 := Numerator(ZetaFunction(C5));
printf "Fermat L(t) at p=5: %o\n", L5;
printf "Factored: %o\n", Factorization(L5);

// Try a few more primes to see the pattern
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, xp^4 + yp^4 + zp^4);
    if not IsNonsingular(Cp) then continue; end if;
    Lp := Numerator(ZetaFunction(Cp));
    fac := Factorization(Lp);
    printf "p=%o: %o\n", p, fac;
end for;

// For the Fermat quartic, the Jacobian is isogenous to E_32^3 where
// E_32 has CM by Z[i] and conductor 32.  Let's check:
printf "\n--- Checking CM curves for Fermat ---\n";
// CM by Z[i]: the curves with j=1728
// E: y^2 = x^3 - x, conductor 32
E_cm_i := EllipticCurve([0,0,0,-1,0]);
printf "E(Z[i]): j=%o, cond=%o\n", jInvariant(E_cm_i), Conductor(E_cm_i);

// CM by Z[sqrt(-2)]: j = 8000
E_cm_2 := EllipticCurveWithjInvariant(Rationals()!8000);
printf "E(Z[sqrt(-2)]): j=%o, cond=%o\n", jInvariant(E_cm_2), Conductor(E_cm_2);

// CM by Z[(1+sqrt(-7))/2]: j = -3375
E_cm_7 := EllipticCurveWithjInvariant(Rationals()!(-3375));
printf "E(Z[(1+sqrt(-7))/2]): j=%o, cond=%o\n", jInvariant(E_cm_7), Conductor(E_cm_7);

// Let's compare a_p for Fermat L-poly factors with known CM curves
printf "\n--- Matching Fermat L-poly factors to CM curves ---\n";
printf "%-5o | %-20o | %-10o | %-10o | %-10o\n",
    "p", "L-poly factors", "a_p(j=1728)", "a_p(j=8000)", "a_p(j=-3375)";
for p in [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73] do
    Fp := GF(p);

    // Fermat L-poly
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, xp^4 + yp^4 + zp^4);
    if not IsNonsingular(Cp) then continue; end if;
    Lp := Numerator(ZetaFunction(Cp));
    fac := Factorization(Lp);
    fac_aps := [];
    for f in fac do
        if Degree(f[1]) eq 2 then
            Append(~fac_aps, Coefficients(f[1])[2]);
        end if;
    end for;

    // a_p for CM curves
    E1 := EllipticCurveWithjInvariant(Fp!1728);
    a1 := p + 1 - #E1;
    E2 := EllipticCurveWithjInvariant(Fp!8000);
    a2 := p + 1 - #E2;
    E3 := EllipticCurveWithjInvariant(Fp!(-3375 mod p));
    a3 := p + 1 - #E3;

    printf "p=%-4o | fac a_p=%o | %o | %o | %o\n",
        p, fac_aps, a1, a2, a3;
end for;

// Now do the same for Edge
printf "\n--- Identifying Edge Jacobian factors ---\n";
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp := 25*(xp^4 + yp^4 + zp^4) - 34*(xp^2*yp^2 + xp^2*zp^2 + yp^2*zp^2);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "p=%o: SINGULAR\n", p;
        continue;
    end if;
    Lp := Numerator(ZetaFunction(Cp));
    fac := Factorization(Lp);
    printf "p=%-4o: ", p;
    for i in [1..#fac] do
        if i gt 1 then printf " * "; end if;
        if fac[i][2] gt 1 then
            printf "(%o)^%o", fac[i][1], fac[i][2];
        else
            printf "(%o)", fac[i][1];
        end if;
    end for;
    printf "\n";
    // Extract a_p values
    for f in fac do
        if Degree(f[1]) eq 2 then
            printf "    deg-2 factor: a_p = %o", Coefficients(f[1])[2];
            if f[2] gt 1 then printf " (mult %o)", f[2]; end if;
            printf "\n";
        end if;
    end for;
end for;

// Also compare Edge factors with CM curves
printf "\n--- Matching Edge L-poly factors to CM curves ---\n";
printf "%-5o | %-25o | %-10o | %-10o | %-10o\n",
    "p", "L-poly deg-2 a_p", "a_p(j=54000)", "a_p(j=1728)", "a_p(j=8000)";
for p in [7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp := 25*(xp^4 + yp^4 + zp^4) - 34*(xp^2*yp^2 + xp^2*zp^2 + yp^2*zp^2);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then continue; end if;
    Lp := Numerator(ZetaFunction(Cp));
    fac := Factorization(Lp);
    fac_aps := [];
    for f in fac do
        if Degree(f[1]) eq 2 then
            for rep in [1..f[2]] do
                Append(~fac_aps, Coefficients(f[1])[2]);
            end for;
        end if;
    end for;

    // a_p for candidate CM curves
    a_54000 := p + 1 - #EllipticCurveWithjInvariant(Fp!54000);
    a_1728 := p + 1 - #EllipticCurveWithjInvariant(Fp!1728);
    a_8000 := p + 1 - #EllipticCurveWithjInvariant(Fp!8000);

    printf "p=%-4o | %o | %o | %o | %o\n",
        p, fac_aps, a_54000, a_1728, a_8000;
end for;

UnsetOutputFile();
printf "\nPhase 1 done. Results in results/ss_jacobian.log\n";
printf "Review the factorization patterns to identify Jacobian decompositions,\n";
printf "then Phase 2 will compute full cross-references.\n";
quit;
