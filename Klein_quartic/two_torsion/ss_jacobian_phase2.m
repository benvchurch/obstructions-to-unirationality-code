/*******************************************************************************
 * ss_jacobian_phase2.m
 *
 * Phase 2: Now that we know all three Jacobians are E^3, identify the
 * elliptic factors, compute ss(J) = ss(E) up to BOUND, and cross-reference
 * with Prym elliptic curve ss primes.
 *
 * Key insight: J ss at p iff a_p(E)=0, and for ss detection the quadratic
 * twist doesn't matter (a_p -> -a_p preserves a_p=0).
 ******************************************************************************/

SetColumns(0);
BOUND := 10000;

// =====================================================================
// Helpers (from ss_coincidences.m)
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

// Compute ss primes for an elliptic curve over Q (given as Magma curve)
function SSPrimesFromCurve(E_Q, BOUND)
    ss := {};
    N := Conductor(E_Q);
    for p in PrimesInInterval(5, BOUND) do
        if N mod p eq 0 then continue; end if;  // bad reduction
        ap := TraceOfFrobenius(E_Q, p);
        if ap eq 0 then
            Include(~ss, p);
        end if;
    end for;
    return ss;
end function;

SetOutputFile("results/ss_jacobian.log" : Overwrite := true);

QQ := Rationals();
P2Q<x,y,z> := ProjectiveSpace(QQ, 2);
PQ<t> := PolynomialRing(Rationals());

// =====================================================================
// Step 1: Identify the elliptic factor for each quartic
// =====================================================================
printf "======================================================================\n";
printf "JACOBIAN DECOMPOSITION IDENTIFICATION\n";
printf "======================================================================\n";

// --- Klein twist: E = 49a1, j = -3375 ---
E_klein := EllipticCurve("49a1");
printf "\nKlein twist: J ~ E^3, E = 49a1\n";
printf "  j = %o, conductor = %o\n", jInvariant(E_klein), Conductor(E_klein);
printf "  CM disc = -7 (Z[(1+sqrt(-7))/2])\n";

// --- Fermat: identify the twist of j=1728 ---
// From Phase 1: a_p(Jac) = -a_p(y^2=x^3-x) at all primes p=1 mod 4
// The twist of y^2 = x^3 - x by d is y^2 = x^3 - d^2*x
// This changes a_p to (d/p)*a_p
// We need (d/p) = -1 for all p=1 mod 4 where a_p != 0

// Actually, check: is the Jacobian factor 32a1 or 32a2?
E_32a1 := EllipticCurve("32a1");
E_32a2 := EllipticCurve("32a2");
printf "\nFermat quartic: identifying twist of j=1728\n";
printf "  32a1: %o, j=%o\n", E_32a1, jInvariant(E_32a1);
printf "  32a2: %o, j=%o\n", E_32a2, jInvariant(E_32a2);

// Compare a_p at small primes with the Fermat L-poly factors
printf "\n  Checking a_p match:\n";
printf "  %-5o | %-10o | %-10o | %-10o\n", "p", "Jac factor", "32a1", "32a2";

// Compute Fermat L-polys at small primes
fermat_F := x^4 + y^4 + z^4;
RQ<xq,yq,zq> := PolynomialRing(QQ, 3);
fermat_poly := Evaluate(fermat_F, [xq, yq, zq]);

for p in [5, 11, 13, 17, 23, 29, 37, 41, 53, 61] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, Evaluate(fermat_poly, [xp, yp, zp]));
    if not IsNonsingular(Cp) then continue; end if;
    Lp := Numerator(ZetaFunction(Cp));
    fac := Factorization(Lp);
    ap_jac := Coefficients(fac[1][1])[2];
    ap_1 := TraceOfFrobenius(E_32a1, p);
    ap_2 := TraceOfFrobenius(E_32a2, p);
    printf "  p=%-4o | %-10o | %-10o | %-10o", p, ap_jac, ap_1, ap_2;
    if ap_jac eq ap_1 then printf "  <-- 32a1 match"; end if;
    if ap_jac eq ap_2 then printf "  <-- 32a2 match"; end if;
    printf "\n";
end for;

// --- Edge: identify the non-CM factor ---
// Collect a_p data from Edge L-polys
edge_F := 25*(x^4 + y^4 + z^4) - 34*(x^2*y^2 + x^2*z^2 + y^2*z^2);
edge_poly := Evaluate(edge_F, [xq, yq, zq]);

printf "\nEdge quartic: identifying non-CM factor\n";
printf "  Collecting a_p data...\n";

edge_aps := [];
for p in PrimesInInterval(5, 100) do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, Evaluate(edge_poly, [xp, yp, zp]));
    if not IsNonsingular(Cp) then
        printf "  p=%o: singular\n", p;
        continue;
    end if;
    Lp := Numerator(ZetaFunction(Cp));
    fac := Factorization(Lp);
    ap := Coefficients(fac[1][1])[2];
    Append(~edge_aps, <p, ap>);
end for;

printf "  a_p data: %o\n", edge_aps;

// =====================================================================
// Step 2: Compute ss primes for Jacobian factors
// =====================================================================
printf "\n======================================================================\n";
printf "SUPERSINGULAR PRIME COMPUTATION\n";
printf "======================================================================\n";

// Klein twist
ss_klein_jac := SSPrimesFromCurve(E_klein, BOUND);
printf "\nKlein twist J: %o ss primes up to %o\n", #ss_klein_jac, BOUND;
if #ss_klein_jac le 50 then
    printf "  primes: %o\n", Sort(Setseq(ss_klein_jac));
end if;

// Fermat - use whichever 32a curve matched (we expect j=1728)
// For ss detection, twist doesn't matter, so just use j=1728
E_fermat := EllipticCurve([QQ|0,0,0,-1,0]);  // y^2 = x^3 - x, j=1728
ss_fermat_jac := SSPrimesFromCurve(E_fermat, BOUND);
printf "\nFermat J: %o ss primes up to %o (using j=1728)\n", #ss_fermat_jac, BOUND;
if #ss_fermat_jac le 50 then
    printf "  primes: %o\n", Sort(Setseq(ss_fermat_jac));
else
    sorted := Sort(Setseq(ss_fermat_jac));
    printf "  first 20: %o ...\n", sorted[1..20];
end if;

// Edge - use the identified curve from Cremona if found
E_edge := false;  // will be set if found
// Search Cremona database
printf "\nEdge: searching Cremona database for matching curve...\n";
for N in [1..1000] do
    curves := EllipticCurves(CremonaDatabase(), N);
    for E in curves do
        match := true;
        for pair in edge_aps do
            p := pair[1];
            ap_target := pair[2];
            if N mod p eq 0 then continue; end if;
            ap_E := TraceOfFrobenius(E, p);
            if ap_E ne ap_target and ap_E ne -ap_target then
                match := false;
                break;
            end if;
        end for;
        if match then
            printf "  FOUND: conductor %o, curve %o, j=%o\n", N, CremonaReference(E), jInvariant(E);
            // Check exact vs twist match
            is_exact := true;
            for pair in edge_aps do
                p := pair[1];
                if N mod p eq 0 then continue; end if;
                if TraceOfFrobenius(E, p) ne pair[2] then
                    is_exact := false;
                    break;
                end if;
            end for;
            if is_exact then
                printf "  Exact a_p match (not twist)\n";
            else
                printf "  Twist match\n";
            end if;
            E_edge := E;
            break;
        end if;
    end for;
    if Type(E_edge) ne BoolElt then break; end if;
end for;

ss_edge_jac := {};
if Type(E_edge) ne BoolElt then
    printf "\nEdge J: using identified curve from Cremona\n";
    ss_edge_jac := SSPrimesFromCurve(E_edge, BOUND);
else
    printf "\nEdge: no Cremona match, computing from point counts...\n";
    for p in PrimesInInterval(5, BOUND) do
        Fp := GF(p);
        P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
        Cp := Curve(P2p, Evaluate(edge_poly, [xp, yp, zp]));
        if not IsNonsingular(Cp) then continue; end if;
        Np := #Cp;
        if Np eq (p + 1) then
            Include(~ss_edge_jac, p);
        end if;
    end for;
end if;
printf "Edge J: %o ss primes up to %o\n", #ss_edge_jac, BOUND;
if #ss_edge_jac le 50 then
    printf "  primes: %o\n", Sort(Setseq(ss_edge_jac));
else
    sorted := Sort(Setseq(ss_edge_jac));
    printf "  first 20: %o ...\n", sorted[1..20];
end if;

// =====================================================================
// Step 3: Cross-reference with Prym elliptic curves
// =====================================================================
printf "\n======================================================================\n";
printf "CROSS-REFERENCE: Prym ss primes vs Jacobian ss primes\n";
printf "======================================================================\n";

// --- Klein twist ---
printf "\n--- KLEIN TWIST (J ~ 49a1^3, CM sqrt(-7)) ---\n";
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

for i in [1..#klein_prym_polys] do
    m_int := ClearDenominators(klein_prym_polys[i]);
    ss_prym := SSPrimesElliptic(m_int, BOUND);
    inter := ss_prym meet ss_klein_jac;
    printf "\n  [%o] %o\n", i, klein_prym_labels[i];
    printf "    |ss(E)|=%o, |ss(J)|=%o, |ss(E)∩ss(J)|=%o\n",
        #ss_prym, #ss_klein_jac, #inter;
    if #ss_prym gt 0 then
        ratio := 1.0 * #inter / #ss_prym;
        printf "    Fraction of Prym ss primes that are Jac ss: %.3o\n", ratio;
    end if;
    if ss_prym subset ss_klein_jac and #ss_prym gt 0 then
        printf "    *** ss(Prym) ⊂ ss(Jac) ***\n";
    end if;
    only_prym := ss_prym diff ss_klein_jac;
    if #only_prym gt 0 and #only_prym le 30 then
        printf "    ss(Prym) \\ ss(Jac): %o\n", Sort(Setseq(only_prym));
    end if;
    if #inter gt 0 and #inter le 30 then
        printf "    ss(Prym) ∩ ss(Jac): %o\n", Sort(Setseq(inter));
    end if;
end for;

// --- Fermat ---
printf "\n--- FERMAT (J ~ E^3, j=1728, CM sqrt(-1)) ---\n";
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

for i in [1..#fermat_prym_polys] do
    m_int := ClearDenominators(fermat_prym_polys[i]);
    ss_prym := SSPrimesElliptic(m_int, BOUND);
    inter := ss_prym meet ss_fermat_jac;
    printf "\n  [%o] %o\n", i, fermat_prym_labels[i];
    printf "    |ss(E)|=%o, |ss(J)|=%o, |ss(E)∩ss(J)|=%o\n",
        #ss_prym, #ss_fermat_jac, #inter;
    if #ss_prym gt 0 then
        ratio := 1.0 * #inter / #ss_prym;
        printf "    Fraction of Prym ss primes that are Jac ss: %.3o\n", ratio;
    end if;
    if ss_prym subset ss_fermat_jac and #ss_prym gt 0 then
        printf "    *** ss(Prym) ⊂ ss(Jac) ***\n";
    end if;
    only_prym := ss_prym diff ss_fermat_jac;
    if #only_prym gt 0 and #only_prym le 30 then
        printf "    ss(Prym) \\ ss(Jac): %o\n", Sort(Setseq(only_prym));
    end if;
    if #inter gt 0 and #inter le 30 then
        printf "    ss(Prym) ∩ ss(Jac): %o\n", Sort(Setseq(inter));
    end if;
end for;

// --- Edge ---
printf "\n--- EDGE (J ~ E^3, non-CM) ---\n";
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

for i in [1..#edge_prym_polys] do
    m_int := ClearDenominators(edge_prym_polys[i]);
    ss_prym := SSPrimesElliptic(m_int, BOUND);
    inter := ss_prym meet ss_edge_jac;
    printf "\n  [%o] %o\n", i, edge_prym_labels[i];
    printf "    |ss(E)|=%o, |ss(J)|=%o, |ss(E)∩ss(J)|=%o\n",
        #ss_prym, #ss_edge_jac, #inter;
    if #ss_prym gt 0 then
        ratio := 1.0 * #inter / #ss_prym;
        printf "    Fraction of Prym ss primes that are Jac ss: %.3o\n", ratio;
    end if;
    if ss_prym subset ss_edge_jac and #ss_prym gt 0 then
        printf "    *** ss(Prym) ⊂ ss(Jac) ***\n";
    end if;
    only_prym := ss_prym diff ss_edge_jac;
    if #only_prym gt 0 and #only_prym le 30 then
        printf "    ss(Prym) \\ ss(Jac): %o\n", Sort(Setseq(only_prym));
    end if;
    if #inter gt 0 and #inter le 30 then
        printf "    ss(Prym) ∩ ss(Jac): %o\n", Sort(Setseq(inter));
    end if;
end for;

UnsetOutputFile();
printf "\nDone. Results in results/ss_jacobian.log\n";
quit;
