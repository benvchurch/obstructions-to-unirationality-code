/*******************************************************************************
 * check_isogeny3.m - Compare genus-2 curves from the 3 PSL(2,7) orbits
 * Compute Igusa invariants and identify Jacobian decompositions
 ******************************************************************************/

load "two_torsion/bitangent_data.m";
K := Parent(bitangent_lines[1][1]);
w := K.1;

RR<x,y,z> := PolynomialRing(K, 3);
F_poly := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
          - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);

mons4 := MonomialsOfDegree(RR, 4);
function CoeffVec(poly)
    return [MonomialCoefficient(poly, m) : m in mons4];
end function;
v_F := CoeffVec(F_poly);

// Contact quadratics
P2K<xK,yK,zK> := ProjectiveSpace(K, 2);
fKp := xK^4 + yK^4 + zK^4 + 6*(xK*yK^3 + yK*zK^3 + zK*xK^3)
      - 3*(xK^2*yK^2 + yK^2*zK^2 + zK^2*xK^2) + 3*xK*yK*zK*(xK+yK+zK);

RK2<UK,VK> := PolynomialRing(K, 2);
contact_quads_K := [];
param_type_K := [];
for i in [1..28] do
    A := bitangent_lines[i][1]; B := bitangent_lines[i][2]; CC := bitangent_lines[i][3];
    if CC ne 0 then
        restricted := Evaluate(fKp, [UK, VK, (-A*UK - B*VK)/CC]);
        restricted *:= CC^4;
        Append(~param_type_K, 3);
    elif B ne 0 then
        restricted := Evaluate(fKp, [UK, -A*UK/B, VK]);
        restricted *:= B^4;
        Append(~param_type_K, 2);
    else
        restricted := Evaluate(fKp, [K!0*UK, UK, VK]);
        Append(~param_type_K, 1);
    end if;
    RKuni<tK> := PolynomialRing(K);
    c0 := MonomialCoefficient(restricted, UK^4);
    c1 := MonomialCoefficient(restricted, UK^3*VK);
    c2 := MonomialCoefficient(restricted, UK^2*VK^2);
    c3 := MonomialCoefficient(restricted, UK*VK^3);
    c4 := MonomialCoefficient(restricted, VK^4);
    h := c0*tK^4 + c1*tK^3 + c2*tK^2 + c3*tK + c4;
    fac := Factorization(h);
    sq_root_monic := &*[e[1]^(e[2] div 2) : e in fac];
    ratio_val := LeadingCoefficient(h) / LeadingCoefficient(sq_root_monic)^2;
    sq_root := Sqrt(ratio_val) * sq_root_monic;
    al := Degree(sq_root) ge 2 select Coefficient(sq_root, 2) else K!0;
    be := Degree(sq_root) ge 1 select Coefficient(sq_root, 1) else K!0;
    ga := Coefficient(sq_root, 0);
    Append(~contact_quads_K, [al, be, ga]);
end for;

function RestrictionMatrixK(i)
    M := ZeroMatrix(K, 3, 6);
    AA := bitangent_lines[i][1]; BB := bitangent_lines[i][2]; CC := bitangent_lines[i][3];
    if param_type_K[i] eq 3 then
        a := -AA/CC; b := -BB/CC;
        M[1,1] := 1; M[1,3] := a; M[1,6] := a^2;
        M[2,2] := 1; M[2,3] := b; M[2,5] := a; M[2,6] := 2*a*b;
        M[3,4] := 1; M[3,5] := b; M[3,6] := b^2;
    elif param_type_K[i] eq 2 then
        c := -AA/BB;
        M[1,1] := 1; M[1,2] := c; M[1,4] := c^2;
        M[2,5] := 1; M[2,6] := c;
        M[3,6] := 1;
    else
        M[1,4] := 1; M[2,5] := 1; M[3,6] := 1;
    end if;
    return M;
end function;

function FindConicK(i, j, k, l)
    MM := ZeroMatrix(K, 12, 10);
    lines := [i, j, k, l];
    for idx in [1..4] do
        m := lines[idx];
        Rm := RestrictionMatrixK(m);
        hm := contact_quads_K[m];
        for r in [1..3] do
            row := 3*(idx-1) + r;
            for c in [1..6] do MM[row, c] := Rm[r, c]; end for;
            MM[row, 6+idx] := -hm[r];
        end for;
    end for;
    N := Nullspace(Transpose(MM));
    if Dimension(N) eq 0 then return [K | 0,0,0,0,0,0], false; end if;
    v := N.1;
    return [v[c] : c in [1..6]], true;
end function;

function QuadMat(coeffs)
    return Matrix(K, 3, 3, [
        [coeffs[1], coeffs[2]/2, coeffs[3]/2],
        [coeffs[2]/2, coeffs[4], coeffs[5]/2],
        [coeffs[3]/2, coeffs[5]/2, coeffs[6]]
    ]);
end function;

function LProdCoeffs(L1, L2)
    return [L1[1]*L2[1], L1[1]*L2[2]+L1[2]*L2[1], L1[1]*L2[3]+L1[3]*L2[1],
            L1[2]*L2[2], L1[2]*L2[3]+L1[3]*L2[2], L1[3]*L2[3]];
end function;

Rt<t> := PolynomialRing(K);

function MakeGenus2(pa, pb, Qc, a_coeff, b_coeff)
    Q1c := LProdCoeffs(bitangent_lines[pa[1]], bitangent_lines[pa[2]]);
    Q1c := [b_coeff * e : e in Q1c];
    Q3c := LProdCoeffs(bitangent_lines[pb[1]], bitangent_lines[pb[2]]);
    Q3c := [-e : e in Q3c];
    Q2c := [K | b_coeff * Qc[idx] : idx in [1..6]];
    M1 := QuadMat(Q1c); M2 := QuadMat(Q2c); M3 := QuadMat(Q3c);
    M := ZeroMatrix(Rt, 3, 3);
    for i in [1..3] do
        for j in [1..3] do
            M[i,j] := Rt!(M1[i,j]) + 2*t*Rt!(M2[i,j]) + t^2*Rt!(M3[i,j]);
        end for;
    end for;
    return -Determinant(M);
end function;

function GetDecomp(pa, pb, Qc)
    prod := (bitangent_lines[pa[1]][1]*x + bitangent_lines[pa[1]][2]*y + bitangent_lines[pa[1]][3]*z)
           *(bitangent_lines[pa[2]][1]*x + bitangent_lines[pa[2]][2]*y + bitangent_lines[pa[2]][3]*z)
           *(bitangent_lines[pb[1]][1]*x + bitangent_lines[pb[1]][2]*y + bitangent_lines[pb[1]][3]*z)
           *(bitangent_lines[pb[2]][1]*x + bitangent_lines[pb[2]][2]*y + bitangent_lines[pb[2]][3]*z);
    Q_poly := Qc[1]*x^2+Qc[2]*x*y+Qc[3]*x*z+Qc[4]*y^2+Qc[5]*y*z+Qc[6]*z^2;
    vprod := CoeffVec(prod);
    vQ2 := CoeffVec(Q_poly^2);
    mat := Matrix(K, 3, #mons4, [v_F, vprod, vQ2]);
    N := Nullspace(mat);
    rel := N.1;
    return -rel[1]/rel[2], rel[3]/rel[2];
end function;

// Representative complexes from the 3 PSL(2,7) orbit types
// From steiner.m output:
// 28-orbit: e.g. Complex #7 = {1,2} {7,10} {11,22} {13,15} {18,20} {24,26}
// 7-orbit: e.g. Complex #3 = {1,10} {2,7} {3,23} {4,19} {9,21} {12,16}
//   and conjugate Complex #4 = {2,9} {7,21} {8,18} {14,15} {22,25} {26,28}
// 21-orbit: e.g. Complex #1 = {1,9} {8,20} {10,21} {11,25} {13,14} {24,28}

test_cases := [
    <"28-orbit (Complex #7)", [[1,2],[7,10],[11,22],[13,15],[18,20],[24,26]]>,
    <"7-orbit-A (Complex #3)", [[1,10],[2,7],[3,23],[4,19],[9,21],[12,16]]>,
    <"7-orbit-B (Complex #4)", [[2,9],[7,21],[8,18],[14,15],[22,25],[26,28]]>,
    <"21-orbit (Complex #1)", [[1,9],[8,20],[10,21],[11,25],[13,14],[24,28]]>
];

for tc in test_cases do
    label := tc[1];
    pairs := tc[2];
    printf "\n=== %o ===\n", label;

    // Try first valid pair-of-pairs
    done := false;
    for pi1 in [1..6] do
        if done then break; end if;
        for pi2 in [pi1+1..6] do
            if done then break; end if;
            pa := pairs[pi1]; pb := pairs[pi2];
            Qc, ok := FindConicK(pa[1], pa[2], pb[1], pb[2]);
            if not ok then continue; end if;

            a_coeff, b_coeff := GetDecomp(pa, pb, Qc);
            dp := MakeGenus2(pa, pb, Qc, a_coeff, b_coeff);

            if Degree(dp) lt 5 then continue; end if;

            printf "Pairs: %o x %o, a=%o, b=%o\n", pa, pb, a_coeff, b_coeff;
            printf "det poly degree: %o\n", Degree(dp);

            H := HyperellipticCurve(dp);
            I := IgusaInvariants(H);
            printf "Igusa [I2,I4,I6,I8,I10] = %o\n", I;

            if I[5] ne 0 then
                abs := [I[1]^5/I[5], I[1]^3*I[2]/I[5], I[1]^2*I[3]/I[5]];
                printf "Absolute Igusa: %o\n", abs;
                for idx in [1..3] do
                    mp := MinimalPolynomial(abs[idx]);
                    names := ["I2^5/I10", "I2^3*I4/I10", "I2^2*I6/I10"];
                    printf "  %o min poly: %o\n", names[idx], mp;
                end for;
            else
                printf "I10 = 0!\n";
            end if;

            fac := Factorization(dp);
            printf "det poly factorization: degrees %o\n", [Degree(f[1]) : f in fac];

            done := true;
        end for;
    end for;
    if not done then print "No valid pair found!"; end if;
end for;

// Now: for each orbit, compute genus-2 curve and try to identify Jacobian
// by reducing mod primes and checking #J(F_p)
print "\n\n=== Identifying Jacobians via point counting ===";

// The Klein quartic has Jac(C) ~ E^3 where E = 49a1 (j = -3375, CM by Q(sqrt(-7)))
// So for a 2-torsion class eta, the Prym variety should be related to E

// For each orbit, compute #J(F_p) of the genus-2 curve for several primes
// and compare with #E1(F_p) * #E2(F_p) for candidate pairs

for tc in test_cases do
    label := tc[1];
    pairs := tc[2];
    printf "\n--- %o: point counts ---\n", label;

    // Find a working decomposition
    found := false;
    dp := Rt!0;
    for pi1 in [1..6] do
        if found then break; end if;
        for pi2 in [pi1+1..6] do
            pa := pairs[pi1]; pb := pairs[pi2];
            Qc, ok := FindConicK(pa[1], pa[2], pb[1], pb[2]);
            if not ok then continue; end if;
            a_coeff, b_coeff := GetDecomp(pa, pb, Qc);
            dp := MakeGenus2(pa, pb, Qc, a_coeff, b_coeff);
            if Degree(dp) ge 5 then found := true; break; end if;
        end for;
    end for;
    if not found then print "  No valid curve"; continue; end if;

    H := HyperellipticCurve(dp);

    // Reduce mod primes
    for p in [11, 13, 29, 31, 37, 41, 43, 47, 53, 59, 67, 71, 73, 79, 83, 89, 97] do
        Fp := GF(p);
        // Check if sqrt(-7) exists mod p
        is_sq, sq7 := IsSquare(Fp!(-7));
        if not is_sq then continue; end if;

        // Reduce coefficients of dp
        coeffs_dp := Coefficients(dp);
        PFp<tp> := PolynomialRing(Fp);
        dp_red := PFp!0;
        for idx in [1..#coeffs_dp] do
            c := coeffs_dp[idx];
            cs := Eltseq(K!c);
            c_red := Fp!(cs[1]) + sq7 * Fp!(cs[2]);
            dp_red +:= c_red * tp^(idx-1);
        end for;

        // Make sure it's a valid hyperelliptic curve
        if Degree(dp_red) lt 5 then continue; end if;
        disc_red := Discriminant(dp_red);
        if disc_red eq 0 then continue; end if;

        try
            Hp := HyperellipticCurve(dp_red);
            Jp := Jacobian(Hp);
            nJ := #Jp;

            // Also compute #E(F_p) for E = 49a1 (y^2 = x^3 - x^2 - 2x - 1, j=-3375)
            Ep := EllipticCurve([Fp| 0, -1, 0, -2, -1]);
            // Actually 49a1 is y^2 + xy = x^3 - x^2 - 2x - 1
            Ep := EllipticCurve([Fp| 1, -1, 0, -2, -1]);
            nE := #Ep;
            ap := p + 1 - nE;

            printf "  p=%o: #J=%o, #E(49a1)=%o, a_p=%o, #E^2=%o, match=%o\n",
                p, nJ, nE, ap, nE^2, nJ eq nE^2;
        catch e
            continue;
        end try;
    end for;
end for;
