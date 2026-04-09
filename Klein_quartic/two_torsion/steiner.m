/*******************************************************************************
 * steiner.m
 *
 * Compute the 63 Steiner complexes of C_twist's 28 bitangent lines.
 *
 * Method: work over F_p (split prime), find tangency points by intersecting
 * each bitangent line with the curve, compute contact divisors in the class
 * group, and group pairs {L_i,L_j} by the 2-torsion class [D_i - D_j].
 * Then compute witnessing conics for each Steiner complex.
 *
 * Dependencies: bitangent_data.m
 ******************************************************************************/

load "two_torsion/bitangent_data.m";

// =====================================================================
// Part 1: Setup over F_p
// =====================================================================

p := 43;
Fp := GF(p);
sq7 := Sqrt(Fp!(-7));

function ToFp(x)
    coeffs := Eltseq(K!x);
    return Fp!(coeffs[1]) + sq7 * Fp!(coeffs[2]);
end function;

P2p<x,y,z> := ProjectiveSpace(Fp, 2);
fp := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
      - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
Cp := Curve(P2p, fp);
assert IsNonsingular(Cp);

// Reduce lines to F_p and store as [A,B,C]
lines_Fp := [];
for i in [1..28] do
    L := bitangent_lines[i];
    Append(~lines_Fp, [ToFp(L[1]), ToFp(L[2]), ToFp(L[3])]);
end for;
printf "Reduced 28 lines to F_%o\n", p;

// =====================================================================
// Part 2: Compute contact divisors
// =====================================================================

print "\n=== Computing contact divisors ===";
Cl, mp := ClassGroup(Cp);
print "Class group:", Cl;

// For each bitangent line, find the contact divisor D_i (degree 2)
// by intersecting the line with the curve.
// The line L_i cuts C in a degree-4 divisor = 2*D_i.
// We find D_i by computing the intersection and halving.

contact_divs := [];

for i in [1..28] do
    A := lines_Fp[i][1]; B := lines_Fp[i][2]; C := lines_Fp[i][3];
    Li := Curve(P2p, A*x + B*y + C*z);

    // Scheme-theoretic intersection
    Z := Li meet Cp;
    pts := PointsOverSplittingField(Z);

    // Build D_i from the tangency points
    // Each point in pts has a multiplicity; for a bitangent, mult >= 2
    // D_i = sum of points with reduced multiplicity

    // Alternative: use function field approach
    // On Cp, the function (Ax+By+Cz)/ell has divisor 2*D_i - deg4
    // where ell is some other linear form.
    // Simpler: use Places directly.

    // Find places on Cp that lie on L_i
    // A place P lies on L_i iff the function (Ax+By+Cz) vanishes at P.
    // On the function field of Cp, (Ax+By+Cz)/z (or appropriate) is a function.

    // Use the ideal-theoretic approach via the scheme intersection
    comps := IrreducibleComponents(Z);
    D := Zero(DivisorGroup(Cp));
    for comp in comps do
        deg := Degree(comp);
        // The intersection has multiplicity 2 at each tangency point
        // Each component appears with multiplicity 2 in L_i ∩ C
        // D_i uses multiplicity 1
        pts_comp := Points(comp);
        if #pts_comp gt 0 then
            for pt in pts_comp do
                ptC := Cp!Eltseq(pt);
                pl := Place(ptC);
                D +:= Divisor(pl);
            end for;
        else
            // Degree-2 component with no rational points
            // Need to find the corresponding degree-2 place
            // The component is defined by two equations: the curve and the line
            // plus the minimal polynomial of the point
            I_comp := Ideal(comp);

            // Find the degree-2 place on Cp
            // Search through degree-2 places
            places2 := Places(Cp, 2);
            found := false;
            for pl in places2 do
                // Check if this place lies on L_i
                // Evaluate A*x/z + B*y/z + C at the place (using z!=0 chart)
                // or use the residue/function field
                F := FunctionField(Cp);
                // The function A*x + B*y + C*z as a rational function on Cp
                // Use coords: in Magma, for a projective curve,
                // FunctionField gives functions as ratios of forms of same degree
                if C ne 0 then
                    // Use z != 0: function = A*(x/z) + B*(y/z) + C
                    Aff := AffinePatch(Cp, 3);  // z != 0
                    FA := FunctionField(Aff);
                    line_fn := A*FA.1 + B*FA.2 + C;
                elif B ne 0 then
                    Aff := AffinePatch(Cp, 2);
                    FA := FunctionField(Aff);
                    line_fn := A*FA.1 + B + C*FA.2;
                else
                    Aff := AffinePatch(Cp, 1);
                    FA := FunctionField(Aff);
                    line_fn := A + B*FA.1 + C*FA.2;
                end if;
                v := Valuation(line_fn, pl);
                if v ge 1 then
                    D +:= Divisor(pl);
                    found := true;
                    break;
                end if;
            end for;
            if not found then
                error "Could not find degree-2 place for bitangent", i;
            end if;
        end if;
    end for;

    assert Degree(D) eq 2;
    Append(~contact_divs, D);
end for;

print "All 28 contact divisors computed.";

// =====================================================================
// Part 3: Compute Steiner complexes via J[2]
// =====================================================================

print "\n=== Computing Steiner complexes ===";

// Map a 2-torsion divisor to its J[2] coordinate vector in (Z/2)^6
// For Cl = Z/2 x Z/2 x Z/2 x Z/28 x Z/28 x Z/28 x Z:
// 2-torsion coords are (c1, c2, c3, c4/14, c5/14, c6/14) dropping the Z factor
function ClassJ2(D)
    cl := D @@ mp;
    coords := Eltseq(cl);
    inv := Invariants(Cl);
    j2 := [];
    for k in [1..#inv] do
        if inv[k] eq 0 then
            // Z factor (degree): skip for degree-0 divisors
            continue;
        end if;
        half := inv[k] div 2;
        if half eq 0 then
            // Should not happen since inv[k] >= 2
            Append(~j2, coords[k]);
        else
            Append(~j2, coords[k] div half);
        end if;
    end for;
    return j2;
end function;

// Group pairs by [D_i - D_j] mod 2
class_to_pairs := AssociativeArray();
for i in [1..28] do
    for j in [i+1..28] do
        D_diff := contact_divs[i] - contact_divs[j];
        cl2 := ClassJ2(D_diff);
        if not IsDefined(class_to_pairs, cl2) then
            class_to_pairs[cl2] := [];
        end if;
        Append(~class_to_pairs[cl2], [i, j]);
    end for;
end for;

nclasses := #Keys(class_to_pairs);
sizes := Sort([#class_to_pairs[k] : k in Keys(class_to_pairs)]);
printf "Distinct 2-torsion classes: %o\n", nclasses;
printf "Sizes: %o\n", sizes;
assert nclasses eq 63;
assert &and[s eq 6 : s in sizes];
print "63 Steiner complexes, each with 6 pairs. ✓";

// =====================================================================
// Part 4: Compute witnessing conics
// =====================================================================

print "\n=== Computing witnessing conics ===";

// For 4 bitangent lines, find the conic through their 8 tangency points.
// The tangency points of L_i are the support of D_i.
// Instead of working with points directly, use the algebraic condition:
//   Q(x,y,z) vanishes at the tangency points of L_m
//   iff Q restricted to L_m is divisible by the contact quadratic h_m.
//
// For line Ax+By+Cz=0, we parameterize and compute Q|_L.
// We need the contact quadratic h_m over F_p.

// Compute contact quadratics over F_p
Rp<U,Vv> := PolynomialRing(Fp, 2);
Runi<t> := PolynomialRing(Fp);

contact_quads := [];  // [alpha, beta, gamma] for each line's parameterization
param_type := [];     // which coord is eliminated

for i in [1..28] do
    A := lines_Fp[i][1]; B := lines_Fp[i][2]; C := lines_Fp[i][3];
    if C ne 0 then
        // z = (-Ax - By)/C, param (U, V, (-AU-BV)/C)
        restricted := Evaluate(fp, [U, Vv, (-A*U - B*Vv)/C]);
        restricted *:= C^4;  // clear denominator
        Append(~param_type, 3);
    elif B ne 0 then
        // y = (-Ax)/B, param (U, -AU/B, V)
        restricted := Evaluate(fp, [U, -A*U/B, Vv]);
        restricted *:= B^4;
        Append(~param_type, 2);
    else
        restricted := Evaluate(fp, [Fp!0*U, U, Vv]);
        Append(~param_type, 1);
    end if;

    // Extract quartic coefficients and take square root
    c0 := MonomialCoefficient(restricted, U^4);
    c1 := MonomialCoefficient(restricted, U^3*Vv);
    c2 := MonomialCoefficient(restricted, U^2*Vv^2);
    c3 := MonomialCoefficient(restricted, U*Vv^3);
    c4 := MonomialCoefficient(restricted, Vv^4);

    // Factor the dehomogenized quartic to find square root
    h := c0*t^4 + c1*t^3 + c2*t^2 + c3*t + c4;
    fac := Factorization(h);
    assert &and[e[2] mod 2 eq 0 : e in fac];
    // Reconstruct monic square root
    sq_root_monic := &*[e[1]^(e[2] div 2) : e in fac];
    // h = ratio * sq_root_monic^2, find ratio via leading coefficients
    deg_h := Degree(h);
    deg_s := Degree(sq_root_monic);
    assert deg_h eq 2*deg_s or (deg_h lt 0 and deg_s lt 0);
    if deg_h ge 0 then
        ratio_val := LeadingCoefficient(h) / LeadingCoefficient(sq_root_monic)^2;
    else
        ratio_val := Fp!1;
    end if;
    assert IsSquare(ratio_val);
    sq_root := Sqrt(ratio_val) * sq_root_monic;
    assert sq_root^2 eq h;

    // Extract quadratic coefficients [alpha, beta, gamma]
    if Degree(sq_root) eq 2 then
        al := Coefficient(sq_root, 2);
        be := Coefficient(sq_root, 1);
        ga := Coefficient(sq_root, 0);
    elif Degree(sq_root) eq 1 then
        // U=0 is a tangency point
        al := Fp!0;
        be := Coefficient(sq_root, 1);
        ga := Coefficient(sq_root, 0);
    else
        al := Fp!0; be := Fp!0;
        ga := Coefficient(sq_root, 0);
    end if;
    Append(~contact_quads, [al, be, ga]);
end for;
print "Contact quadratics computed over F_p.";

// Restriction matrix: for line i and conic Q=[A,B,C,D,E,F] (Ax^2+Bxy+Cxz+Dy^2+Eyz+Fz^2),
// compute Q|_{L_i} as a quadratic in (U,V).
function RestrictionMatrix(i)
    M := ZeroMatrix(Fp, 3, 6);
    AA := lines_Fp[i][1]; BB := lines_Fp[i][2]; CC := lines_Fp[i][3];
    if param_type[i] eq 3 then
        // param (U, V, (-AA*U - BB*V)/CC)
        a := -AA/CC; b := -BB/CC;
        M[1,1] := 1; M[1,3] := a; M[1,6] := a^2;
        M[2,2] := 1; M[2,3] := b; M[2,5] := a; M[2,6] := 2*a*b;
        M[3,4] := 1; M[3,5] := b; M[3,6] := b^2;
    elif param_type[i] eq 2 then
        // param (U, -AA*U/BB, V)
        c := -AA/BB;
        M[1,1] := 1; M[1,2] := c; M[1,4] := c^2;
        M[2,3] := 1; M[2,5] := c;
        M[3,6] := 1;
    else
        // param (0, U, V)
        M[1,4] := 1;
        M[2,5] := 1;
        M[3,6] := 1;
    end if;
    return M;
end function;

function FindConic(i, j, k, l)
    M := ZeroMatrix(Fp, 12, 10);
    lines := [i, j, k, l];
    for idx in [1..4] do
        m := lines[idx];
        Rm := RestrictionMatrix(m);
        hm := contact_quads[m];
        for r in [1..3] do
            row := 3*(idx-1) + r;
            for c in [1..6] do
                M[row, c] := Rm[r, c];
            end for;
            M[row, 6+idx] := -hm[r];
        end for;
    end for;
    N := Nullspace(Transpose(M));
    dim := Dimension(N);
    if dim eq 0 then
        return [Fp | 0,0,0,0,0,0], false;
    end if;
    v := N.1;
    return [v[c] : c in [1..6]], true;
end function;

// Build steiner_data
steiner_data := [];
complex_idx := 0;
for key in Keys(class_to_pairs) do
    complex_idx +:= 1;
    cpairs := class_to_pairs[key];

    // Compute 15 witnessing conics
    conics := [];
    all_found := true;
    for a in [1..6] do
        for b in [a+1..6] do
            pa := cpairs[a]; pb := cpairs[b];
            conic, ok := FindConic(pa[1], pa[2], pb[1], pb[2]);
            if not ok then
                printf "WARNING: no conic for complex %o, sub-pair %o,%o\n", complex_idx, a, b;
                all_found := false;
            end if;
            Append(~conics, conic);
        end for;
    end for;

    Append(~steiner_data, <cpairs, conics, key>);
end for;

// =====================================================================
// Part 5: Verify conics
// =====================================================================

print "\nVerifying all 945 conics...";
verified := 0;
failed := 0;
for ci in [1..63] do
    sd := steiner_data[ci];
    cpairs := sd[1];
    conics := sd[2];
    conic_idx := 0;
    for a in [1..6] do
        for b in [a+1..6] do
            conic_idx +:= 1;
            Q := conics[conic_idx];
            if Q eq [Fp|0,0,0,0,0,0] then continue; end if;
            pa := cpairs[a]; pb := cpairs[b];
            ok := true;
            for m in pa cat pb do
                Rm := RestrictionMatrix(m);
                hm := contact_quads[m];
                restr := [&+[Rm[r,c]*Q[c] : c in [1..6]] : r in [1..3]];
                // Check proportionality to hm
                lambda := Fp!0;
                for r in [1..3] do
                    if hm[r] ne 0 then
                        lambda := restr[r] / hm[r];
                        break;
                    end if;
                end for;
                expected := [lambda * hm[r] : r in [1..3]];
                if restr ne expected then
                    ok := false;
                end if;
            end for;
            if ok then verified +:= 1; else failed +:= 1; end if;
        end for;
    end for;
end for;
printf "Verified: %o, Failed: %o (out of 945)\n", verified, failed;

// =====================================================================
// Part 6: Display
// =====================================================================

print "\n========================================";
printf "The 63 Steiner complexes (over F_%o)\n", p;
print "========================================";

for ci in [1..#steiner_data] do
    sd := steiner_data[ci];
    printf "Complex #%o: ", ci;
    for k in [1..6] do
        printf "{%o,%o}", sd[1][k][1], sd[1][k][2];
        if k lt 6 then printf " "; end if;
    end for;
    // Lines involved
    involved := {};
    for pr in sd[1] do
        Include(~involved, pr[1]); Include(~involved, pr[2]);
    end for;
    printf "  [%o lines]\n", #involved;
end for;

// Statistics
print "\n=== Statistics ===";
line_count := AssociativeArray();
for i in [1..28] do line_count[i] := 0; end for;
for sd in steiner_data do
    for pr in sd[1] do
        line_count[pr[1]] +:= 1;
        line_count[pr[2]] +:= 1;
    end for;
end for;
counts := [line_count[i] : i in [1..28]];
printf "Complexes per line: %o\n", counts;
assert &and[c eq 27 : c in counts];
print "Each line in exactly 27 complexes. ✓";

// Distinct conics
all_conics := {};
for sd in steiner_data do
    for c in sd[2] do
        if c eq [Fp|0,0,0,0,0,0] then continue; end if;
        nc := c;
        for j in [1..6] do
            if nc[j] ne 0 then
                inv := nc[j]^(-1);
                nc := [inv * nc[k] : k in [1..6]];
                break;
            end if;
        end for;
        Include(~all_conics, nc);
    end for;
end for;
printf "Distinct conics: %o (out of 945)\n", #all_conics;

// Lines per complex
lpc := [];
for sd in steiner_data do
    involved := {};
    for pr in sd[1] do
        Include(~involved, pr[1]); Include(~involved, pr[2]);
    end for;
    Append(~lpc, #involved);
end for;
Sort(~lpc);
printf "Lines per complex: %o\n", lpc;

// =====================================================================
// Part 7: Lift conics to Q(sqrt(-7))
// =====================================================================

print "\n=== Lifting conics to Q(sqrt(-7)) ===";

// Compute contact quadratics over K = Q(sqrt(-7))
RK<UK,VK> := PolynomialRing(K, 2);
RKuni<tK> := PolynomialRing(K);

P2K<xK,yK,zK> := ProjectiveSpace(K, 2);
fK := xK^4 + yK^4 + zK^4 + 6*(xK*yK^3 + yK*zK^3 + zK*xK^3)
      - 3*(xK^2*yK^2 + yK^2*zK^2 + zK^2*xK^2) + 3*xK*yK*zK*(xK+yK+zK);

contact_quads_K := [];
param_type_K := [];

for i in [1..28] do
    A := bitangent_lines[i][1]; B := bitangent_lines[i][2]; CC := bitangent_lines[i][3];
    if CC ne 0 then
        restricted := Evaluate(fK, [UK, VK, (-A*UK - B*VK)/CC]);
        restricted *:= CC^4;
        Append(~param_type_K, 3);
    elif B ne 0 then
        restricted := Evaluate(fK, [UK, -A*UK/B, VK]);
        restricted *:= B^4;
        Append(~param_type_K, 2);
    else
        restricted := Evaluate(fK, [K!0*UK, UK, VK]);
        Append(~param_type_K, 1);
    end if;

    c0 := MonomialCoefficient(restricted, UK^4);
    c1 := MonomialCoefficient(restricted, UK^3*VK);
    c2 := MonomialCoefficient(restricted, UK^2*VK^2);
    c3 := MonomialCoefficient(restricted, UK*VK^3);
    c4 := MonomialCoefficient(restricted, VK^4);

    h := c0*tK^4 + c1*tK^3 + c2*tK^2 + c3*tK + c4;
    fac := Factorization(h);
    assert &and[e[2] mod 2 eq 0 : e in fac];
    sq_root_monic := &*[e[1]^(e[2] div 2) : e in fac];
    if Degree(h) ge 0 then
        ratio_val := LeadingCoefficient(h) / LeadingCoefficient(sq_root_monic)^2;
    else
        ratio_val := K!1;
    end if;
    assert IsSquare(ratio_val);
    sq_root := Sqrt(ratio_val) * sq_root_monic;
    assert sq_root^2 eq h;

    if Degree(sq_root) eq 2 then
        al := Coefficient(sq_root, 2);
        be := Coefficient(sq_root, 1);
        ga := Coefficient(sq_root, 0);
    elif Degree(sq_root) eq 1 then
        al := K!0;
        be := Coefficient(sq_root, 1);
        ga := Coefficient(sq_root, 0);
    else
        al := K!0; be := K!0;
        ga := Coefficient(sq_root, 0);
    end if;
    Append(~contact_quads_K, [al, be, ga]);
end for;
print "Contact quadratics computed over Q(sqrt(-7)).";

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
        M[2,3] := 1; M[2,5] := c;
        M[3,6] := 1;
    else
        M[1,4] := 1;
        M[2,5] := 1;
        M[3,6] := 1;
    end if;
    return M;
end function;

function FindConicK(i, j, k, l)
    M := ZeroMatrix(K, 12, 10);
    lines := [i, j, k, l];
    for idx in [1..4] do
        m := lines[idx];
        Rm := RestrictionMatrixK(m);
        hm := contact_quads_K[m];
        for r in [1..3] do
            row := 3*(idx-1) + r;
            for c in [1..6] do
                M[row, c] := Rm[r, c];
            end for;
            M[row, 6+idx] := -hm[r];
        end for;
    end for;
    N := Nullspace(Transpose(M));
    dim := Dimension(N);
    if dim eq 0 then
        return [K | 0,0,0,0,0,0], false;
    end if;
    v := N.1;
    return [v[c] : c in [1..6]], true;
end function;

// Recompute conics over K using the same Steiner complex pairings
steiner_data_K := [];
for ci in [1..63] do
    cpairs := steiner_data[ci][1];
    conics_K := [];
    for a in [1..6] do
        for b in [a+1..6] do
            pa := cpairs[a]; pb := cpairs[b];
            conic, ok := FindConicK(pa[1], pa[2], pb[1], pb[2]);
            if not ok then
                printf "WARNING: no conic for complex %o, sub-pair %o,%o over K\n", ci, a, b;
            end if;
            Append(~conics_K, conic);
        end for;
    end for;
    Append(~steiner_data_K, <cpairs, conics_K>);
end for;

// Verify conics over K
print "Verifying conics over Q(sqrt(-7))...";
verified_K := 0;
failed_K := 0;
for ci in [1..63] do
    sd := steiner_data_K[ci];
    cpairs := sd[1];
    conics_K := sd[2];
    conic_idx := 0;
    for a in [1..6] do
        for b in [a+1..6] do
            conic_idx +:= 1;
            Q := conics_K[conic_idx];
            if Q eq [K|0,0,0,0,0,0] then continue; end if;
            pa := cpairs[a]; pb := cpairs[b];
            ok := true;
            for m in pa cat pb do
                Rm := RestrictionMatrixK(m);
                hm := contact_quads_K[m];
                restr := [&+[Rm[r,c]*Q[c] : c in [1..6]] : r in [1..3]];
                lambda := K!0;
                for r in [1..3] do
                    if hm[r] ne 0 then
                        lambda := restr[r] / hm[r];
                        break;
                    end if;
                end for;
                expected := [lambda * hm[r] : r in [1..3]];
                if restr ne expected then
                    ok := false;
                end if;
            end for;
            if ok then verified_K +:= 1; else failed_K +:= 1; end if;
        end for;
    end for;
end for;
printf "Over Q(sqrt(-7)): Verified: %o, Failed: %o (out of 945)\n", verified_K, failed_K;

// =====================================================================
// Part 8: Verify quartic decompositions a*F = L_i*L_j*L_k*L_l + b*Q^2
// =====================================================================

// =====================================================================
// Part 8: Verify quartic decompositions a*F = L_i*L_j*L_k*L_l + b*Q^2
// =====================================================================

print "\n=== Verifying quartic decompositions ===";

RR<xx,yy,zz> := PolynomialRing(K, 3);
F_poly := xx^4 + yy^4 + zz^4 + 6*(xx*yy^3 + yy*zz^3 + zz*xx^3)
          - 3*(xx^2*yy^2 + yy^2*zz^2 + zz^2*xx^2) + 3*xx*yy*zz*(xx+yy+zz);

mons4 := MonomialsOfDegree(RR, 4);
function CoeffVec(poly)
    return [MonomialCoefficient(poly, m) : m in mons4];
end function;

v_F := CoeffVec(F_poly);

decomp_verified := 0;
decomp_failed := 0;
decomps := [];  // store [complex_idx, pair_a, pair_b, a_coeff, b_coeff]

for ci in [1..63] do
    sd := steiner_data_K[ci];
    cpairs := sd[1];
    conics_K := sd[2];
    conic_idx := 0;
    for a in [1..6] do
        for b in [a+1..6] do
            conic_idx +:= 1;
            pa := cpairs[a]; pb := cpairs[b];

            // Build linear forms
            Li := bitangent_lines[pa[1]];
            Lj := bitangent_lines[pa[2]];
            Lk := bitangent_lines[pb[1]];
            Ll := bitangent_lines[pb[2]];
            prod_L := (Li[1]*xx + Li[2]*yy + Li[3]*zz)
                     *(Lj[1]*xx + Lj[2]*yy + Lj[3]*zz)
                     *(Lk[1]*xx + Lk[2]*yy + Lk[3]*zz)
                     *(Ll[1]*xx + Ll[2]*yy + Ll[3]*zz);

            // Build conic
            Qc := conics_K[conic_idx];
            Q_poly := Qc[1]*xx^2 + Qc[2]*xx*yy + Qc[3]*xx*zz
                    + Qc[4]*yy^2 + Qc[5]*yy*zz + Qc[6]*zz^2;
            Q2_poly := Q_poly^2;

            v_prod := CoeffVec(prod_L);
            v_Q2 := CoeffVec(Q2_poly);

            // Check linear dependence: find kernel of [v_F; v_prod; v_Q2]
            M := Matrix(K, 3, #mons4, [v_F, v_prod, v_Q2]);
            N := Nullspace(M);
            if Dimension(N) ge 1 then
                rel := N.1;
                // rel[1]*F + rel[2]*prod_L + rel[3]*Q^2 = 0
                // => (-rel[1]/rel[2])*F = prod_L + (rel[3]/rel[2])*Q^2
                if rel[2] ne 0 then
                    a_coeff := -rel[1]/rel[2];
                    b_coeff := rel[3]/rel[2];
                    // Verify: a_coeff * F = prod_L + b_coeff * Q^2
                    assert a_coeff * F_poly eq prod_L + b_coeff * Q2_poly;
                    Append(~decomps, <ci, pa, pb, a_coeff, b_coeff>);
                    decomp_verified +:= 1;
                else
                    // F not involved — degenerate
                    decomp_failed +:= 1;
                end if;
            else
                decomp_failed +:= 1;
            end if;
        end for;
    end for;
end for;
printf "Decompositions verified: %o, failed: %o (out of 945)\n",
    decomp_verified, decomp_failed;

// Display a few examples
print "\n--- Sample decompositions ---";
for idx in [1..Min(5, #decomps)] do
    d := decomps[idx];
    printf "Complex #%o, lines {%o,%o} x {%o,%o}:\n",
        d[1], d[2][1], d[2][2], d[3][1], d[3][2];
    printf "  %o * F = L_%o*L_%o*L_%o*L_%o + (%o) * Q^2\n",
        d[4], d[2][1], d[2][2], d[3][1], d[3][2], d[5];
end for;

// =====================================================================
// Part 9+10: Genus-2 curves, Z/3Z orbits, and j-invariants
// =====================================================================

print "\n=== Genus-2 curves and j-invariants ===";

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

Pt<t> := PolynomialRing(K);

// Corrected: given a*F = prod + b*Q^2, multiply by b:
//   ab*F = b*prod + (bQ)^2
// Set Q1 = b*L_i*L_j, Q3 = -L_k*L_l, Q2 = b*Q.
// Then Q1*Q3 - Q2^2 = -b*prod - b^2*Q^2 = -ab*F.
function DetPoly(pa, pb, Qc, a_coeff, b_coeff)
    Q1c := LProdCoeffs(bitangent_lines[pa[1]], bitangent_lines[pa[2]]);
    Q1c := [b_coeff * e : e in Q1c];
    Q3c := LProdCoeffs(bitangent_lines[pb[1]], bitangent_lines[pb[2]]);
    Q3c := [-e : e in Q3c];
    Q2c := [K | b_coeff * Qc[idx] : idx in [1..6]];
    M1 := QuadMat(Q1c); M2 := QuadMat(Q2c); M3 := QuadMat(Q3c);
    M := ZeroMatrix(Pt, 3, 3);
    for i in [1..3] do
        for j in [1..3] do
            M[i,j] := Pt!(M1[i,j]) + 2*t*Pt!(M2[i,j]) + t^2*Pt!(M3[i,j]);
        end for;
    end for;
    return -Determinant(M);
end function;

// Search all C(6,3) partitions for Z/3Z orbit {x, 1-1/x, 1/(1-x)}
// pts = sequence of <value, is_inf> pairs, length 6
function FindOrbit(pts)
    F := Parent(pts[1][1]);
    for i1 in [1..6] do
        for i2 in [i1+1..6] do
            for i3 in [i2+1..6] do
                rest := [k : k in [1..6] | k notin {i1,i2,i3}];
                s1 := pts[i1]; s2 := pts[i2]; s3 := pts[i3];

                // FLT sending s1->0, s2->1, s3->inf applied to rest
                imgs := [];
                ok := true;
                for k in [1..3] do
                    rr := pts[rest[k]];
                    if s3[2] then
                        // s3=inf: phi(z) = (z-s1)/(s2-s1)
                        if rr[2] then ok := false; break; end if;
                        Append(~imgs, (rr[1] - s1[1]) / (s2[1] - s1[1]));
                    elif s2[2] then
                        if rr[2] then Append(~imgs, F!1); continue; end if;
                        Append(~imgs, (rr[1] - s1[1]) / (rr[1] - s3[1]));
                    elif s1[2] then
                        if rr[2] then Append(~imgs, F!0); continue; end if;
                        Append(~imgs, (s2[1] - s3[1]) / (rr[1] - s3[1]));
                    else
                        if rr[2] then
                            Append(~imgs, (s2[1]-s3[1]) / (s2[1]-s1[1]));
                        else
                            d := (rr[1]-s3[1])*(s2[1]-s1[1]);
                            if d eq 0 then ok := false; break; end if;
                            Append(~imgs, (rr[1]-s1[1])*(s2[1]-s3[1]) / d);
                        end if;
                    end if;
                end for;
                if not ok then continue; end if;

                for idx in [1..3] do
                    x0 := imgs[idx];
                    if x0 eq 0 or x0 eq 1 then continue; end if;
                    if (1 - x0) eq 0 then continue; end if;
                    orb := {x0, 1 - 1/x0, 1/(1 - x0)};
                    if orb eq Set(imgs) then
                        return true, x0;
                    end if;
                end for;
            end for;
        end for;
    end for;
    return false, F!0;
end function;

// Build Q(zeta_7) as degree-3 extension of K
PK<u> := PolynomialRing(K);
cyc7 := u^6+u^5+u^4+u^3+u^2+u+1;
fac_cyc := Factorization(cyc7);
printf "Cyclotomic poly over K factors as degrees %o\n", [Degree(f[1]) : f in fac_cyc];
L7<z7> := ext<K | fac_cyc[1][1]>;
printf "Q(zeta_7) built as degree-%o extension of K\n", Degree(L7, K);
PL7<tL> := PolynomialRing(L7);

// Try all pair-of-pairs per complex, use first that gives a Z/3Z orbit
// Conic index for pair (a,b) with a<b: sequential in the double loop
function ConicIdx(a, b)
    // a in [1..6], b in [a+1..6]
    idx := 0;
    for aa in [1..a-1] do idx +:= 6 - aa; end for;
    return idx + b - a;
end function;

for ci in [1..63] do
    sd := steiner_data_K[ci];
    cpairs := sd[1];

    found := false;
    lam := K!0;
    F := K;
    best_degs := [];
    best_field := "";

    for pi1 in [1..6] do
        if found then break; end if;
        for pi2 in [pi1+1..6] do
            pa := cpairs[pi1]; pb := cpairs[pi2];
            cidx := ConicIdx(pi1, pi2);
            Qc := sd[2][cidx];
            a_coeff := decomps[(ci-1)*15 + cidx][4];
            b_coeff := decomps[(ci-1)*15 + cidx][5];

            p := DetPoly(pa, pb, Qc, a_coeff, b_coeff);
            fac := Factorization(p);
            degs := [Degree(f[1]) : f in fac];

            if not &and[d eq 1 : d in degs] then continue; end if;

            rts := [<K!(-Coefficient(f[1],0)/Coefficient(f[1],1)), false> : f in fac];
            Append(~rts, <K!0, true>);

            found_here, lam_here := FindOrbit(rts);
            if found_here then
                found := true;
                lam := lam_here;
                F := K;
                best_degs := degs;
                best_field := "K";
                break;
            end if;
        end for;
    end for;

    if not found then
        // None of the fully-split pair-of-pairs worked. Use first pair, extend field.
        pa := cpairs[1]; pb := cpairs[2];
        Qc := sd[2][1];
        a_coeff := decomps[(ci-1)*15 + 1][4];
        b_coeff := decomps[(ci-1)*15 + 1][5];
        p := DetPoly(pa, pb, Qc, a_coeff, b_coeff);
        fac := Factorization(p);
        best_degs := [Degree(f[1]) : f in fac];

        F := K;
        PF := PolynomialRing(F);
        fac_ext := Factorization(PF ! p);
        while not &and[Degree(f[1]) eq 1 : f in fac_ext] do
            for ff in fac_ext do
                if Degree(ff[1]) gt 1 then
                    F := ext<F | ff[1]>;
                    break;
                end if;
            end for;
            PF := PolynomialRing(F);
            fac_ext := Factorization(PF ! p);
        end while;
        best_field := Sprintf("deg%o", AbsoluteDegree(F) div 2);
        rts := [<F!(-Coefficient(f[1],0)/Coefficient(f[1],1)), false> : f in fac_ext];
        Append(~rts, <F!0, true>);

        found, lam := FindOrbit(rts);
    else
        // already found
    end if;

4.0.1372.1.4.0.1372.1.
    if not found then
        print "NO Z/3Z orbit";
        continue;
    end if;

    // j-invariant
    disc := lam^2 - lam + 1;
    if disc eq 0 then
        print "degenerate (disc=0)";
        continue;
    end if;

    is_sq, sq_v := IsSquare(disc);
    if is_sq then
        s := (1-lam)*(lam+sq_v)^2;
        if s eq 0 or s eq 1 then print "degenerate (s=0 or 1)"; continue; end if;
        j := 2^8*(1-s*(1-s))^3/(s^2*(1-s)^2);
        mp := MinimalPolynomial(j);
        printf "j min poly = %o\n", mp;
    else
        PF := PolynomialRing(F);
        F2<sq2> := ext<F | PF![-disc,0,1]>;
        lam2 := F2!lam;
        s := (1-lam2)*(lam2+sq2)^2;
        if s eq 0 or s eq 1 then print "degenerate (s=0 or 1)"; continue; end if;
        j := 2^8*(1-s*(1-s))^3/(s^2*(1-s)^2);
        mp := MinimalPolynomial(j);
        printf "j min poly = %o\n", mp;
    end if;
end for;

// =====================================================================
// Part 11: Verify Z/3Z orbit consistency
// =====================================================================

print "\n=== Z/3Z action on bitangent lines and Steiner complexes ===";

// Z/3Z acts by (x:y:z) -> (y:z:x), so on dual coords [A:B:C] -> [C:A:B]
// Find how this permutes the 28 bitangent lines

function NormLine(L)
    if L[3] ne 0 then return [L[1]/L[3], L[2]/L[3], K!1]; end if;
    if L[2] ne 0 then return [L[1]/L[2], K!1, K!0]; end if;
    return [K!1, K!0, K!0];
end function;

sigma := [];  // sigma[i] = j means Z/3Z sends line i to line j
for i in [1..28] do
    L := bitangent_lines[i];
    // Image: [A:B:C] -> [C:A:B]
    img := NormLine([L[3], L[1], L[2]]);
    found := 0;
    for j in [1..28] do
        if NormLine(bitangent_lines[j]) eq img then
            found := j; break;
        end if;
    end for;
    Append(~sigma, found);
end for;
printf "Z/3Z permutation of 28 lines: %o\n", sigma;

// Verify it's order 3
sigma2 := [sigma[sigma[i]] : i in [1..28]];
sigma3 := [sigma[sigma[sigma[i]]] : i in [1..28]];
assert sigma3 eq [i : i in [1..28]];
print "Verified: sigma^3 = identity";

// Fixed lines
fixed := [i : i in [1..28] | sigma[i] eq i];
printf "Fixed lines: %o\n", fixed;

// Now compute Z/3Z action on Steiner complexes
// A Steiner complex is a set of 6 pairs. sigma acts on pairs: {i,j} -> {sigma(i), sigma(j)}
// Map each complex to a canonical form (sorted set of sorted pairs)
function CanonicalComplex(pairs)
    can := Sort([Sort(p) : p in pairs]);
    return can;
end function;

complex_canon := [];
for ci in [1..63] do
    Append(~complex_canon, CanonicalComplex(steiner_data[ci][1]));
end for;

function FindComplex(can)
    for ci in [1..63] do
        if complex_canon[ci] eq can then return ci; end if;
    end for;
    return 0;
end function;

sigma_complex := [];  // sigma_complex[ci] = image of complex ci under Z/3Z
for ci in [1..63] do
    pairs := steiner_data[ci][1];
    img_pairs := [[sigma[p[1]], sigma[p[2]]] : p in pairs];
    img_can := CanonicalComplex(img_pairs);
    img_ci := FindComplex(img_can);
    Append(~sigma_complex, img_ci);
end for;
printf "Z/3Z permutation of 63 complexes: %o\n", sigma_complex;

// Find orbits
used_ci := {};
z3_orbits := [];
for ci in [1..63] do
    if ci in used_ci then continue; end if;
    orb := [ci];
    Include(~used_ci, ci);
    cur := ci;
    for step in [1..2] do
        cur := sigma_complex[cur];
        if cur notin used_ci then
            Append(~orb, cur);
            Include(~used_ci, cur);
        end if;
    end for;
    Append(~z3_orbits, orb);
end for;

printf "Z/3Z orbits on complexes: %o orbits\n", #z3_orbits;
printf "Orbit sizes: %o\n", Sort([#o : o in z3_orbits]);
print "\nOrbit details:";
for idx in [1..#z3_orbits] do
    o := z3_orbits[idx];
    printf "  Orbit %o: complexes %o\n", idx, o;
end for;
