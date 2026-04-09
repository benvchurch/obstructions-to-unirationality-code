/*******************************************************************************
 * steiner_genus2.m
 *
 * Given a smooth plane quartic F over Q, compute:
 *   1. The 28 bitangent lines (over the splitting field)
 *   2. The 63 Steiner complexes
 *   3. Witnessing conics for each pair-of-pairs
 *   4. Quartic decompositions a*F = L_i*L_j*L_k*L_l + b*Q^2
 *   5. Genus-2 curves via det(Q1 + 2t*Q2 + t^2*Q3)
 *
 * INPUT: Set the quartic form F_input below (homogeneous degree 4 in x,y,z).
 *
 * The script is self-contained. No external dependencies.
 ******************************************************************************/

// =====================================================================
// INPUT: Define your quartic here
// =====================================================================

QQ := Rationals();
P2Q<x,y,z> := ProjectiveSpace(QQ, 2);

// Klein twist: C_twist
F_input := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
           - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);

C_Q := Curve(P2Q, F_input);
assert IsNonsingular(C_Q);
print "Quartic is smooth over Q.";

// =====================================================================
// STEP 0: Find a good prime and compute bitangent lines over F_p
// =====================================================================

RQ<xq,yq,zq> := PolynomialRing(QQ, 3);
F_poly := Evaluate(F_input, [xq, yq, zq]);

function FindBitangentsFp(fp_proj, Fp)
    Runi<t> := PolynomialRing(Fp);
    lines := [];

    // Lines [A:B:1]
    for A in Fp do
        for B in Fp do
            restricted := Evaluate(fp_proj, [t, Fp!1, -A*t - B]);
            if Degree(restricted) lt 0 then continue; end if;
            fac := Factorization(restricted);
            if &and[e[2] mod 2 eq 0 : e in fac] then
                Append(~lines, [A, B, Fp!1]);
            end if;
        end for;
    end for;

    // Lines [A:1:0]
    for A in Fp do
        restricted := Evaluate(fp_proj, [t, -A*t, Fp!1]);
        if Degree(restricted) lt 0 then continue; end if;
        fac := Factorization(restricted);
        if &and[e[2] mod 2 eq 0 : e in fac] then
            Append(~lines, [A, Fp!1, Fp!0]);
        end if;
    end for;

    // Line [1:0:0] i.e. x=0
    restricted := Evaluate(fp_proj, [Fp!0, t, Fp!1]);
    if Degree(restricted) ge 0 then
        fac := Factorization(restricted);
        if &and[e[2] mod 2 eq 0 : e in fac] then
            Append(~lines, [Fp!1, Fp!0, Fp!0]);
        end if;
    end if;

    return lines;
end function;

good_p := 0;
lines_Fp := [];
printf "Searching for a prime with 28 F_p-rational bitangent lines...\n";
for p in [29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
          101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
          167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
          239, 241, 251, 257, 263, 269, 271, 277, 281, 283] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp_proj := Evaluate(F_poly, [xp, yp, zp]);
    Cp := Curve(P2p, fp_proj);
    if not IsNonsingular(Cp) then continue; end if;
    ls := FindBitangentsFp(fp_proj, Fp);
    printf "  p=%o: %o bitangent lines\n", p, #ls;
    if #ls eq 28 then
        good_p := p;
        lines_Fp := ls;
        break;
    end if;
end for;

if good_p eq 0 then
    error "No suitable prime found among candidates. Try larger primes.";
end if;

p := good_p;
Fp := GF(p);
P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
fp_proj := Evaluate(F_poly, [xp, yp, zp]);
Cp := Curve(P2p, fp_proj);
printf "\nUsing p = %o with 28 bitangent lines.\n", p;

// =====================================================================
// STEP 1: Function field and Steiner complexes via J[2]
// =====================================================================
// Use the explicit function field FF = Fp(t)[u]/(f(t,u,1)) to avoid
// brittle scheme-intersection code. For each pair of bitangent lines,
// div(L_i/L_j) = 2*(D_i - D_j) as a divisor on C, so the half-divisor
// gives the J[2] class directly.

print "\n=== Building function field ===";

// Build f(t, u, 1) from F_poly
Rp<X,Y,Z> := PolynomialRing(Fp, 3);
FKp := Evaluate(F_poly, [X, Y, Z]);

Fpt<t_var> := FunctionField(Fp);
Ku<u_var> := PolynomialRing(Fpt);

f_u := Ku!0;
for j in [0..4] do
    coeff_j := Fpt!0;
    for i in [0..4-j] do
        k := 4 - i - j;
        c := MonomialCoefficient(FKp, X^i * Y^j * Z^k);
        if c ne 0 then coeff_j +:= (Fpt!c) * t_var^i; end if;
    end for;
    f_u +:= coeff_j * u_var^j;
end for;
printf "Affine equation: %o = 0\n", f_u;
assert Degree(f_u) ge 3;

FF<uu> := FunctionField(f_u);
elt_t := FF!t_var;

Cl, mp := ClassGroup(FF);
invs := Invariants(Cl);
printf "Class group invariants: %o\n", invs;

// J[2] extraction: for each class group element, extract the mod-2 coordinates
even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
F2 := GF(2);
dim := #even_idx;

function ClassJ2(D)
    cl := D @@ mp;
    coords := Eltseq(cl);
    j2 := [];
    for k in [1..#invs] do
        if invs[k] eq 0 then continue; end if;
        if invs[k] mod 2 ne 0 then continue; end if;
        // For Z/nZ (n even), the 2-torsion is {0, n/2}.
        // Map: a -> (2*a div n) mod 2, which sends 0->0 and n/2->1.
        Append(~j2, (2 * coords[k] div invs[k]) mod 2);
    end for;
    return j2;
end function;

// For each bitangent line [A,B,C], build the function (Ax+By+Cz)/z = At+Bu+C
// as an element of FF
line_fns := [];
for i in [1..28] do
    A := Fp!lines_Fp[i][1]; B := Fp!lines_Fp[i][2]; C := Fp!lines_Fp[i][3];
    f_L := A*elt_t + B*uu + FF!C;
    Append(~line_fns, f_L);
end for;

// Compute half-divisors relative to a reference line
// D_i - D_ref = (1/2) * div(L_i / L_ref)
print "\n=== Computing Steiner complexes via J[2] ===";

ref := 1;  // use line 1 as reference
half_divs := [];
for i in [1..28] do
    if i eq ref then
        Append(~half_divs, Zero(DivisorGroup(FF)));
        continue;
    end if;
    ratio := line_fns[i] / line_fns[ref];
    D_ratio := Divisor(ratio);
    // Verify all valuations are even (bitangent property)
    supp := Support(D_ratio);
    all_even := true;
    for P in supp do
        v := Valuation(ratio, P);
        if v mod 2 ne 0 then all_even := false; break; end if;
    end for;
    if not all_even then
        printf "WARNING: line %o has odd valuations in div(L_%o/L_%o)\n", i, i, ref;
        Append(~half_divs, Zero(DivisorGroup(FF)));
        continue;
    end if;
    D_half := D_ratio div 2;
    Append(~half_divs, D_half);
end for;
print "Half-divisors computed for all 28 lines.";

// Group pairs by [D_i - D_j] = half_divs[i] - half_divs[j] in J[2]
class_to_pairs := AssociativeArray();
for i in [1..28] do
    for j in [i+1..28] do
        D_diff := half_divs[i] - half_divs[j];
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
print "63 Steiner complexes, each with 6 pairs.";

// =====================================================================
// STEP 2: Contact quadratics and witnessing conics over F_p
// =====================================================================

print "\n=== Computing witnessing conics ===";

Runi<tt> := PolynomialRing(Fp);

contact_quads := [];
param_type := [];

for i in [1..28] do
    A := lines_Fp[i][1]; B := lines_Fp[i][2]; CC := lines_Fp[i][3];
    if CC ne 0 then
        restricted := Evaluate(fp_proj, [tt, Fp!1, (-A*tt - B)/CC]);
        restricted *:= CC^4;
        Append(~param_type, <3, A, B, CC>);
    elif B ne 0 then
        restricted := Evaluate(fp_proj, [tt, -A*tt/B, Fp!1]);
        restricted *:= B^4;
        Append(~param_type, <2, A, B, CC>);
    else
        restricted := Evaluate(fp_proj, [Fp!0, tt, Fp!1]);
        Append(~param_type, <1, A, B, CC>);
    end if;

    fac := Factorization(restricted);
    assert &and[e[2] mod 2 eq 0 : e in fac];
    if #fac eq 0 then
        // restricted is a nonzero constant (contact points at infinity in this chart)
        assert IsSquare(restricted);
        sq_root := Parent(restricted)!Sqrt(Fp!restricted);
    else
        sq_root_monic := &*[e[1]^(e[2] div 2) : e in fac];
        ratio_val := LeadingCoefficient(restricted) / LeadingCoefficient(sq_root_monic)^2;
        assert IsSquare(ratio_val);
        sq_root := Sqrt(ratio_val) * sq_root_monic;
    end if;

    al := Degree(sq_root) ge 2 select Coefficient(sq_root, 2) else Fp!0;
    be := Degree(sq_root) ge 1 select Coefficient(sq_root, 1) else Fp!0;
    ga := Coefficient(sq_root, 0);
    Append(~contact_quads, [al, be, ga]);
end for;
print "Contact quadratics computed.";

function RestrictionMatrix(i)
    M := ZeroMatrix(Fp, 3, 6);
    pt := param_type[i];
    AA := pt[2]; BB := pt[3]; CC := pt[4];
    if pt[1] eq 3 then
        a := -AA/CC; b := -BB/CC;
        M[1,1] := 1; M[1,3] := a; M[1,6] := a^2;
        M[2,2] := 1; M[2,3] := b; M[2,5] := a; M[2,6] := 2*a*b;
        M[3,4] := 1; M[3,5] := b; M[3,6] := b^2;
    elif pt[1] eq 2 then
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

function FindConic(i, j, k, l)
    M := ZeroMatrix(Fp, 12, 10);
    lines_idx := [i, j, k, l];
    for idx in [1..4] do
        m := lines_idx[idx];
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
    if Dimension(N) eq 0 then
        return [Fp | 0,0,0,0,0,0], false;
    end if;
    v := N.1;
    return [v[c] : c in [1..6]], true;
end function;

steiner_data := [];
complex_idx := 0;
for key in Keys(class_to_pairs) do
    complex_idx +:= 1;
    cpairs := class_to_pairs[key];
    conics := [];
    for a in [1..6] do
        for b in [a+1..6] do
            pa := cpairs[a]; pb := cpairs[b];
            conic, ok := FindConic(pa[1], pa[2], pb[1], pb[2]);
            if not ok then
                printf "WARNING: no conic for complex %o, sub-pair %o,%o\n",
                    complex_idx, a, b;
            end if;
            Append(~conics, conic);
        end for;
    end for;
    Append(~steiner_data, <cpairs, conics, key>);
end for;

// Verify conics
print "Verifying conics...";
verified := 0;
for ci in [1..63] do
    sd := steiner_data[ci];
    cpairs := sd[1]; conics := sd[2];
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
                lambda := Fp!0;
                for r in [1..3] do
                    if hm[r] ne 0 then lambda := restr[r]/hm[r]; break; end if;
                end for;
                if restr ne [lambda*hm[r] : r in [1..3]] then ok := false; end if;
            end for;
            if ok then verified +:= 1; end if;
        end for;
    end for;
end for;
printf "Verified %o / 945 conics.\n", verified;

// =====================================================================
// STEP 3: Display Steiner complexes
// =====================================================================

print "\n========================================";
print "The 63 Steiner complexes";
print "========================================";
for ci in [1..#steiner_data] do
    sd := steiner_data[ci];
    printf "Complex #%o: ", ci;
    for k in [1..6] do
        printf "{%o,%o}", sd[1][k][1], sd[1][k][2];
        if k lt 6 then printf " "; end if;
    end for;
    involved := {};
    for pr in sd[1] do Include(~involved, pr[1]); Include(~involved, pr[2]); end for;
    printf "  [%o lines]\n", #involved;
end for;

line_count := AssociativeArray();
for i in [1..28] do line_count[i] := 0; end for;
for sd in steiner_data do
    for pr in sd[1] do line_count[pr[1]] +:= 1; line_count[pr[2]] +:= 1; end for;
end for;
counts := [line_count[i] : i in [1..28]];
assert &and[c eq 27 : c in counts];
print "Each line in exactly 27 complexes.";

// =====================================================================
// STEP 4: Quartic decompositions a*F = L_i*L_j*L_k*L_l + b*Q^2
// =====================================================================

print "\n=== Quartic decompositions ===";

RR<xx,yy,zz> := PolynomialRing(Fp, 3);
F_Fp := Evaluate(F_poly, [xx, yy, zz]);
mons4 := MonomialsOfDegree(RR, 4);

function CoeffVec(poly)
    return [MonomialCoefficient(poly, m) : m in mons4];
end function;

v_F := CoeffVec(F_Fp);

function LProdCoeffs(L1, L2)
    return [L1[1]*L2[1], L1[1]*L2[2]+L1[2]*L2[1], L1[1]*L2[3]+L1[3]*L2[1],
            L1[2]*L2[2], L1[2]*L2[3]+L1[3]*L2[2], L1[3]*L2[3]];
end function;

function QuadMat(coeffs)
    return Matrix(Fp, 3, 3, [
        [coeffs[1], coeffs[2]/2, coeffs[3]/2],
        [coeffs[2]/2, coeffs[4], coeffs[5]/2],
        [coeffs[3]/2, coeffs[5]/2, coeffs[6]]
    ]);
end function;

decomps := [];
for ci in [1..63] do
    sd := steiner_data[ci];
    cpairs := sd[1]; conics := sd[2];
    conic_idx := 0;
    for a in [1..6] do
        for b in [a+1..6] do
            conic_idx +:= 1;
            pa := cpairs[a]; pb := cpairs[b];
            Qc := conics[conic_idx];
            if Qc eq [Fp|0,0,0,0,0,0] then continue; end if;

            Li := lines_Fp[pa[1]]; Lj := lines_Fp[pa[2]];
            Lk := lines_Fp[pb[1]]; Ll := lines_Fp[pb[2]];
            prod_L := (Li[1]*xx+Li[2]*yy+Li[3]*zz)*(Lj[1]*xx+Lj[2]*yy+Lj[3]*zz)
                     *(Lk[1]*xx+Lk[2]*yy+Lk[3]*zz)*(Ll[1]*xx+Ll[2]*yy+Ll[3]*zz);
            Q_poly := Qc[1]*xx^2+Qc[2]*xx*yy+Qc[3]*xx*zz
                     +Qc[4]*yy^2+Qc[5]*yy*zz+Qc[6]*zz^2;

            vprod := CoeffVec(prod_L);
            vQ2 := CoeffVec(Q_poly^2);
            M := Matrix(Fp, 3, #mons4, [v_F, vprod, vQ2]);
            N := Nullspace(M);
            if Dimension(N) ge 1 then
                rel := N.1;
                if rel[2] ne 0 then
                    a_coeff := -rel[1]/rel[2];
                    b_coeff := rel[3]/rel[2];
                    Append(~decomps, <ci, pa, pb, Qc, a_coeff, b_coeff>);
                end if;
            end if;
        end for;
    end for;
end for;
printf "Quartic decompositions found: %o\n", #decomps;

// =====================================================================
// STEP 5: Genus-2 curves via determinantal pencil
// =====================================================================

print "\n=== Genus-2 curves ===";

Pt<t_pen> := PolynomialRing(Fp);

// Given a*F = prod + b*Q^2, the correct pencil is:
//   Q1 = b * L_i*L_j, Q3 = -L_k*L_l, Q2 = b * Q
// Then Q1*Q3 - Q2^2 = -ab*F
// Genus-2: y^2 = -det(Q1 + 2t*Q2 + t^2*Q3)
function MakeGenus2(pa, pb, Qc, a_coeff, b_coeff)
    Q1c := LProdCoeffs(lines_Fp[pa[1]], lines_Fp[pa[2]]);
    Q1c := [b_coeff * e : e in Q1c];
    Q3c := LProdCoeffs(lines_Fp[pb[1]], lines_Fp[pb[2]]);
    Q3c := [-e : e in Q3c];
    Q2c := [Fp | b_coeff * Qc[idx] : idx in [1..6]];

    M1 := QuadMat(Q1c); M2 := QuadMat(Q2c); M3 := QuadMat(Q3c);
    M := ZeroMatrix(Pt, 3, 3);
    for i in [1..3] do
        for j in [1..3] do
            M[i,j] := Pt!(M1[i,j]) + 2*t_pen*Pt!(M2[i,j]) + t_pen^2*Pt!(M3[i,j]);
        end for;
    end for;
    return -Determinant(M);
end function;

genus2_data := AssociativeArray();
for d in decomps do
    ci := d[1];
    if IsDefined(genus2_data, ci) then continue; end if;
    dp := MakeGenus2(d[2], d[3], d[4], d[5], d[6]);
    if Degree(dp) ge 5 then
        genus2_data[ci] := dp;
    end if;
end for;

printf "Genus-2 curves computed for %o / 63 complexes.\n", #Keys(genus2_data);

print "\n--- Sample genus-2 curves (y^2 = f(t)) ---";
count := 0;
for ci in Sort(Setseq(Keys(genus2_data))) do
    count +:= 1;
    if count gt 10 then break; end if;
    printf "Complex #%o: y^2 = %o\n", ci, genus2_data[ci];
end for;

// =====================================================================
// STEP 6: Compute Igusa invariants (over F_p)
// =====================================================================

print "\n=== Igusa invariants ===";
inv_counts := AssociativeArray();
for ci in Sort(Setseq(Keys(genus2_data))) do
    f_g2 := genus2_data[ci];
    try
        H := HyperellipticCurve(f_g2);
        I := IgusaInvariants(H);
        abs_inv := I[5] ne 0 select I[1]^5/I[5] else Fp!0;
        printf "Complex #%o: I2^5/I10 = %o\n", ci, abs_inv;
        key := Sprintf("%o", abs_inv);
        if not IsDefined(inv_counts, key) then inv_counts[key] := 0; end if;
        inv_counts[key] +:= 1;
    catch e
        printf "Complex #%o: could not compute Igusa invariants\n", ci;
    end try;
end for;
print "\n--- Summary: distinct I2^5/I10 values ---";
for k in Sort(Setseq(Keys(inv_counts))) do
    printf "  I2^5/I10 = %o : %o complexes\n", k, inv_counts[k];
end for;

// =====================================================================
// STEP 7: Bitangent lines, genus-2 curves, and Igusa invariants
//         over a number field
// =====================================================================

print "\n========================================";
print "NUMBER FIELD COMPUTATION";
print "========================================";

// Strategy: find the bitangent field via elimination, then solve for all 28 lines
// by root-finding. Handle three chart cases:
//   (1) z != 0 lines: z = -(ax+by)
//   (2) z = 0, y != 0 lines: y = -cx (i.e., cx + y = 0)
//   (3) z = 0, y = 0 line: x = 0

// === Chart 1: z != 0 ===
print "\nBuilding tangency ideal (z != 0 chart)...";
RR5<a_var, b_var, al, be, ga> := PolynomialRing(QQ, 5);
Rt5<ttt> := PolynomialRing(RR5);

f_restr := Evaluate(F_poly, [ttt, RR5!1, -a_var*ttt - b_var]);
sq := (al*ttt^2 + be*ttt + ga)^2;
eqns := [Coefficient(f_restr, d) - Coefficient(sq, d) : d in [0..4]];

I_bt := ideal<RR5 | eqns>;
I_ab := EliminationIdeal(I_bt, {a_var, b_var});
gens_ab := Basis(I_ab);
printf "Bitangent ideal in (a,b): %o generators.\n", #gens_ab;

// Univariate polynomials
RR2<aa, bb> := PolynomialRing(QQ, 2);
gens2 := [Evaluate(g, [aa, bb, 0, 0, 0]) : g in gens_ab];
I2 := ideal<RR2 | gens2>;
I_b_only := EliminationIdeal(I2, {bb});
fb := UnivariatePolynomial(Basis(I_b_only)[1]);
printf "Univariate polynomial in b: degree %o\n", Degree(fb);

fac_b := Factorization(fb);
printf "Factorization of b-poly over Q:\n";
for f in fac_b do printf "  degree %o (mult %o)\n", Degree(f[1]), f[2]; end for;

// === Chart 2: z = 0, y != 0 ===
// Line cx + y = 0 with z free: parametrize as (t, -ct, s)
// Restriction F(t, -ct, s) must be a perfect square of a binary quadratic
print "\nBuilding tangency ideal (z = 0 chart)...";
RR4<c_var, al2, be2, ga2> := PolynomialRing(QQ, 4);
Rts<ss, tt2> := PolynomialRing(RR4, 2);
f_restr2 := Evaluate(F_poly, [tt2, -c_var*tt2, ss]);
sq2 := (al2*tt2^2 + be2*tt2*ss + ga2*ss^2)^2;
// Extract coefficients of t^4, t^3*s, t^2*s^2, t*s^3, s^4
mons_ts := [tt2^4, tt2^3*ss, tt2^2*ss^2, tt2*ss^3, ss^4];
eqns2 := [MonomialCoefficient(f_restr2, m) - MonomialCoefficient(sq2, m) : m in mons_ts];
I_bt2 := ideal<RR4 | eqns2>;
I_c := EliminationIdeal(I_bt2, {c_var});
gens_c := Basis(I_c);
if #gens_c gt 0 then
    fc := UnivariatePolynomial(gens_c[1]);
    printf "z=0 bitangent polynomial in c: degree %o\n", Degree(fc);
    fac_c := Factorization(fc);
    printf "Factorization:\n";
    for f in fac_c do printf "  degree %o (mult %o)\n", Degree(f[1]), f[2]; end for;
else
    fc := Parent(fb)!1;
    print "No z=0 bitangent conditions found.";
end if;

// === Compute splitting field from all chart polynomials ===
all_irred := [f[1] : f in fac_b | Degree(f[1]) gt 1];
if Degree(fc) gt 0 then
    all_irred cat:= [f[1] : f in fac_c | Degree(f[1]) gt 1];
end if;

if #all_irred eq 0 then
    K := QQ;
    printf "All bitangent coordinates are rational.\n";
else
    prod_fac := &*all_irred;
    K<w> := SplittingField(prod_fac);
    printf "Splitting field K has degree %o over Q.\n", Degree(K, QQ);
end if;

// === Solve for all bitangent lines over K ===
Ra_K<aK> := PolynomialRing(K);
lines_K := [];

// Chart 1: z != 0 lines. For each b-root, find all a-roots.
fb_K := ChangeRing(fb, K);
b_roots := [r[1] : r in Roots(fb_K)];
printf "b-roots over K: %o\n", #b_roots;

for b0 in b_roots do
    // Substitute b=b0 into the ideal generators to get conditions on a
    a_polys := [];
    for g in gens_ab do
        gab := Evaluate(g, [aa, bb, 0, 0, 0]);
        // Substitute bb -> b0 to get a univariate in aa
        ga_uni := Evaluate(gab, [aK, Ra_K!b0]);
        if Degree(ga_uni) ge 1 then Append(~a_polys, ga_uni); end if;
    end for;
    if #a_polys eq 0 then continue; end if;
    g_a := GCD(a_polys);
    if Degree(g_a) ge 1 then
        a_roots := [r[1] : r in Roots(g_a)];
        for a0 in a_roots do
            // Verify tangency: F(t, 1, -(a0*t + b0)) must be a perfect square
            f_check := Evaluate(F_poly, [aK, K!1, -a0*aK - K!b0]);
            if Degree(f_check) lt 0 then continue; end if;
            is_bt := true;
            if Degree(f_check) ge 1 then
                fac_check := Factorization(f_check);
                is_bt := &and[e[2] mod 2 eq 0 : e in fac_check];
            end if;
            // Degree 0 (constant) means all intersection at y=0: hyperflex
            if is_bt then
                Append(~lines_K, [a0, b0, K!1]);
            end if;
        end for;
    end if;
end for;
printf "Bitangent lines from z!=0 chart: %o\n", #lines_K;

// Chart 2: z = 0 lines (cx + y = 0)
if Degree(fc) gt 0 then
    fc_K := ChangeRing(fc, K);
    c_roots := [r[1] : r in Roots(fc_K)];
    for c0 in c_roots do
        // Verify: F(t, -c0*t, s) should be a perfect square as binary quartic
        // Check dehomogenized: F(t, -c0*t, 1)
        f_check := Evaluate(F_poly, [aK, -c0*aK, K!1]);
        is_bt := true;
        if Degree(f_check) ge 1 then
            fac_check := Factorization(f_check);
            is_bt := &and[e[2] mod 2 eq 0 : e in fac_check];
        end if;
        if not is_bt and Degree(f_check) le 0 then
            // Degree 0 or negative: all tangencies at s=0, check F(1, -c0, 0)
            is_bt := true;
        end if;
        if is_bt then
            Append(~lines_K, [c0, K!1, K!0]);
        end if;
    end for;
end if;

// Chart 3: x = 0
f_x0 := Evaluate(F_poly, [Ra_K!0, aK, K!1]);
if Degree(f_x0) ge 1 then
    fac_x0 := Factorization(f_x0);
    if &and[e[2] mod 2 eq 0 : e in fac_x0] then
        Append(~lines_K, [K!1, K!0, K!0]);
    end if;
elif Evaluate(F_poly, [QQ!0, QQ!1, QQ!0]) eq 0 then
    // y^4 = 0 at (0:1:0), so x=0 is tangent with mult 4
    Append(~lines_K, [K!1, K!0, K!0]);
end if;

// Remove duplicates (normalize by first nonzero coordinate)
function NormLineK(L)
    for k in [1..3] do
        if L[k] ne 0 then return [L[j]/L[k] : j in [1..3]]; end if;
    end for;
    return L;
end function;
norm_set := {};
lines_K_unique := [];
for L in lines_K do
    nL := NormLineK(L);
    key := Sprintf("%o", nL);
    if key notin norm_set then
        Include(~norm_set, key);
        Append(~lines_K_unique, L);
    end if;
end for;
lines_K := lines_K_unique;

printf "Total bitangent lines over K (deduplicated): %o\n", #lines_K;

if #lines_K ne 28 then
    printf "WARNING: expected 28, got %o.\n", #lines_K;
    if #lines_K lt 28 then
        print "Number field genus-2 computation skipped.\n\nDone.";
        quit;
    end if;
end if;

// === Match K-lines to F_p lines (same index for Steiner complex reuse) ===
// Reduce each K-line mod p and match to lines_Fp
print "Matching K-lines to F_p lines...";

// Build a consistent embedding K -> F_p.
// Express K-elements via Eltseq (power basis in w) and evaluate at one F_p root.
if Type(K) eq FldRat then
    // K = Q, reduction is trivial
    function ReduceModP(val, Fp_field)
        return Fp_field!val;
    end function;
else
    // Find the minimal polynomial of the generator w and its F_p roots
    w_minpoly := MinimalPolynomial(K.1);
    w_roots_Fp := [r[1] : r in Roots(ChangeRing(w_minpoly, Fp))];
    printf "Generator w has %o roots mod %o.\n", #w_roots_Fp, p;
    // We'll try each root to find the one that gives a consistent line matching.
    // For now, store them and pick later.
    function ReduceViaRoot(val, Fp_field, wroot)
        if Type(val) eq FldRatElt or Type(val) eq RngIntElt then
            return Fp_field!val;
        end if;
        cs := Eltseq(val);
        result := Fp_field!0;
        for i in [1..#cs] do
            result +:= Fp_field!cs[i] * wroot^(i-1);
        end for;
        return result;
    end function;
end if;

function NormFp(L)
    for k in [1..3] do
        if L[k] ne 0 then return [L[j]/L[k] : j in [1..3]]; end if;
    end for;
    return L;
end function;

// Build lookup from normalized F_p lines to their index
fp_lookup := AssociativeArray();
for i in [1..28] do
    nL := NormFp(lines_Fp[i]);
    key := Sprintf("%o", nL);
    fp_lookup[key] := i;
end for;

// Match each K-line to its F_p counterpart
// Try each candidate w-root to find one giving 28/28 matches.
lines_K_ordered := [lines_K[1] : i in [1..28]];  // placeholder
best_matched := 0;
best_wroot := Fp!0;

if Type(K) eq FldRat then
    // Trivial case: K = Q
    for ki in [1..28] do
        LK := lines_K[ki];
        LK_Fp := [Fp!LK[j] : j in [1..3]];
        nL := NormFp(LK_Fp);
        key := Sprintf("%o", nL);
        if IsDefined(fp_lookup, key) then
            fp_idx := fp_lookup[key];
            lines_K_ordered[fp_idx] := LK;
            best_matched +:= 1;
        end if;
    end for;
    printf "Matched %o / 28 lines.\n", best_matched;
else
    for wi in [1..#w_roots_Fp] do
        wr := w_roots_Fp[wi];
        test_ordered := [lines_K[1] : i in [1..28]];
        test_matched := 0;
        for ki in [1..28] do
            LK := lines_K[ki];
            LK_Fp := [ReduceViaRoot(LK[j], Fp, wr) : j in [1..3]];
            nL := NormFp(LK_Fp);
            key := Sprintf("%o", nL);
            if IsDefined(fp_lookup, key) then
                fp_idx := fp_lookup[key];
                test_ordered[fp_idx] := LK;
                test_matched +:= 1;
            end if;
        end for;
        printf "  w-root #%o (%o): matched %o / 28\n", wi, wr, test_matched;
        if test_matched gt best_matched then
            best_matched := test_matched;
            best_wroot := wr;
            lines_K_ordered := test_ordered;
        end if;
    end for;
    printf "Best match: %o / 28 using w-root %o\n", best_matched, best_wroot;

    // Define the consistent ReduceModP using the best root
    chosen_wroot := best_wroot;
    function ReduceModP(val, Fp_field)
        return ReduceViaRoot(val, Fp_field, chosen_wroot);
    end function;
end if;

if best_matched eq 28 then
    lines_K := lines_K_ordered;
else
    printf "WARNING: only matched %o lines. Some K-lines may not reduce cleanly to F_p.\n", best_matched;
end if;

// =====================================================================
// STEP 8: Conics, decompositions, genus-2 curves, Igusa invariants over K
// =====================================================================

print "\n=== Computing genus-2 curves over K ===";

RK<xK,yK,zK> := PolynomialRing(K, 3);
FK := Evaluate(F_poly, [xK, yK, zK]);
mons4K := MonomialsOfDegree(RK, 4);

function CoeffVecK(poly)
    return [MonomialCoefficient(poly, m) : m in mons4K];
end function;
vFK := CoeffVecK(FK);

function LinFormK(idx)
    return lines_K[idx][1]*xK + lines_K[idx][2]*yK + lines_K[idx][3]*zK;
end function;

function LProdCoeffsK(L1, L2)
    return [L1[1]*L2[1], L1[1]*L2[2]+L1[2]*L2[1], L1[1]*L2[3]+L1[3]*L2[1],
            L1[2]*L2[2], L1[2]*L2[3]+L1[3]*L2[2], L1[3]*L2[3]];
end function;

function QuadMatK(coeffs)
    return Matrix(K, 3, 3, [
        [coeffs[1], coeffs[2]/2, coeffs[3]/2],
        [coeffs[2]/2, coeffs[4], coeffs[5]/2],
        [coeffs[3]/2, coeffs[5]/2, coeffs[6]]
    ]);
end function;

// Contact quadratics over K
RKuni<tK> := PolynomialRing(K);
contact_quads_K := [];
param_type_K := [];
for i in [1..28] do
    A := lines_K[i][1]; B := lines_K[i][2]; CC := lines_K[i][3];
    if CC ne 0 then
        restricted := Evaluate(FK, [tK, K!1, (-A*tK - B)/CC]);
        restricted *:= CC^4;
        Append(~param_type_K, <3, A, B, CC>);
    elif B ne 0 then
        restricted := Evaluate(FK, [tK, -A*tK/B, K!1]);
        restricted *:= B^4;
        Append(~param_type_K, <2, A, B, CC>);
    else
        restricted := Evaluate(FK, [RKuni!0, tK, K!1]);
        Append(~param_type_K, <1, A, B, CC>);
    end if;
    fac := Factorization(restricted);
    if #fac eq 0 then
        sq_root := Parent(restricted)!Sqrt(K!restricted);
    else
        sq_root_monic := &*[e[1]^(e[2] div 2) : e in fac];
        ratio_val := LeadingCoefficient(restricted) / LeadingCoefficient(sq_root_monic)^2;
        sq_root := Sqrt(ratio_val) * sq_root_monic;
    end if;
    al_K := Degree(sq_root) ge 2 select Coefficient(sq_root, 2) else K!0;
    be_K := Degree(sq_root) ge 1 select Coefficient(sq_root, 1) else K!0;
    ga_K := Coefficient(sq_root, 0);
    Append(~contact_quads_K, [al_K, be_K, ga_K]);
end for;
print "Contact quadratics over K computed.";

// Note: sign of contact quadratic h_i doesn't affect FindConicK
// (the lambda_i parameter absorbs the sign), so no sign correction needed.

function RestrictionMatrixK(i)
    M := ZeroMatrix(K, 3, 6);
    pt := param_type_K[i];
    AA := pt[2]; BB := pt[3]; CC := pt[4];
    if pt[1] eq 3 then
        a := -AA/CC; b := -BB/CC;
        M[1,1] := 1; M[1,3] := a; M[1,6] := a^2;
        M[2,2] := 1; M[2,3] := b; M[2,5] := a; M[2,6] := 2*a*b;
        M[3,4] := 1; M[3,5] := b; M[3,6] := b^2;
    elif pt[1] eq 2 then
        c := -AA/BB;
        M[1,1] := 1; M[1,2] := c; M[1,4] := c^2;
        M[2,3] := 1; M[2,5] := c;
        M[3,6] := 1;
    else
        M[1,4] := 1; M[2,5] := 1; M[3,6] := 1;
    end if;
    return M;
end function;

function FindConicK(i, j, k, l)
    MM := ZeroMatrix(K, 12, 10);
    lines_idx := [i, j, k, l];
    for idx in [1..4] do
        m := lines_idx[idx];
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

PtK<t_K> := PolynomialRing(K);

genus2_K := AssociativeArray();
igusa_K := AssociativeArray();

for ci in [1..#steiner_data] do
    sd := steiner_data[ci];
    cpairs := sd[1];

    // Try all 15 pair-of-pairs until one gives a valid genus-2 curve
    found_g2 := false;
    conic_fail := 0;
    decomp_fail := 0;
    deg_fail := 0;
    for pi1 in [1..6] do
        if found_g2 then break; end if;
        for pi2 in [pi1+1..6] do
            pa := cpairs[pi1]; pb := cpairs[pi2];
            Qc, ok := FindConicK(pa[1], pa[2], pb[1], pb[2]);
            if not ok then conic_fail +:= 1; continue; end if;

            prod_L := LinFormK(pa[1])*LinFormK(pa[2])*LinFormK(pb[1])*LinFormK(pb[2]);
            Q_poly := Qc[1]*xK^2+Qc[2]*xK*yK+Qc[3]*xK*zK+Qc[4]*yK^2+Qc[5]*yK*zK+Qc[6]*zK^2;
            vprod := CoeffVecK(prod_L);
            vQ2K := CoeffVecK(Q_poly^2);
            matK := Matrix(K, 3, #mons4K, [vFK, vprod, vQ2K]);
            NK := Nullspace(matK);
            if Dimension(NK) eq 0 then decomp_fail +:= 1; continue; end if;
            rel := NK.1;
            if rel[2] eq 0 then decomp_fail +:= 1; continue; end if;
            a_c := -rel[1]/rel[2]; b_c := rel[3]/rel[2];

            Q1c := LProdCoeffsK(lines_K[pa[1]], lines_K[pa[2]]);
            Q1c := [b_c * e : e in Q1c];
            Q3c := LProdCoeffsK(lines_K[pb[1]], lines_K[pb[2]]);
            Q3c := [-e : e in Q3c];
            Q2c := [K | b_c * Qc[idx] : idx in [1..6]];

            M1 := QuadMatK(Q1c); M2 := QuadMatK(Q2c); M3 := QuadMatK(Q3c);
            MK := ZeroMatrix(PtK, 3, 3);
            for ii in [1..3] do
                for jj in [1..3] do
                    MK[ii,jj] := PtK!(M1[ii,jj]) + 2*t_K*PtK!(M2[ii,jj]) + t_K^2*PtK!(M3[ii,jj]);
                end for;
            end for;
            dp := -Determinant(MK);
            if Degree(dp) lt 5 then deg_fail +:= 1; continue; end if;
            genus2_K[ci] := dp;

            HK := HyperellipticCurve(dp);
            IKvals := IgusaInvariants(HK);
            igusa_K[ci] := IKvals;
            found_g2 := true;
            break;
        end for;
    end for;
    if not found_g2 then
        printf "Complex #%o: FAILED (conic=%o, decomp=%o, deg=%o of 15)\n",
            ci, conic_fail, decomp_fail, deg_fail;
    end if;
end for;

printf "Genus-2 curves over K: %o / 63 complexes.\n", #Keys(genus2_K);

// =====================================================================
// STEP 9: Igusa invariants and isomorphism classes
// =====================================================================

print "\n=== Absolute Igusa invariants over K ===";
abs_inv_K := AssociativeArray();
for ci in Sort(Setseq(Keys(igusa_K))) do
    IKvals := igusa_K[ci];
    if IKvals[5] ne 0 then
        j1 := IKvals[1]^5/IKvals[5];
        j2 := IKvals[1]^3*IKvals[2]/IKvals[5];
        j3 := IKvals[1]^2*IKvals[3]/IKvals[5];
        printf "Complex #%o: j1=%o, j2=%o, j3=%o\n", ci, j1, j2, j3;
        abs_inv_K[ci] := [j1, j2, j3];
    else
        printf "Complex #%o: I10=0 (degenerate)\n", ci;
    end if;
end for;

inv_classes := {};
for ci in Keys(abs_inv_K) do Include(~inv_classes, abs_inv_K[ci]); end for;
printf "\nDistinct geometric isomorphism classes: %o\n", #inv_classes;
for cl in inv_classes do
    cnt := #[ci : ci in Keys(abs_inv_K) | abs_inv_K[ci] eq cl];
    printf "  j = %o : %o complexes\n", cl, cnt;
end for;

// =====================================================================
// STEP 10: Elliptic j-invariants via Z/3Z action on branch points
// =====================================================================
// The genus-2 curve y^2 = f(t) has 6 branch points (5 finite roots + infinity
// if deg=5, or 6 finite roots if deg=6). A Z/3Z partition of these 6 points
// into two orbits {x, 1-1/x, 1/(1-x)} determines a cross-ratio lambda,
// from which we get the j-invariant of the associated elliptic curve:
//   disc = lambda^2 - lambda + 1
//   s = (1-lambda)*(lambda + sqrt(disc))^2
//   j = 256*(1 - s*(1-s))^3 / (s^2*(1-s)^2)

print "\n=== Elliptic j-invariants via Z/3Z orbits on branch points ===";

// Search all C(6,3) = 20 partitions of 6 branch points for a Z/3Z orbit
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

j_inv_K := AssociativeArray();

for ci in Sort(Setseq(Keys(genus2_K))) do
    f_g2 := genus2_K[ci];
    fac_g2 := Factorization(f_g2);
    degs := [Degree(f[1]) : f in fac_g2];

    // Build branch points as <value, is_inf> pairs
    // The genus-2 sextic is -det(Q1 + 2tQ2 + t^2 Q3), degree 5 or 6.
    // If degree 5, there is a branch point at infinity.
    rts_K := [];
    all_split := true;
    for f in fac_g2 do
        if Degree(f[1]) eq 1 then
            Append(~rts_K, <K!(-Coefficient(f[1],0)/Coefficient(f[1],1)), false>);
        else
            all_split := false;
        end if;
    end for;
    if Degree(f_g2) le 5 then
        Append(~rts_K, <K!0, true>);  // point at infinity
    end if;

    if not all_split then
        // Sextic doesn't split over K; try extending the field
        F_ext := K;
        PF_ext := PolynomialRing(F_ext);
        fac_ext := Factorization(PF_ext ! f_g2);
        while not &and[Degree(f[1]) eq 1 : f in fac_ext] do
            extended := false;
            for ff in fac_ext do
                if Degree(ff[1]) gt 1 then
                    F_ext := ext<F_ext | ff[1]>;
                    extended := true;
                    break;
                end if;
            end for;
            if not extended then break; end if;
            PF_ext := PolynomialRing(F_ext);
            fac_ext := Factorization(PF_ext ! f_g2);
        end while;
        rts_K := [<F_ext!(-Coefficient(f[1],0)/Coefficient(f[1],1)), false> : f in fac_ext];
        if Degree(f_g2) le 5 then
            Append(~rts_K, <F_ext!0, true>);
        end if;
    end if;

    if #rts_K ne 6 then
        printf "Complex #%o: wrong number of branch points (%o)\n", ci, #rts_K;
        continue;
    end if;

    found_orb, lam := FindOrbit(rts_K);
    if not found_orb then
        printf "Complex #%o: no Z/3Z orbit found\n", ci;
        continue;
    end if;

    // j-invariant from cross-ratio lambda
    F_lam := Parent(lam);
    disc := lam^2 - lam + 1;
    if disc eq 0 then
        printf "Complex #%o: degenerate (disc=0)\n", ci;
        continue;
    end if;

    is_sq, sq_v := IsSquare(disc);
    if not is_sq then
        PF2 := PolynomialRing(F_lam);
        F2<sq2> := ext<F_lam | PF2![-disc,0,1]>;
        lam2 := F2!lam;
        s := (1-lam2)*(lam2+sq2)^2;
    else
        s := (1-lam)*(lam+sq_v)^2;
    end if;

    if s eq 0 or s eq 1 then
        printf "Complex #%o: degenerate (s=%o)\n", ci, s;
        continue;
    end if;

    j := 2^8*(1-s*(1-s))^3/(s^2*(1-s)^2);
    // Absolute minimal polynomial (over Q)
    abs_mp := AbsoluteMinimalPolynomial(j);
    j_inv_K[ci] := abs_mp;
    printf "Complex #%o: j abs min poly = %o\n", ci, abs_mp;
end for;

// Summary of distinct j minimal polynomials
j_classes := AssociativeArray();
for ci in Keys(j_inv_K) do
    key := Sprintf("%o", j_inv_K[ci]);
    if not IsDefined(j_classes, key) then j_classes[key] := []; end if;
    Append(~j_classes[key], ci);
end for;
printf "\nDistinct elliptic j abs min polys over Q: %o\n", #Keys(j_classes);
PQj<tj> := PolynomialRing(Rationals());
for key in Sort(Setseq(Keys(j_classes))) do
    printf "  %o : %o complexes (%o)\n", key, #j_classes[key], j_classes[key];
    // Evaluate at 1728 and factor
    mp := j_inv_K[j_classes[key][1]];
    mp_Q := ChangeRing(mp, Rationals());
    val := Evaluate(mp_Q, 1728);
    if val ne 0 then
        num := Numerator(val); den := Denominator(val);
        printf "    abs_mp(1728) = %o\n", val;
        printf "    Factorization: %o\n", Factorization(Integers()!Abs(num));
        if den ne 1 then printf "    Denominator: %o\n", Factorization(den); end if;
    else
        printf "    j = 1728 IS a root!\n";
    end if;
end for;

// =====================================================================
// STEP 11: Z/3Z orbit analysis on Steiner complexes
// =====================================================================

print "\n=== Z/3Z action on Steiner complexes ===";

F_sigma := Evaluate(F_poly, [yq, zq, xq]);
if F_sigma ne F_poly then
    print "Quartic is NOT invariant under (x:y:z) -> (y:z:x). Skipping.";
else
    print "Quartic is invariant under sigma: (x:y:z) -> (y:z:x).";

    function NormLineK2(L)
        for k in [1..3] do
            if L[k] ne 0 then return [L[j]/L[k] : j in [1..3]]; end if;
        end for;
        return L;
    end function;

    sigma_perm := [];
    for i in [1..28] do
        L := lines_K[i];
        img := NormLineK2([L[3], L[1], L[2]]);
        found_j := 0;
        for j in [1..28] do
            if NormLineK2(lines_K[j]) eq img then found_j := j; break; end if;
        end for;
        Append(~sigma_perm, found_j);
    end for;

    sigma3 := [sigma_perm[sigma_perm[sigma_perm[i]]] : i in [1..28]];
    assert sigma3 eq [i : i in [1..28]];
    print "Verified: sigma^3 = identity on 28 lines.";

    fixed_lines := [i : i in [1..28] | sigma_perm[i] eq i];
    printf "Fixed lines: %o (count: %o)\n", fixed_lines, #fixed_lines;

    function CanonicalComplex(pairs)
        return Sort([Sort(p) : p in pairs]);
    end function;

    complex_canon := [CanonicalComplex(steiner_data[ci][1]) : ci in [1..63]];

    function FindComplexIdx(can)
        for ci in [1..63] do
            if complex_canon[ci] eq can then return ci; end if;
        end for;
        return 0;
    end function;

    sigma_complex := [];
    for ci in [1..63] do
        pairs := steiner_data[ci][1];
        img_pairs := [[sigma_perm[p[1]], sigma_perm[p[2]]] : p in pairs];
        Append(~sigma_complex, FindComplexIdx(CanonicalComplex(img_pairs)));
    end for;

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
    for idx in [1..#z3_orbits] do
        o := z3_orbits[idx];
        printf "  Orbit %o (size %o): complexes %o\n", idx, #o, o;
    end for;
end if;

print "\nDone.";
