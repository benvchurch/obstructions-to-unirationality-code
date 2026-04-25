/*
 * galois_fields.m
 *
 * For each of the three quartics (Klein twist, Fermat, Edge), compute:
 *   1. Aut(C)-orbits on J[2]\{0} (via F_p automorphism group)
 *   2. Gal(K/Q)-action on J[2]\{0} (via bitangent lines over K)
 *   3. For each Aut-orbit: the smallest field over which the orbit is
 *      well-defined (= fixed field of the Galois stabilizer of the orbit)
 *
 * USAGE: magma -b galois_fields.m
 */

SetColumns(0);

// =====================================================================
// Shared helpers
// =====================================================================

function NormalizeLine(L)
    for k in [1..3] do
        if L[k] ne 0 then return [L[j]/L[k] : j in [1..3]]; end if;
    end for;
    return L;
end function;

function FindBitangentsFp(fp_proj, Fp)
    Runi<t> := PolynomialRing(Fp);
    lines := [];
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
    for A in Fp do
        restricted := Evaluate(fp_proj, [t, -A*t, Fp!1]);
        if Degree(restricted) lt 0 then continue; end if;
        fac := Factorization(restricted);
        if &and[e[2] mod 2 eq 0 : e in fac] then
            Append(~lines, [A, Fp!1, Fp!0]);
        end if;
    end for;
    restricted := Evaluate(fp_proj, [Fp!0, t, Fp!1]);
    if Degree(restricted) ge 0 then
        fac := Factorization(restricted);
        if &and[e[2] mod 2 eq 0 : e in fac] then
            Append(~lines, [Fp!1, Fp!0, Fp!0]);
        end if;
    end if;
    norm_set := {};
    lines_uniq := [];
    for L in lines do
        nL := NormalizeLine(L);
        key := Sprintf("%o", nL);
        if key notin norm_set then
            Include(~norm_set, key);
            Append(~lines_uniq, nL);
        end if;
    end for;
    return lines_uniq;
end function;

// =====================================================================
// PGL(3) helpers (from bitangent_j2_orbits.m)
// =====================================================================

function NoThreeColinear(pts, Fq)
    n := #pts;
    for i in [1..n-2] do
        for j in [i+1..n-1] do
            for k in [j+1..n] do
                Mc := Matrix(Fq, 3, 3, pts[i] cat pts[j] cat pts[k]);
                if Determinant(Mc) eq 0 then return false; end if;
            end for;
        end for;
    end for;
    return true;
end function;

function PGL3FromImages(Pin, Pout, Fq)
    M1 := Matrix(Fq, 3, 3,
        [Pin[1][1], Pin[2][1], Pin[3][1],
         Pin[1][2], Pin[2][2], Pin[3][2],
         Pin[1][3], Pin[2][3], Pin[3][3]]);
    sol := Solution(Transpose(M1), Vector(Fq, Pin[4]));
    A := M1 * DiagonalMatrix(Fq, [sol[1], sol[2], sol[3]]);
    M2 := Matrix(Fq, 3, 3,
        [Pout[1][1], Pout[2][1], Pout[3][1],
         Pout[1][2], Pout[2][2], Pout[3][2],
         Pout[1][3], Pout[2][3], Pout[3][3]]);
    sol2 := Solution(Transpose(M2), Vector(Fq, Pout[4]));
    B := M2 * DiagonalMatrix(Fq, [sol2[1], sol2[2], sol2[3]]);
    return B * A^(-1);
end function;

function AutToMatrix(g, Cpts, Fq)
    eqs := DefiningEquations(g);
    Pin := []; Pout := [];
    for v in Cpts do
        if #Pin eq 4 then break; end if;
        img := [Evaluate(e, v) : e in eqs];
        if img[1] eq 0 and img[2] eq 0 and img[3] eq 0 then continue; end if;
        new_pts := Pin cat [v];
        if NoThreeColinear(new_pts, Fq) then
            Append(~Pin, v);
            Append(~Pout, [Fq | c : c in img]);
        end if;
    end for;
    if #Pin lt 4 then error "too few points for PGL3"; end if;
    return PGL3FromImages(Pin, Pout, Fq);
end function;

function LinePermutation(M, bits)
    Minv := M^(-1);
    perm := [];
    for i in [1..#bits] do
        L := bits[i];
        img := [&+[L[c] * Minv[c, r] : c in [1..3]] : r in [1..3]];
        img_n := NormalizeLine(img);
        found := 0;
        for j in [1..#bits] do
            if NormalizeLine(bits[j]) eq img_n then found := j; break; end if;
        end for;
        if found eq 0 then error "image not found"; end if;
        Append(~perm, found);
    end for;
    return perm;
end function;

// =====================================================================
// J[2] computation: vectors, complexes, Aut-orbits
// Returns: J2_vecs (63 nonzero vectors), complexes (63 pair-lists),
//          aut_orbits (sequence of sets of indices 1..63),
//          aut_orbit_of (map from 1..63 to orbit index)
// =====================================================================
function ComputeJ2AndOrbits(F_poly, Fp, lines_Fp)
    F2 := GF(2);
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
    FF<uu> := FunctionField(f_u);
    elt_t := FF ! t_var;
    Cl, mp := ClassGroup(FF);
    invs := Invariants(Cl);

    even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
    dim := #even_idx;
    assert dim eq 6;

    function ClassJ2(D)
        cl := D @@ mp;
        coords := Eltseq(cl);
        j2 := [];
        for k in [1..#invs] do
            if invs[k] eq 0 then continue; end if;
            if invs[k] mod 2 ne 0 then continue; end if;
            Append(~j2, (2 * coords[k] div invs[k]) mod 2);
        end for;
        return j2;
    end function;

    // Line functions in function field
    ref := 1;
    line_fns := [];
    for i in [1..28] do
        A := Fp ! lines_Fp[i][1];
        B := Fp ! lines_Fp[i][2];
        CC := Fp ! lines_Fp[i][3];
        Append(~line_fns, A * elt_t + B * uu + (FF ! CC));
    end for;

    half_divs := [];
    for i in [1..28] do
        if i eq ref then
            Append(~half_divs, Zero(DivisorGroup(FF)));
            continue;
        end if;
        ratio := line_fns[i] / line_fns[ref];
        D_ratio := Divisor(ratio);
        D_half := D_ratio div 2;
        Append(~half_divs, D_half);
    end for;

    // J[2] vectors for each bitangent
    J2_vec := [];
    for i in [1..28] do
        if i eq ref then
            Append(~J2_vec, [F2 ! 0 : k in [1..dim]]);
        else
            v := ClassJ2(half_divs[i]);
            Append(~J2_vec, [F2 ! Integers() ! s : s in v]);
        end if;
    end for;

    // J[2] basis
    basis_idx := [];
    Bmat_rows := [];
    for i in [1..28] do
        if i eq ref then continue; end if;
        if #basis_idx ge dim then break; end if;
        v := J2_vec[i];
        test_seq := &cat (Bmat_rows cat [v]);
        test := Matrix(F2, #Bmat_rows + 1, dim, test_seq);
        if Rank(test) eq #Bmat_rows + 1 then
            Append(~basis_idx, i);
            Append(~Bmat_rows, v);
        end if;
    end for;
    assert #basis_idx eq dim;
    Bmat := Matrix(F2, dim, dim, &cat Bmat_rows);

    J2_coords := [];
    for i in [1..28] do
        sol := Solution(Bmat, Vector(F2, J2_vec[i]));
        Append(~J2_coords, [sol[j] : j in [1..dim]]);
    end for;

    // Steiner complexes: group pairs by J[2] class
    class_to_pairs := AssociativeArray();
    // Also track the J[2] vector for each complex
    complex_j2_keys := [];
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
    assert #Keys(class_to_pairs) eq 63;

    // Build ordered list of complexes (same order as Keys iteration)
    complexes := [];
    j2_vectors := [];  // the J[2] vector for each complex
    V := VectorSpace(F2, dim);
    for key in Keys(class_to_pairs) do
        Append(~complexes, class_to_pairs[key]);
        // Convert key (sequence) to J[2] basis coords
        sol := Solution(Bmat, Vector(F2, [F2 ! Integers() ! s : s in key]));
        Append(~j2_vectors, sol);
    end for;

    // =====================================================================
    // Aut-orbits: compute via F_p automorphism group on J[2]
    // =====================================================================
    p := Characteristic(Fp);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp_proj := Evaluate(F_poly, [xp, yp, zp]);
    Cp := Curve(P2p, fp_proj);
    auts := Automorphisms(Cp);
    printf "  |Aut(C / F_%o)| = %o\n", p, #auts;

    Cpts := [];
    for pt in Points(Cp) do
        v := Eltseq(pt);
        if &and[IsCoercible(Fp, c) : c in v] then
            Append(~Cpts, [Fp | c : c in v]);
        end if;
    end for;

    // Build F_2 matrices for each automorphism on J[2]
    gen_matrices_f2 := [];
    for gi in [1..#auts] do
        M := AutToMatrix(auts[gi], Cpts, Fp);
        perm := LinePermutation(M, lines_Fp);
        rows := [];
        for k in [1..dim] do
            bi := basis_idx[k];
            v_pi := J2_vec[perm[bi]];
            v_pref := J2_vec[perm[ref]];
            target := [v_pi[s] + v_pref[s] : s in [1..dim]];
            sol := Solution(Bmat, Vector(F2, target));
            Append(~rows, [sol[j] : j in [1..dim]]);
        end for;
        Mg := Matrix(F2, dim, dim, &cat rows);
        Append(~gen_matrices_f2, Mg);
    end for;

    G_j2 := sub<GL(dim, F2) | gen_matrices_f2>;
    printf "  J[2] matrix group: order %o, name %o\n", #G_j2, GroupName(G_j2);

    // Compute orbits of G_j2 on J[2]\{0}
    // Map nonzero vectors to complex indices
    vec_to_complex := AssociativeArray();
    for ci in [1..63] do
        vec_to_complex[j2_vectors[ci]] := ci;
    end for;

    orbit_of := [0 : i in [1..63]];
    aut_orbits := [];
    for ci in [1..63] do
        if orbit_of[ci] ne 0 then continue; end if;
        oi := #aut_orbits + 1;
        orb_vecs := {j2_vectors[ci]};
        for M in G_j2 do
            Include(~orb_vecs, j2_vectors[ci] * M);
        end for;
        orb_indices := {};
        for v in orb_vecs do
            if IsDefined(vec_to_complex, v) then
                Include(~orb_indices, vec_to_complex[v]);
            end if;
        end for;
        Append(~aut_orbits, Sort(SetToSequence(orb_indices)));
        for ci2 in orb_indices do
            orbit_of[ci2] := oi;
        end for;
    end for;

    printf "  Aut-orbits on J[2]\\{0}: %o orbits, sizes %o\n",
        #aut_orbits, Sort([#o : o in aut_orbits]);

    return j2_vectors, complexes, aut_orbits, orbit_of, J2_vec, J2_coords, basis_idx, ref, Bmat;
end function;

// =====================================================================
// Compute bitangent lines over K (the splitting field)
// =====================================================================
function ComputeLinesOverK(F_poly, Fp, lines_Fp)
    QQ := Rationals();
    RR5<a_var, b_var, al, be, ga> := PolynomialRing(QQ, 5);
    Rt5<ttt> := PolynomialRing(RR5);
    f_restr := Evaluate(F_poly, [ttt, RR5!1, -a_var*ttt - b_var]);
    sq := (al*ttt^2 + be*ttt + ga)^2;
    eqns := [Coefficient(f_restr, d) - Coefficient(sq, d) : d in [0..4]];
    I_bt := ideal<RR5 | eqns>;
    I_ab := EliminationIdeal(I_bt, {a_var, b_var});
    gens_ab := Basis(I_ab);

    RR2<aa, bb> := PolynomialRing(QQ, 2);
    gens2 := [Evaluate(g, [aa, bb, 0, 0, 0]) : g in gens_ab];
    I2 := ideal<RR2 | gens2>;
    I_b_only := EliminationIdeal(I2, {bb});
    fb := UnivariatePolynomial(Basis(I_b_only)[1]);
    fac_b := Factorization(fb);

    RR4<c_var, al2, be2, ga2> := PolynomialRing(QQ, 4);
    Rts<ss, tt2> := PolynomialRing(RR4, 2);
    f_restr2 := Evaluate(F_poly, [tt2, -c_var*tt2, ss]);
    sq2 := (al2*tt2^2 + be2*tt2*ss + ga2*ss^2)^2;
    mons_ts := [tt2^4, tt2^3*ss, tt2^2*ss^2, tt2*ss^3, ss^4];
    eqns2 := [MonomialCoefficient(f_restr2, m) - MonomialCoefficient(sq2, m) : m in mons_ts];
    I_bt2 := ideal<RR4 | eqns2>;
    I_c := EliminationIdeal(I_bt2, {c_var});
    gens_c := Basis(I_c);
    if #gens_c gt 0 then
        fc := UnivariatePolynomial(gens_c[1]);
        fac_c := Factorization(fc);
    else
        Runi := Parent(fb);
        fc := Runi!1;
        fac_c := [];
    end if;

    all_irred := [f[1] : f in fac_b | Degree(f[1]) gt 1];
    if Degree(fc) gt 0 then
        all_irred cat:= [f[1] : f in fac_c | Degree(f[1]) gt 1];
    end if;

    if #all_irred eq 0 then
        K := QQ;
    else
        prod_fac := &*all_irred;
        K<w> := SplittingField(prod_fac);
    end if;

    Ra_K<aK> := PolynomialRing(K);
    lines_K := [];

    fb_K := ChangeRing(fb, K);
    b_roots := [r[1] : r in Roots(fb_K)];

    for b0 in b_roots do
        a_polys := [];
        for g in gens_ab do
            gab := Evaluate(g, [aa, bb, 0, 0, 0]);
            ga_uni := Evaluate(gab, [aK, Ra_K!b0]);
            if Degree(ga_uni) ge 1 then Append(~a_polys, ga_uni); end if;
        end for;
        if #a_polys eq 0 then continue; end if;
        g_a := GCD(a_polys);
        if Degree(g_a) ge 1 then
            a_roots := [r[1] : r in Roots(g_a)];
            for a0 in a_roots do
                f_check := Evaluate(F_poly, [aK, K!1, -a0*aK - K!b0]);
                if Degree(f_check) lt 0 then continue; end if;
                is_bt := true;
                if Degree(f_check) ge 1 then
                    fac_check := Factorization(f_check);
                    is_bt := &and[e[2] mod 2 eq 0 : e in fac_check];
                end if;
                if is_bt then Append(~lines_K, [a0, b0, K!1]); end if;
            end for;
        end if;
    end for;

    if Degree(fc) gt 0 then
        fc_K := ChangeRing(fc, K);
        c_roots := [r[1] : r in Roots(fc_K)];
        for c0 in c_roots do
            f_check := Evaluate(F_poly, [aK, -c0*aK, K!1]);
            is_bt := true;
            if Degree(f_check) ge 1 then
                fac_check := Factorization(f_check);
                is_bt := &and[e[2] mod 2 eq 0 : e in fac_check];
            end if;
            if not is_bt and Degree(f_check) le 0 then is_bt := true; end if;
            if is_bt then Append(~lines_K, [c0, K!1, K!0]); end if;
        end for;
    end if;

    f_x0 := Evaluate(F_poly, [Ra_K!0, aK, K!1]);
    if Degree(f_x0) ge 1 then
        fac_x0 := Factorization(f_x0);
        if &and[e[2] mod 2 eq 0 : e in fac_x0] then
            Append(~lines_K, [K!1, K!0, K!0]);
        end if;
    elif Evaluate(F_poly, [Rationals()!0, Rationals()!1, Rationals()!0]) eq 0 then
        Append(~lines_K, [K!1, K!0, K!0]);
    end if;

    norm_set := {};
    lines_K_unique := [];
    for L in lines_K do
        nL := NormalizeLine(L);
        key := Sprintf("%o", nL);
        if key notin norm_set then
            Include(~norm_set, key);
            Append(~lines_K_unique, L);
        end if;
    end for;
    lines_K := lines_K_unique;
    assert #lines_K eq 28;

    // Match K-lines to F_p lines
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

    fp_lookup := AssociativeArray();
    for i in [1..28] do
        nL := NormalizeLine(lines_Fp[i]);
        key := Sprintf("%o", nL);
        fp_lookup[key] := i;
    end for;

    lines_K_ordered := [lines_K[1] : i in [1..28]];
    best_matched := 0;

    if Type(K) eq FldRat then
        for ki in [1..28] do
            LK := lines_K[ki];
            LK_Fp := [Fp!LK[j] : j in [1..3]];
            nL := NormalizeLine(LK_Fp);
            key := Sprintf("%o", nL);
            if IsDefined(fp_lookup, key) then
                lines_K_ordered[fp_lookup[key]] := LK;
                best_matched +:= 1;
            end if;
        end for;
    else
        w_minpoly := MinimalPolynomial(K.1);
        w_roots_Fp := [r[1] : r in Roots(ChangeRing(w_minpoly, Fp))];
        for wi in [1..#w_roots_Fp] do
            wr := w_roots_Fp[wi];
            test_ordered := [lines_K[1] : i in [1..28]];
            test_matched := 0;
            for ki in [1..28] do
                LK := lines_K[ki];
                LK_Fp := [ReduceViaRoot(LK[j], Fp, wr) : j in [1..3]];
                nL := NormalizeLine(LK_Fp);
                key := Sprintf("%o", nL);
                if IsDefined(fp_lookup, key) then
                    test_ordered[fp_lookup[key]] := LK;
                    test_matched +:= 1;
                end if;
            end for;
            if test_matched gt best_matched then
                best_matched := test_matched;
                lines_K_ordered := test_ordered;
            end if;
        end for;
    end if;

    assert best_matched eq 28;
    return K, lines_K_ordered;
end function;

// =====================================================================
// Galois permutation on {1..28} lines
// =====================================================================
function GaloisPermOnLines(K, lines_K, sigma)
    lookup := AssociativeArray();
    for i in [1..28] do
        nL := NormalizeLine(lines_K[i]);
        key := Sprintf("%o", nL);
        lookup[key] := i;
    end for;
    perm := [];
    for i in [1..28] do
        L := lines_K[i];
        L_sigma := [sigma(L[j]) : j in [1..3]];
        nL := NormalizeLine(L_sigma);
        key := Sprintf("%o", nL);
        assert IsDefined(lookup, key);
        Append(~perm, lookup[key]);
    end for;
    return perm;
end function;

// =====================================================================
// Lift line permutation to J[2] permutation on 63 complexes
// via the F_2 linear action on J[2] vectors
// =====================================================================
function GaloisPermOnJ2(perm28, J2_vec, basis_idx, ref, Bmat, j2_vectors)
    F2 := GF(2);
    dim := 6;
    // Build the F_2 matrix for this line permutation
    rows := [];
    for k in [1..dim] do
        bi := basis_idx[k];
        v_pi := J2_vec[perm28[bi]];
        v_pref := J2_vec[perm28[ref]];
        target := [v_pi[s] + v_pref[s] : s in [1..dim]];
        sol := Solution(Bmat, Vector(F2, target));
        Append(~rows, [sol[j] : j in [1..dim]]);
    end for;
    Mg := Matrix(F2, dim, dim, &cat rows);

    // Now apply Mg to each of the 63 J[2] vectors
    vec_to_idx := AssociativeArray();
    for ci in [1..63] do
        vec_to_idx[j2_vectors[ci]] := ci;
    end for;

    perm63 := [];
    for ci in [1..63] do
        img := j2_vectors[ci] * Mg;
        assert IsDefined(vec_to_idx, img);
        Append(~perm63, vec_to_idx[img]);
    end for;
    return perm63;
end function;

// =====================================================================
// Identify fixed subfield name from a Galois automorphism
// =====================================================================
function SquarefreeDisc(mp)
    QQ := Rationals();
    disc := QQ ! (Coefficient(mp,1)^2 - 4*Coefficient(mp,0));
    n := Integers() ! Numerator(disc);
    d := Integers() ! Denominator(disc);
    nd := n * d;
    if nd eq 0 then return 0; end if;
    sgn := nd gt 0 select 1 else -1;
    fac := Factorization(Abs(nd));
    sf := sgn;
    for f in fac do
        if f[2] mod 2 eq 1 then sf *:= f[1]; end if;
    end for;
    return sf;
end function;

function SubfieldName(K, sigma)
    w := K.1;
    sw := sigma(w);
    candidates := [w + sw, w * sw, w - sw, w^2 + sw^2];
    for elt in candidates do
        mp := MinimalPolynomial(elt);
        if Degree(mp) eq 2 then
            sf := SquarefreeDisc(mp);
            return Sprintf("Q(sqrt(%o))", sf);
        end if;
    end for;
    return "Q";
end function;

// =====================================================================
// Main computation
// =====================================================================

QQ := Rationals();
RQ<xq,yq,zq> := PolynomialRing(QQ, 3);

quartics := [
    <"Klein twist",
     xq^4 + yq^4 + zq^4 + 6*(xq*yq^3 + yq*zq^3 + zq*xq^3)
     - 3*(xq^2*yq^2 + yq^2*zq^2 + zq^2*xq^2) + 3*xq*yq*zq*(xq+yq+zq),
     29>,
    <"Fermat",
     xq^4 + yq^4 + zq^4,
     41>,
    <"Edge",
     25*(xq^4 + yq^4 + zq^4) - 34*(xq^2*yq^2 + yq^2*zq^2 + xq^2*zq^2),
     29>
];

for qi in [1..#quartics] do
    label := quartics[qi][1];
    F_poly := quartics[qi][2];
    p := quartics[qi][3];
    Fp := GF(p);

    print "============================================================";
    printf "%o (p = %o)\n", label, p;
    print "============================================================";

    // Bitangents over F_p
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp_proj := Evaluate(F_poly, [xp, yp, zp]);
    lines_Fp := FindBitangentsFp(fp_proj, Fp);
    assert #lines_Fp eq 28;

    // J[2], Steiner complexes, Aut-orbits
    printf "Computing J[2] and Aut-orbits over F_%o...\n", p;
    j2_vectors, complexes, aut_orbits, orbit_of,
        J2_vec, J2_coords, basis_idx, ref, Bmat :=
        ComputeJ2AndOrbits(F_poly, Fp, lines_Fp);

    // Lines over K
    printf "Computing bitangent lines over K...\n";
    K, lines_K := ComputeLinesOverK(F_poly, Fp, lines_Fp);
    deg_K := Degree(K, QQ);
    printf "  [K:Q] = %o\n", deg_K;

    if Type(K) eq FldRat then
        printf "\nK = Q: all orbits defined over Q.\n";
        printf "\n| Orbit | Size | Field |\n|-------|------|-------|\n";
        for oi in [1..#aut_orbits] do
            printf "| %o | %o | Q |\n", oi, #aut_orbits[oi];
        end for;
        print "";
        continue;
    end if;

    // Galois group
    auts_K := Automorphisms(K);
    gal_nontrivial := [sigma : sigma in auts_K | sigma(K.1) ne K.1];
    printf "Gal(K/Q): %o non-trivial elements\n", #gal_nontrivial;
    for i in [1..#gal_nontrivial] do
        printf "  sigma_%o: w -> %o  (fixes %o)\n",
            i, gal_nontrivial[i](K.1), SubfieldName(K, gal_nontrivial[i]);
    end for;

    // Galois permutations on J[2]
    gal_perm63 := [];
    for si in [1..#gal_nontrivial] do
        sigma := gal_nontrivial[si];
        p28 := GaloisPermOnLines(K, lines_K, sigma);
        p63 := GaloisPermOnJ2(p28, J2_vec, basis_idx, ref, Bmat, j2_vectors);
        Append(~gal_perm63, p63);
        fixed := #[i : i in [1..63] | p63[i] eq i];
        printf "  sigma_%o: %o fixed complexes\n", si, fixed;
    end for;

    // For each Aut-orbit, determine which Galois elements stabilize it as a set
    printf "\n=== Field of definition for each Aut(C)-orbit ===\n";
    printf "\n| Orbit | Size | Field |\n|-------|------|-------|\n";

    for oi in [1..#aut_orbits] do
        orb_set := Set(aut_orbits[oi]);
        // Check which sigma stabilize this orbit as a set
        stab_indices := {};
        for si in [1..#gal_nontrivial] do
            sigma_orb := {gal_perm63[si][ci] : ci in orb_set};
            if sigma_orb eq orb_set then
                Include(~stab_indices, si);
            end if;
        end for;

        if #stab_indices eq #gal_nontrivial then
            field := "Q";
        elif #stab_indices eq 0 then
            if deg_K eq 2 then
                dp := DefiningPolynomial(K);
                sf := SquarefreeDisc(dp);
                field := Sprintf("Q(sqrt(%o))", sf);
            else
                field := "K = Q(zeta_8)";
            end if;
        else
            // One or more sigma stabilize, identify the fixed field
            // The stabilizer subgroup determines the field
            // For deg 4 with (Z/2)^2 Galois: stabilizer of order 2 gives quadratic subfield
            si := Representative(stab_indices);
            field := SubfieldName(K, gal_nontrivial[si]);
        end if;

        printf "| %o | %o | %o |\n", oi, #aut_orbits[oi], field;
    end for;

    // Also show individual complex data for verification
    printf "\nIndividual complex fields of definition:\n";
    for ci in [1..63] do
        stab := {};
        for si in [1..#gal_nontrivial] do
            if gal_perm63[si][ci] eq ci then Include(~stab, si); end if;
        end for;
        if #stab eq #gal_nontrivial then
            field := "Q";
        elif #stab eq 0 then
            field := "K";
        else
            si := Representative(stab);
            field := SubfieldName(K, gal_nontrivial[si]);
        end if;
        printf "  #%o (orbit %o): %o\n", ci, orbit_of[ci], field;
    end for;

    print "";
end for;

quit;
