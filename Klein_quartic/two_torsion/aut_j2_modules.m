/*******************************************************************************
 * aut_j2_modules.m
 *
 * For each of the three curves (Klein twist, Fermat, Edge), compute:
 *   - the geometric automorphism group Aut(C / F_q^bar) (we work over a finite
 *     field F_q chosen so that this group is fully visible),
 *   - its action on the 28 bitangent lines,
 *   - the induced F_2[Aut(C)]-module structure on H^1(C, F_2) = J(C)[2],
 *   - the decomposition into composition factors and indecomposable summands,
 *   - whether H^1(C, F_2) is semisimple as an F_2[Aut(C)]-module.
 *
 * The J[2] basis is built from bitangent differences:
 *     a basis vector v_i = [L_{i+1}] - [L_1]   (i = 1..6)
 * where L_i are 28 bitangent classes in (1/2)·K_C ⊂ Pic(C).  The differences
 * lie in J[2] = ker(2: J -> J).
 *
 * The action of an automorphism g on this basis is computed via the
 * permutation pi_g of the 28 bitangents:
 *     g.(L_i - L_1) = L_{pi_g(i)} - L_{pi_g(1)}.
 ******************************************************************************/

SetOutputFile("results/aut_j2_modules.log" : Overwrite := true);
SetColumns(0);
F2 := GF(2);

// ---------------------------------------------------------------------
// Helper: enumerate the 28 bitangents of a smooth plane quartic C / F_q.
//
// A line ax + by + cz = 0 is bitangent to C iff the restriction of F to the
// line factors as a square of a quadratic.  We parameterize lines by an
// affine chart and search.
// ---------------------------------------------------------------------
function FindBitangents(F, Fq)
    P2 := Parent(F);
    x := P2.1; y := P2.2; z := P2.3;
    bits := [];

    Pt<t> := PolynomialRing(Fq);

    // Chart 1: lines z = a*x + b*y  (i.e. parameterize as (s, t, a*s+b*t))
    for a in Fq do
        for b in Fq do
            f_line := Evaluate(F, [t, 1, a*t + b]);
            // f_line is a polynomial in t of degree 4
            if Degree(f_line) lt 0 then continue; end if;
            // Check if f_line / leading_coeff is a square
            if f_line eq 0 then continue; end if;
            lc := LeadingCoefficient(f_line);
            f_norm := f_line / lc;
            is_sq, _ := IsSquare(f_norm);
            if is_sq then
                // Line: -a*x - b*y + z = 0  i.e. coeffs [-a, -b, 1]
                Append(~bits, [Fq | -a, -b, 1]);
            end if;
        end for;
    end for;

    // Chart 2: lines y = c*x  (with z = 0 implicitly)
    // Parameterize as (s, c*s, t) and check if F(s, cs, t) (degree 4 in s,t) factors
    // as a square in t for fixed s = 1
    for c in Fq do
        f_line := Evaluate(F, [1, c, t]);
        if Degree(f_line) lt 0 then continue; end if;
        if f_line eq 0 then continue; end if;
        lc := LeadingCoefficient(f_line);
        f_norm := f_line / lc;
        is_sq, _ := IsSquare(f_norm);
        if is_sq then
            // Line: c*x - y = 0, coeffs [c, -1, 0]
            Append(~bits, [Fq | c, -1, 0]);
        end if;
    end for;

    // Chart 3: line x = 0
    f_line := Evaluate(F, [0, 1, t]);
    if Degree(f_line) ge 0 and f_line ne 0 then
        lc := LeadingCoefficient(f_line);
        f_norm := f_line / lc;
        is_sq, _ := IsSquare(f_norm);
        if is_sq then
            Append(~bits, [Fq | 1, 0, 0]);
        end if;
    end if;

    // Normalize: scale each line so that the first non-zero entry is 1.
    bits_norm := [];
    for L in bits do
        for k in [1..3] do
            if L[k] ne 0 then
                Append(~bits_norm, [L[i]/L[k] : i in [1..3]]);
                break;
            end if;
        end for;
    end for;

    // Deduplicate
    bits_uniq := [];
    for L in bits_norm do
        if not (L in bits_uniq) then
            Append(~bits_uniq, L);
        end if;
    end for;
    return bits_uniq;
end function;

// ---------------------------------------------------------------------
// Helper: compute the action of a 3x3 matrix M (acting on column vectors)
// on the bitangents. Lines transform contravariantly: line L (row vector)
// goes to L * M^{-1}.
// ---------------------------------------------------------------------
function NormalizeLine(L)
    for k in [1..3] do
        if L[k] ne 0 then
            return [L[i]/L[k] : i in [1..3]];
        end if;
    end for;
    return L;
end function;

function LinePermutation(M, bits)
    // M is a 3x3 invertible matrix in PGL(3, K)
    // We want pi: {1..28} -> {1..28} such that L_i.M^{-1} = L_{pi(i)}
    Minv := M^(-1);
    perm := [];
    for i in [1..#bits] do
        L := bits[i];
        // new line = L * Minv  (row vector times matrix)
        img := [&+[L[c] * Minv[c, r] : c in [1..3]] : r in [1..3]];
        img_n := NormalizeLine(img);
        found := 0;
        for j in [1..#bits] do
            if NormalizeLine(bits[j]) eq img_n then
                found := j;
                break;
            end if;
        end for;
        if found eq 0 then
            error "LinePermutation: image not found";
        end if;
        Append(~perm, found);
    end for;
    return perm;
end function;

// ---------------------------------------------------------------------
// Helpers for recovering the 3x3 PGL(3) matrix from a curve automorphism.
// Magma represents an automorphism g of a smooth plane quartic C as a
// polynomial map whose DefiningEquations are degree-4 polynomials (the
// linear PGL(3) action expressed using a different polynomial representation
// modulo the curve equation). To recover the underlying linear matrix we
// sample g at 4 F_q-points of C in general position and solve for the
// PGL(3) element via the standard projective frame construction.
// ---------------------------------------------------------------------

function PGL3FromImages(Pin, Pout, Fq)
    // Pin = [P1, P2, P3, P4], Pout = [Q1, Q2, Q3, Q4] are 4-tuples of length-3
    // sequences (homogeneous coordinates) with no 3 colinear. Returns the
    // unique 3x3 matrix M (up to scalar) in the COLUMN-vector convention
    // P -> M * P  sending the projective points [Pi] to [Qi].
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

function NoThreeColinear(pts, Fq)
    // True iff no 3 of the points in pts are colinear in P^2.
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

function AutToMatrix(g, Cpts, Fq)
    // Recover the underlying PGL(3) matrix of a curve automorphism g
    // by evaluating its defining equations at 4 points of C in general
    // position. Cpts is a precomputed list of F_q-rational points of C.
    eqs := DefiningEquations(g);
    Pin := [];
    Pout := [];
    for v in Cpts do
        if #Pin eq 4 then break; end if;
        img := [Evaluate(e, v) : e in eqs];
        // Skip base points (g undefined here as a P^2 map)
        if img[1] eq 0 and img[2] eq 0 and img[3] eq 0 then continue; end if;
        // Check that adding v keeps the chosen points in general position.
        new_pts := Pin cat [v];
        if NoThreeColinear(new_pts, Fq) then
            Append(~Pin, v);
            Append(~Pout, [Fq | c : c in img]);
        end if;
    end for;
    if #Pin lt 4 then
        error "AutToMatrix: could not find 4 points in general position";
    end if;
    return PGL3FromImages(Pin, Pout, Fq);
end function;

// ---------------------------------------------------------------------
// Main analysis
// ---------------------------------------------------------------------
procedure AnalyzeCurve(label, F_str, p)
    printf "\n========================================\n";
    printf "Curve: %o (over F_%o)\n", label, p;
    printf "========================================\n";

    Fq := GF(p);
    P2<x,y,z> := ProjectiveSpace(Fq, 2);
    R := CoordinateRing(P2);
    F := eval F_str;

    C := Curve(P2, F);
    if not IsNonsingular(C) then
        printf "  C is singular over F_%o, skipping.\n", p;
        return;
    end if;

    printf "Computing Automorphisms(C)...\n";
    t0 := Cputime();
    auts := Automorphisms(C);
    printf "  done (%.1os).  |Aut(C / F_%o)| = %o\n", Cputime(t0), p, #auts;

    // Find bitangents
    printf "Finding 28 bitangents...\n";
    t0 := Cputime();
    bits := FindBitangents(F, Fq);
    printf "  found %o bitangents (%.1os).\n", #bits, Cputime(t0);
    if #bits ne 28 then
        printf "  Warning: expected 28 bitangents.\n";
        return;
    end if;

    // Precompute F_q-rational points on C, for use in matrix recovery.
    printf "Computing F_%o-rational points on C...\n", p;
    t0 := Cputime();
    Cpts_set := Points(C);
    Cpts := [];
    for pt in Cpts_set do
        v := Eltseq(pt);
        if &and[IsCoercible(Fq, c) : c in v] then
            Append(~Cpts, [Fq | c : c in v]);
        end if;
    end for;
    printf "  %o F_%o-rational points (%.1os).\n", #Cpts, p, Cputime(t0);
    if #Cpts lt 6 then
        printf "  ERROR: too few points to recover automorphism matrices.\n";
        return;
    end if;

    // For each automorphism, recover its 3x3 PGL(3) matrix and induced
    // permutation of the bitangents.
    perms := [];
    for g in auts do
        M := AutToMatrix(g, Cpts, Fq);
        perm := LinePermutation(M, bits);
        Append(~perms, perm);
    end for;
    printf "Built bitangent action for all %o group elements.\n", #perms;

    // Build the algebraic function field FF = F_p(t)[u]/(f(t,u,1)) so that
    // ClassGroup(FF) works (Magma's ClassGroup does NOT work directly on the
    // FunctionField of a plane curve scheme).  This is the same construction
    // used by steiner_pipeline.m.
    printf "Building algebraic function field & class group...\n";
    t0 := Cputime();
    Rxyz<X,Y,Z> := PolynomialRing(Fq, 3);
    F_XYZ := Evaluate(F, [X, Y, Z]);
    Fpt<t_var> := FunctionField(Fq);
    Ku<u_var> := PolynomialRing(Fpt);
    f_u := Ku ! 0;
    for j in [0..4] do
        coeff_j := Fpt ! 0;
        for i in [0..4-j] do
            k := 4 - i - j;
            c := MonomialCoefficient(F_XYZ, X^i * Y^j * Z^k);
            if c ne 0 then coeff_j +:= (Fpt ! c) * t_var^i; end if;
        end for;
        f_u +:= coeff_j * u_var^j;
    end for;
    assert Degree(f_u) ge 3;
    FF<uu> := FunctionField(f_u);
    elt_t := FF ! t_var;
    Cl, mp := ClassGroup(FF);
    invs := Invariants(Cl);
    printf "  done (%.1os). Cl invariants = %o\n", Cputime(t0), invs;

    // J[2] extraction: read off the mod-2 coordinates on the even cyclic factors
    even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
    dim := #even_idx;
    printf "  J[2] dimension = %o (expected 6)\n", dim;
    if dim ne 6 then
        printf "  WARNING: J[2] dimension is %o, not 6 — aborting.\n", dim;
        return;
    end if;

    function ClassJ2(D)
        cl := D @@ mp;
        coords := Eltseq(cl);
        j2 := [];
        for k in [1..#invs] do
            if invs[k] eq 0 then continue; end if;
            if invs[k] mod 2 ne 0 then continue; end if;
            // 2-torsion of Z/n (n even) is {0, n/2}; map a -> (2a div n) mod 2
            Append(~j2, (2 * coords[k] div invs[k]) mod 2);
        end for;
        return j2;
    end function;

    // Build line functions L_i / (line_at_infinity z=1) = A*t + B*u + C
    // and the half-divisors (1/2)*div(L_i / L_ref) ∈ J[2].
    printf "Computing half-divisors for the 28 bitangents...\n";
    t0 := Cputime();
    line_fns := [];
    for i in [1..28] do
        A := Fq ! bits[i][1];
        B := Fq ! bits[i][2];
        CC := Fq ! bits[i][3];
        Append(~line_fns, A * elt_t + B * uu + (FF ! CC));
    end for;
    ref := 1;
    half_divs := [* *];
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
    printf "  done (%.1os).\n", Cputime(t0);

    // Compute J[2] vectors (length-6 over F_2) for all 28 bitangents
    J2_vec := [];
    for i in [1..28] do
        if i eq ref then
            Append(~J2_vec, [F2 ! 0 : k in [1..dim]]);
        else
            v := ClassJ2(half_divs[i]);
            Append(~J2_vec, [F2 ! Integers() ! s : s in v]);
        end if;
    end for;

    // Pick a basis: 6 linearly independent J2_vec[i] (i ≠ ref)
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
    if #basis_idx ne dim then
        printf "  ERROR: only found %o linearly independent J2 vectors (need %o).\n",
            #basis_idx, dim;
        return;
    end if;
    Bmat := Matrix(F2, dim, dim, &cat Bmat_rows);
    printf "Basis bitangent indices (ref = #%o): %o\n", ref, basis_idx;

    // For each automorphism, build the F_2 matrix on this basis.
    // g acts on J[2] by:  g.J2[i] = J2[perm[i]] - J2[perm[ref]]
    //                            = J2[perm[i]] + J2[perm[ref]]    (in char 2)
    gen_matrices_f2 := [];
    for gi in [1..#perms] do
        perm := perms[gi];
        rows := [];
        for k in [1..dim] do
            i := basis_idx[k];
            v_pi := J2_vec[perm[i]];
            v_pref := J2_vec[perm[ref]];
            target := [v_pi[s] + v_pref[s] : s in [1..dim]];
            sol := Solution(Bmat, Vector(F2, target));
            Append(~rows, [sol[j] : j in [1..dim]]);
        end for;
        Mg := Matrix(F2, dim, dim, &cat rows);
        Append(~gen_matrices_f2, Mg);
    end for;

    // Build the matrix group and the GModule
    G_mat := sub<GL(dim, F2) | gen_matrices_f2>;
    printf "F_2-image of Aut(C) has order %o (group: %o)\n",
        #G_mat, GroupName(G_mat);

    M := GModule(G_mat);
    printf "\nGModule M of dimension %o over F_2:\n", Dimension(M);
    printf "  IsIrreducible(M) = %o\n", IsIrreducible(M);
    printf "  IsSemisimple(M)  = %o\n", IsSemisimple(M);

    cf := CompositionFactors(M);
    printf "Composition factors of M: %o factors\n", #cf;
    for i in [1..#cf] do
        printf "  factor %o: dim %o, abs irreducible? %o\n",
            i, Dimension(cf[i]), IsAbsolutelyIrreducible(cf[i]);
    end for;

    indecs := IndecomposableSummands(M);
    printf "Indecomposable summands of M: %o summands\n", #indecs;
    for i in [1..#indecs] do
        printf "  summand %o: dim %o, irreducible? %o\n",
            i, Dimension(indecs[i]), IsIrreducible(indecs[i]);
        if not IsIrreducible(indecs[i]) then
            sub_cf := CompositionFactors(indecs[i]);
            printf "    composition factors:";
            for c in sub_cf do printf " dim %o", Dimension(c); end for;
            printf "\n";
        end if;
    end for;
end procedure;

// ---------------------------------------------------------------------
// Run the analysis on the three curves.
// We choose primes so that the geometric Aut group is fully F_p-rational
// and the 28 bitangents are F_p-rational.
// ---------------------------------------------------------------------
AnalyzeCurve(
    "klein_twist",
    "x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3) - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z)",
    29
);
AnalyzeCurve(
    "fermat",
    "x^4 + y^4 + z^4",
    41
);
AnalyzeCurve(
    "edge",
    "25*(x^4 + y^4 + z^4) - 34*(x^2*y^2 + x^2*z^2 + y^2*z^2)",
    19
);

UnsetOutputFile();
quit;
