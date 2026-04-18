/*******************************************************************************
 * steiner_computations.m
 *
 * Given a smooth plane quartic F over Q, compute:
 *   1. The 28 bitangent lines (over the splitting field)
 *   2. The 63 Steiner complexes
 *   3. Witnessing conics for each pair-of-pairs
 *   4. Quartic decompositions a*F = L_i*L_j*L_k*L_l + b*Q^2
 *   5. Genus-2 curves via det(Q1 + 2t*Q2 + t^2*Q3) -- Pryms of D_eta -> C
 *   6. Igusa invariants and elliptic j-invariants (via Z/3 cross-ratio)
 *
 * USAGE: load this file, then call
 *           RunSteinerPipeline(label, F_input);
 *        where label is a string and F_input is a homogeneous degree-4
 *        polynomial in three variables over Q.
 *
 * Companion math reference: pipeline_math.md (same directory).
 *   STEP 0  - §3 (bitangents = odd theta characteristics)
 *   STEP 1  - §4 (Steiner complexes from J[2], incl. ClassJ2 warning §4.1)
 *   STEP 2  - §5 (contact conic for pair-of-pairs, 12x10 system)
 *   STEP 4  - §5 (quartic decomposition aF = L_i L_j L_k L_l + bQ^2)
 *   STEP 5  - §6 (3x3 symmetric pencil M(t), y^2 = -det M(t))
 *   STEP 7  - §3 (bitangents over K via tangency ideal elimination)
 *   STEP 8  - §§5-7 (same math, redone over K)
 *   STEP 10 - §8 (elliptic factor via Z/3 action on Weierstrass points)
 *   STEP 11 - §2.5 / klein_steiner_pryms.md (Z/3 orbits on complexes)
 *
 * The script is self-contained. No external dependencies.
 ******************************************************************************/

// =====================================================================
// Field-polymorphic helpers (no closure over procedure state)
// =====================================================================

// NormalizeLine(L): canonicalise a projective line [A,B,C] by scaling so the
// first nonzero coordinate is 1. Used to deduplicate and compare lines.
function NormalizeLine(L)
    for k in [1..3] do
        if L[k] ne 0 then return [L[j]/L[k] : j in [1..3]]; end if;
    end for;
    return L;
end function;

// FindBitangentsFp(fp_proj, Fp): enumerate all F_p-rational bitangent lines
// to the quartic fp_proj in P^2 by iterating over the 3 charts. A line L is
// a bitangent iff F|_L is a perfect square (up to scalar). See pipeline_math.md §3.
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

// ContactQuadratic(F, F_poly_F, line, R_uni): given a bitangent line L to a
// quartic F_poly_F over field F, return <param_type_tuple, [al, be, ga]>
// where (al*t^2 + be*t + ga)^2 = F|_L up to scalar. See pipeline_math.md §5.
function ContactQuadratic(F, F_poly_F, line, R_uni)
    tt := R_uni.1;
    A := line[1]; B := line[2]; CC := line[3];
    if CC ne 0 then
        // Chart z != 0: parametrise L as (t, 1, -(A*t+B)/CC)
        restricted := Evaluate(F_poly_F, [tt, F!1, (-A*tt - B)/CC]);
        restricted *:= CC^4;
        pt := <3, A, B, CC>;
    elif B ne 0 then
        // Chart y != 0, z = 0: parametrise as (t, -A*t/B, 1)
        restricted := Evaluate(F_poly_F, [tt, -A*tt/B, F!1]);
        restricted *:= B^4;
        pt := <2, A, B, CC>;
    else
        // Chart x != 0, y = z = 0: the line x = 0 parametrised as (0, t, 1)
        restricted := Evaluate(F_poly_F, [R_uni!0, tt, F!1]);
        pt := <1, A, B, CC>;
    end if;
    fac := Factorization(restricted);
    assert &and[e[2] mod 2 eq 0 : e in fac];  // bitangent => even mults
    if #fac eq 0 then
        // Constant restriction: contact points at infinity in this chart.
        cval := F ! restricted;
        is_sq, sqv := IsSquare(cval);
        assert is_sq;
        sq_root := R_uni ! sqv;
    else
        sq_root_monic := &*[e[1]^(e[2] div 2) : e in fac];
        ratio_val := LeadingCoefficient(restricted) / LeadingCoefficient(sq_root_monic)^2;
        is_sq, sqv := IsSquare(ratio_val);
        assert is_sq;
        sq_root := sqv * sq_root_monic;
    end if;
    al := Degree(sq_root) ge 2 select Coefficient(sq_root, 2) else F!0;
    be := Degree(sq_root) ge 1 select Coefficient(sq_root, 1) else F!0;
    ga := Coefficient(sq_root, 0);
    return pt, [F | al, be, ga];
end function;

// RestrictionMatrix(F, param): 3x6 matrix expressing "restrict a degree-2
// form on P^2 to a parametrised line" for the chart recorded in `param`.
// See pipeline_math.md §5.
function RestrictionMatrix(F, param)
    M := ZeroMatrix(F, 3, 6);
    AA := param[2]; BB := param[3]; CC := param[4];
    if param[1] eq 3 then
        a := -AA/CC; b := -BB/CC;
        M[1,1] := 1; M[1,3] := a; M[1,6] := a^2;
        M[2,2] := 1; M[2,3] := b; M[2,5] := a; M[2,6] := 2*a*b;
        M[3,4] := 1; M[3,5] := b; M[3,6] := b^2;
    elif param[1] eq 2 then
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

// FindConic(F, params, cquads, idx4): solve for the witnessing conic Q
// supported by the 4 bitangents indexed by idx4 = [i,j,k,l].
// Returns <coeffs_of_Q_in_degree2_monomials, ok_flag>.
// Kernel of the 12x10 linear system; see pipeline_math.md §5.
function FindConic(F, params, cquads, idx4)
    M := ZeroMatrix(F, 12, 10);
    for idx in [1..4] do
        m := idx4[idx];
        Rm := RestrictionMatrix(F, params[m]);
        hm := cquads[m];
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
        return [F | 0,0,0,0,0,0], false;
    end if;
    v := N.1;
    return [v[c] : c in [1..6]], true;
end function;

// CoeffVec(poly, mons): coefficient vector of `poly` in the monomial basis `mons`.
function CoeffVec(poly, mons)
    return [MonomialCoefficient(poly, m) : m in mons];
end function;

// LProdCoeffs(L1, L2): 6 coefficients of the symmetric product L1*L2 in the
// basis (x^2, xy, xz, y^2, yz, z^2).
function LProdCoeffs(L1, L2)
    return [L1[1]*L2[1], L1[1]*L2[2]+L1[2]*L2[1], L1[1]*L2[3]+L1[3]*L2[1],
            L1[2]*L2[2], L1[2]*L2[3]+L1[3]*L2[2], L1[3]*L2[3]];
end function;

// QuadMat(F, coeffs): 3x3 symmetric matrix of a quadratic form given its 6
// coefficients in the order (x^2, xy, xz, y^2, yz, z^2).
function QuadMat(F, coeffs)
    return Matrix(F, 3, 3, [
        [coeffs[1], coeffs[2]/2, coeffs[3]/2],
        [coeffs[2]/2, coeffs[4], coeffs[5]/2],
        [coeffs[3]/2, coeffs[5]/2, coeffs[6]]
    ]);
end function;

// MobiusImages(pts, i1, i2, i3): apply the FLT sending pts[i1]->0,
// pts[i2]->1, pts[i3]->inf to the remaining 3 points.
// Returns ok, imgs where imgs = [r1, r2, r3].
// pts = sequence of <value, is_inf> pairs, length 6.
function MobiusImages(pts, i1, i2, i3)
    F := Parent(pts[1][1]);
    rest := [k : k in [1..6] | k notin {i1,i2,i3}];
    s1 := pts[i1]; s2 := pts[i2]; s3 := pts[i3];
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
    return ok, imgs;
end function;

// FindOrbit(pts): search all C(6,3)=20 ways of sending 3 of the 6 branch
// points to {0, 1, inf} via a Mobius transformation, and check whether the
// images of the remaining 3 form a Z/3-orbit {x, 1-1/x, 1/(1-x)}. On success,
// return <true, lambda>. See pipeline_math.md §8.
// pts = sequence of <value, is_inf> pairs, length 6.
function FindOrbit(pts)
    F := Parent(pts[1][1]);
    for i1 in [1..6] do
        for i2 in [i1+1..6] do
            for i3 in [i2+1..6] do
                ok, imgs := MobiusImages(pts, i1, i2, i3);
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

// FindZ2Pair(pts): detect Aut_red >= (Z/2)^2 on a genus-2 curve from its
// 6 branch points.  The normal form is y^2 = x(x-1)(x+1)(x-lam)(x-1/lam),
// with branch points {0, 1, -1, lam, 1/lam, inf}.  The Klein four-group
// V_4 acts via x->1/x, x->(lam*x-1)/(x-lam), and their composition.
// Algorithm: for each ordered triple (i1,i2,i3) of distinct indices, send
// pts[i1]->0, pts[i2]->1, pts[i3]->inf via an FLT and check if one of the
// remaining 3 images is -1 and the other two multiply to 1.
// We must try all 6*5*4=120 ordered triples (not just C(6,3)=20 unordered)
// because the condition is NOT invariant under permuting {0,1,inf}.
// Returns found, lambda where lambda is one of the inverse pair.
function FindZ2Pair(pts)
    F := Parent(pts[1][1]);
    for i1 in [1..6] do
        for i2 in [1..6] do
            if i2 eq i1 then continue; end if;
            for i3 in [1..6] do
                if i3 eq i1 or i3 eq i2 then continue; end if;
                ok, imgs := MobiusImages(pts, i1, i2, i3);
                if not ok then continue; end if;
                // imgs = images of the 3 remaining points
                // Check: is one of them -1, and are the other two inverses?
                for a in [1..3] do
                    if imgs[a] ne -1 then continue; end if;
                    bc := [imgs[j] : j in [1..3] | j ne a];
                    if bc[1] eq 0 or bc[2] eq 0 then continue; end if;
                    if bc[1] * bc[2] eq 1 then
                        return true, bc[1];
                    end if;
                end for;
            end for;
        end for;
    end for;
    return false, F!0;
end function;

// FindZ2Weak(pts): detect ANY Mobius involution permuting 6 branch points.
// This detects Aut_red >= Z/2, including both:
//   - Aut_red = (Z/2)^2 (the {0,1,-1,lam,1/lam,inf} case found by FindZ2Pair)
//   - Aut_red = Z/2 (the y^2 = x(x-1)(x-a)(x-b)(x-a(1-b)/(1-a)) case)
//
// Algorithm: for each of the 120 ordered triples, normalize 3 points to
// {0,1,inf} and check all 15 matchings of {0,1,inf,a,b,c} into 3 transposition
// pairs, plus 3 fixed-pair patterns (involution fixing 2 of {0,1,inf}).
//
// A Mobius involution on P^1 has exactly 2 fixed points, so either:
//   (A) neither fixed point is a branch point -> 3 transposition pairs
//   (B) both fixed points are branch points -> 2 fixed + 2 transposition pairs
// (Exactly 1 fixed branch point is impossible: leaves odd number to pair.)
function FindZ2Weak(pts)
    F := Parent(pts[1][1]);

    for i1 in [1..6] do
        for i2 in [1..6] do
            if i2 eq i1 then continue; end if;
            for i3 in [1..6] do
                if i3 eq i1 or i3 eq i2 then continue; end if;
                ok, imgs := MobiusImages(pts, i1, i2, i3);
                if not ok then continue; end if;
                a := imgs[1]; b := imgs[2]; c := imgs[3];

                // === Case A: 3 transposition pairs (no fixed branch points) ===

                // Type I: (0,inf) paired, involution x -> k/x
                // (0,inf)(1,a)(b,c): k=a, check b*c=a
                if a ne 0 and b*c eq a then return true, "3pair"; end if;
                // (0,inf)(1,b)(a,c): k=b, check a*c=b
                if b ne 0 and a*c eq b then return true, "3pair"; end if;
                // (0,inf)(1,c)(a,b): k=c, check a*b=c
                if c ne 0 and a*b eq c then return true, "3pair"; end if;

                // Type II: (0,1) paired, T(x) = d(x-1)/(x-d), T(inf)=d
                // (0,1)(inf,a)(b,c): check a*(b-1) = c*(b-a)
                if b ne a then
                    if a*(b-1) eq c*(b-a) then return true, "3pair"; end if;
                end if;
                // (0,1)(inf,b)(a,c): check b*(a-1) = c*(a-b)
                if a ne b then
                    if b*(a-1) eq c*(a-b) then return true, "3pair"; end if;
                end if;
                // (0,1)(inf,c)(a,b): check c*(a-1) = b*(a-c)
                if a ne c then
                    if c*(a-1) eq b*(a-c) then return true, "3pair"; end if;
                end if;

                // Type III: (1,inf) paired, T(x) = (x+d)/(x-1)
                // (0,a)(1,inf)(b,c): check (b-a) = c*(b-1)
                if b ne 1 then
                    if (b-a) eq c*(b-1) then return true, "3pair"; end if;
                end if;
                // (0,b)(1,inf)(a,c): check (a-b) = c*(a-1)
                if a ne 1 then
                    if (a-b) eq c*(a-1) then return true, "3pair"; end if;
                end if;
                // (0,c)(1,inf)(a,b): check (a-c) = b*(a-1)
                if a ne 1 then
                    if (a-c) eq b*(a-1) then return true, "3pair"; end if;
                end if;

                // Type IV: none of {0,1,inf} paired together
                // (0,a)(1,b)(inf,c): check b*(1-c) = c*(1-a)
                if b - b*c eq c - c*a then return true, "3pair"; end if;
                // (0,a)(1,c)(inf,b): check c*(1-b) = b*(1-a)
                if c - c*b eq b - b*a then return true, "3pair"; end if;
                // (0,b)(1,a)(inf,c): check a*(1-c) = c*(1-b)
                if a - a*c eq c - c*b then return true, "3pair"; end if;
                // (0,b)(1,c)(inf,a): check c*(1-a) = a*(1-b)
                if c*(1-a) eq a*(1-b) then return true, "3pair"; end if;
                // (0,c)(1,a)(inf,b): check a*(1-b) = b*(1-c)
                if a - a*b eq b - b*c then return true, "3pair"; end if;
                // (0,c)(1,b)(inf,a): check b*(1-a) = a*(1-c)
                if b*(1-a) eq a*(1-c) then return true, "3pair"; end if;

                // === Case B: 2 fixed points among {0,1,inf} ===

                // Fixed {0,inf}: T(x) = -x. T(1)=-1.
                // One of {a,b,c} = -1, other two sum to 0.
                if a eq -1 and b + c eq 0 then return true, "2fixed"; end if;
                if b eq -1 and a + c eq 0 then return true, "2fixed"; end if;
                if c eq -1 and a + b eq 0 then return true, "2fixed"; end if;

                // Fixed {0,1}: T(x) = x/(2x-1). T(inf) = 1/2.
                // One of {a,b,c} = 1/2, other two satisfy T(x)=y.
                half := F!(1/2);
                if a eq half then
                    if 2*b - 1 ne 0 and b/(2*b-1) eq c then return true, "2fixed"; end if;
                end if;
                if b eq half then
                    if 2*a - 1 ne 0 and a/(2*a-1) eq c then return true, "2fixed"; end if;
                end if;
                if c eq half then
                    if 2*a - 1 ne 0 and a/(2*a-1) eq b then return true, "2fixed"; end if;
                end if;

                // Fixed {1,inf}: T(x) = 2-x. T(0)=2.
                // One of {a,b,c} = 2, other two sum to 2.
                two := F!2;
                if a eq two and b + c eq two then return true, "2fixed"; end if;
                if b eq two and a + c eq two then return true, "2fixed"; end if;
                if c eq two and a + b eq two then return true, "2fixed"; end if;

            end for;
        end for;
    end for;

    return false, "";
end function;

// =====================================================================
// Main pipeline driver
// =====================================================================

procedure RunSteinerPipeline(label, F_input)

// If true, run the F_p cross-check block (STEPs 3-6): complex display, quartic
// decompositions, genus-2 curves over F_p, and Igusa invariants over F_p.
// These are a sanity check only — nothing in STEPs 7+ consumes their output.
// STEP 2 (contact quadratics and conic verification) always runs since it
// exercises the merged FindConic helper used later by STEP 8.
do_fp_crosscheck := true;

print "============================================================";
printf "Pipeline run: %o\n", label;
printf "F = %o\n", F_input;
print "============================================================";

QQ := Rationals();
P2Q<x,y,z> := ProjectiveSpace(QQ, 2);

C_Q := Curve(P2Q, F_input);
assert IsNonsingular(C_Q);
print "Quartic is smooth over Q.";

// =====================================================================
// STEP 0: Find a good prime and compute bitangent lines over F_p
// =====================================================================
// See pipeline_math.md §3. A line L is a bitangent iff F|_L is a perfect
// square (the 28 bitangents of a smooth plane quartic = odd theta chars).

RQ<xq,yq,zq> := PolynomialRing(QQ, 3);
F_poly := Evaluate(F_input, [xq, yq, zq]);

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
// See pipeline_math.md §4 (and §4.1 for the ClassJ2 / Cl[2] vs J[2] warning).
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
// See pipeline_math.md §5. A bitangent L satisfies F|_L = c * h_L^2 for a
// scalar c and a degree-2 polynomial h_L ("contact quadratic"). For a
// pair-of-pairs {{i,j},{k,l}}, the witnessing conic Q passes simply through
// the 8 contact points (Bezout: Q.C = 8 = exactly those points); equivalently
// Q|_{L_m} is proportional to h_m for each of the 4 lines. That gives
// FindConic's 12x10 linear system (3 rows/line, 6 conic unknowns + 4 lambdas).
// Helpers ContactQuadratic, RestrictionMatrix, FindConic are at file scope.

print "\n=== Computing witnessing conics ===";

Runi<tt> := PolynomialRing(Fp);

contact_quads := [];
param_type := [];
for i in [1..28] do
    pt, hq := ContactQuadratic(Fp, fp_proj, lines_Fp[i], Runi);
    Append(~param_type, pt);
    Append(~contact_quads, hq);
end for;
print "Contact quadratics computed.";

steiner_data := [];
complex_idx := 0;
for key in Keys(class_to_pairs) do
    complex_idx +:= 1;
    cpairs := class_to_pairs[key];
    conics := [];
    for a in [1..6] do
        for b in [a+1..6] do
            pa := cpairs[a]; pb := cpairs[b];
            conic, ok := FindConic(Fp, param_type, contact_quads, [pa[1], pa[2], pb[1], pb[2]]);
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
                Rm := RestrictionMatrix(Fp, param_type[m]);
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
// STEPs 3-6: F_p cross-check (display, decomp, genus-2, Igusa)
// =====================================================================
// These sanity checks validate the F_p pipeline before re-running the same
// math over K in STEPs 8-10. None of their output feeds downstream steps.
// Gate with `do_fp_crosscheck := false` at the top to skip them.

if do_fp_crosscheck then

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
// See pipeline_math.md §5. Solve a 3-row linear system in the degree-4
// monomial basis to find (a, b) such that aF - bQ^2 is the 4-line product.

print "\n=== Quartic decompositions ===";

RR<xx,yy,zz> := PolynomialRing(Fp, 3);
F_Fp := Evaluate(F_poly, [xx, yy, zz]);
mons4 := MonomialsOfDegree(RR, 4);

// CoeffVec / LProdCoeffs / QuadMat are defined at file scope.

v_F := CoeffVec(F_Fp, mons4);

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

            vprod := CoeffVec(prod_L, mons4);
            vQ2 := CoeffVec(Q_poly^2, mons4);
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
// See pipeline_math.md §6. From aF = L1*L2 * L3*L4 + bQ^2 build the 3x3
// pencil M(t) = b*M(L1L2) + 2t*b*M(Q) + t^2*(-M(L3L4)); genus-2: y^2 = -det M(t).

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

    M1 := QuadMat(Fp, Q1c); M2 := QuadMat(Fp, Q2c); M3 := QuadMat(Fp, Q3c);
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

end if;  // do_fp_crosscheck

// =====================================================================
// STEP 7: Bitangent lines, genus-2 curves, and Igusa invariants
//         over a number field
// =====================================================================
// See pipeline_math.md §3. Find the bitangent splitting field K over Q by
// eliminating variables from the tangency ideal, then re-solve over K for
// each chart case. Results are matched mod p to the F_p ordering.

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
    printf "  K defining polynomial: %o\n", DefiningPolynomial(K);
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

// Deduplicate by NormalizeLine (defined at file scope).
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

printf "Total bitangent lines over K (deduplicated): %o\n", #lines_K;

if #lines_K ne 28 then
    printf "WARNING: expected 28, got %o.\n", #lines_K;
    if #lines_K lt 28 then
        print "Number field genus-2 computation skipped.\n\nDone.";
        return;
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

// Build lookup from normalized F_p lines to their index
fp_lookup := AssociativeArray();
for i in [1..28] do
    nL := NormalizeLine(lines_Fp[i]);
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
        nL := NormalizeLine(LK_Fp);
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
            nL := NormalizeLine(LK_Fp);
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
// STEP 7.5: Possibly extend K so contact quadratics live over K
// =====================================================================
// The contact quadratic h_L of a bitangent L satisfies F|_L = c * h_L^2
// for some scalar c in K. If c is not a square in K, then h_L only lives
// over K(sqrt c). Pre-scan all 28 bitangents and extend K accordingly so
// the rest of the pipeline (Steps 8-11) operates over a single field.

print "\n=== Pre-scanning contact quadratics for needed sqrts ===";
RKuni_pre<tK_pre> := PolynomialRing(K);
RK_pre<xK_pre,yK_pre,zK_pre> := PolynomialRing(K, 3);
FK_pre := Evaluate(F_poly, [xK_pre, yK_pre, zK_pre]);

needed_sqfree := [];  // squarefree integers d such that we need sqrt(d)
for i in [1..28] do
    A := lines_K[i][1]; B := lines_K[i][2]; CC := lines_K[i][3];
    if CC ne 0 then
        rest_pre := Evaluate(FK_pre, [tK_pre, K!1, (-A*tK_pre - B)/CC]);
        rest_pre *:= CC^4;
    elif B ne 0 then
        rest_pre := Evaluate(FK_pre, [tK_pre, -A*tK_pre/B, K!1]);
        rest_pre *:= B^4;
    else
        rest_pre := Evaluate(FK_pre, [RKuni_pre!0, tK_pre, K!1]);
    end if;
    fac_pre := Factorization(rest_pre);
    if #fac_pre eq 0 then
        rv_pre := K ! rest_pre;
    else
        srm := &*[e[1]^(e[2] div 2) : e in fac_pre];
        rv_pre := LeadingCoefficient(rest_pre) / LeadingCoefficient(srm)^2;
    end if;
    is_sq, _ := IsSquare(rv_pre);
    if not is_sq then
        if Type(K) eq FldRat then
            // Squarefree part of numerator * denominator (squarefree part is
            // invariant up to squares)
            n := Numerator(rv_pre) * Denominator(rv_pre);
            sgn := Sign(n);
            sf := sgn * SquarefreePart(Abs(n));
            if sf notin needed_sqfree then
                Append(~needed_sqfree, sf);
            end if;
        else
            // Number-field case: just record the value
            if rv_pre notin needed_sqfree then
                Append(~needed_sqfree, rv_pre);
            end if;
        end if;
    end if;
end for;

if #needed_sqfree gt 0 then
    printf "Extending K to contain sqrt(d) for d in %o\n", needed_sqfree;
    if Type(K) eq FldRat then
        // Build successive quadratic extensions, then take an absolute field
        K_ext := QuadraticField(needed_sqfree[1]);
        for j in [2..#needed_sqfree] do
            Pj := PolynomialRing(K_ext);
            mp := Pj.1^2 - K_ext!needed_sqfree[j];
            if not HasRoot(mp) then
                K_ext := ext<K_ext | mp>;
            end if;
        end for;
        K := AbsoluteField(K_ext);
    else
        K_ext := K;
        for v in needed_sqfree do
            Pj := PolynomialRing(K_ext);
            mp := Pj.1^2 - K_ext!v;
            if not HasRoot(mp) then
                K_ext := ext<K_ext | mp>;
            end if;
        end for;
        K := AbsoluteField(K_ext);
    end if;
    printf "Extended K has degree %o over Q.\n", Degree(K, Rationals());
    // Re-coerce lines_K into the new K
    lines_K := [[K!l[j] : j in [1..3]] : l in lines_K];
else
    print "No extension needed; contact quadratics live over current K.";
end if;

// =====================================================================
// STEP 8: Conics, decompositions, genus-2 curves, Igusa invariants over K
// =====================================================================
// See pipeline_math.md §§5-7. Re-run STEPs 2, 4, 5 over K in one pass:
// TryMakeGenus2 iterates the 15 pair-of-pairs for each complex and returns
// on the first that yields a genus-2 curve.

print "\n=== Computing genus-2 curves over K ===";

RK<xK,yK,zK> := PolynomialRing(K, 3);
FK := Evaluate(F_poly, [xK, yK, zK]);
mons4K := MonomialsOfDegree(RK, 4);

vFK := CoeffVec(FK, mons4K);

function LinFormK(idx)
    return lines_K[idx][1]*xK + lines_K[idx][2]*yK + lines_K[idx][3]*zK;
end function;

// Contact quadratics over K (re-uses the merged ContactQuadratic helper).
// Note: sign of contact quadratic h_i doesn't affect FindConic (the lambda_i
// parameter absorbs the sign), so no sign correction needed.
RKuni<tK> := PolynomialRing(K);
contact_quads_K := [];
param_type_K := [];
for i in [1..28] do
    pt, hq := ContactQuadratic(K, FK, lines_K[i], RKuni);
    Append(~param_type_K, pt);
    Append(~contact_quads_K, hq);
end for;
print "Contact quadratics over K computed.";

PtK<t_K> := PolynomialRing(K);

// TryMakeGenus2(cpairs): iterate the C(6,2)=15 pair-of-pairs for a single
// Steiner complex and return on the first that yields a genus-2 curve.
// Returns <ok, genus2_poly, igusa_invariants, [conic_fails, decomp_fails,
// deg_fails]>. See pipeline_math.md §§5-7 (contact conic -> quartic
// decomposition -> determinantal pencil -> Prym).
function TryMakeGenus2(cpairs)
    conic_fail := 0; decomp_fail := 0; deg_fail := 0;
    for pi1 in [1..6] do
        for pi2 in [pi1+1..6] do
            pa := cpairs[pi1]; pb := cpairs[pi2];
            Qc, ok := FindConic(K, param_type_K, contact_quads_K, [pa[1], pa[2], pb[1], pb[2]]);
            if not ok then conic_fail +:= 1; continue; end if;

            prod_L := LinFormK(pa[1])*LinFormK(pa[2])*LinFormK(pb[1])*LinFormK(pb[2]);
            Q_poly := Qc[1]*xK^2+Qc[2]*xK*yK+Qc[3]*xK*zK+Qc[4]*yK^2+Qc[5]*yK*zK+Qc[6]*zK^2;
            vprod := CoeffVec(prod_L, mons4K);
            vQ2K := CoeffVec(Q_poly^2, mons4K);
            matK := Matrix(K, 3, #mons4K, [vFK, vprod, vQ2K]);
            NK := Nullspace(matK);
            if Dimension(NK) eq 0 then decomp_fail +:= 1; continue; end if;
            rel := NK.1;
            if rel[2] eq 0 then decomp_fail +:= 1; continue; end if;
            b_c := rel[3]/rel[2];

            Q1c := LProdCoeffs(lines_K[pa[1]], lines_K[pa[2]]);
            Q1c := [b_c * e : e in Q1c];
            Q3c := LProdCoeffs(lines_K[pb[1]], lines_K[pb[2]]);
            Q3c := [-e : e in Q3c];
            Q2c := [K | b_c * Qc[idx] : idx in [1..6]];

            M1 := QuadMat(K, Q1c); M2 := QuadMat(K, Q2c); M3 := QuadMat(K, Q3c);
            MK := ZeroMatrix(PtK, 3, 3);
            for ii in [1..3] do
                for jj in [1..3] do
                    MK[ii,jj] := PtK!(M1[ii,jj]) + 2*t_K*PtK!(M2[ii,jj]) + t_K^2*PtK!(M3[ii,jj]);
                end for;
            end for;
            dp := -Determinant(MK);
            if Degree(dp) lt 5 then deg_fail +:= 1; continue; end if;

            HK := HyperellipticCurve(dp);
            return true, dp, IgusaInvariants(HK), [conic_fail, decomp_fail, deg_fail];
        end for;
    end for;
    return false, PtK!0, [K|0,0,0,0,0], [conic_fail, decomp_fail, deg_fail];
end function;

genus2_K := AssociativeArray();
igusa_K := AssociativeArray();

for ci in [1..#steiner_data] do
    ok, dp, IKvals, fails := TryMakeGenus2(steiner_data[ci][1]);
    if ok then
        genus2_K[ci] := dp;
        igusa_K[ci] := IKvals;
    else
        printf "Complex #%o: FAILED (conic=%o, decomp=%o, deg=%o of 15)\n",
            ci, fails[1], fails[2], fails[3];
    end if;
end for;

printf "Genus-2 curves over K: %o / 63 complexes.\n", #Keys(genus2_K);

// =====================================================================
// STEP 9: Igusa invariants and isomorphism classes
// =====================================================================
// See pipeline_math.md §6. Absolute Igusa invariants j1,j2,j3 distinguish
// geometric isomorphism classes of the 63 Prym genus-2 curves.

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
// STEP 9b: Syzygetic triples within Igusa classes
// =====================================================================
// Three nonzero J[2] elements x,y,z are syzygetic iff x+y+z = 0 in F_2^6.
// For each Igusa isomorphism class, count unordered syzygetic triples
// among the complexes sharing that class.

print "\n=== Syzygetic triples within Igusa classes ===";
for cl in inv_classes do
    cls_members := Sort([ci : ci in Keys(abs_inv_K) | abs_inv_K[ci] eq cl]);
    n_cls := #cls_members;
    syz_count := 0;
    syz_triples := [];
    for a in [1..n_cls] do
        for b in [a+1..n_cls] do
            for c in [b+1..n_cls] do
                ki := steiner_data[cls_members[a]][3];
                kj := steiner_data[cls_members[b]][3];
                kk := steiner_data[cls_members[c]][3];
                if &and[(ki[m] + kj[m] + kk[m]) mod 2 eq 0 : m in [1..#ki]] then
                    syz_count +:= 1;
                    Append(~syz_triples, [cls_members[a], cls_members[b], cls_members[c]]);
                end if;
            end for;
        end for;
    end for;
    printf "  j = %o (%o complexes): %o syzygetic triples\n", cl, n_cls, syz_count;
    for tr in syz_triples do
        printf "    {%o, %o, %o}\n", tr[1], tr[2], tr[3];
    end for;
end for;

// =====================================================================
// STEP 10: Elliptic j-invariants via Z/3Z action on branch points
// =====================================================================
// See pipeline_math.md §8.
// The genus-2 curve y^2 = f(t) has 6 branch points (5 finite roots + infinity
// if deg=5, or 6 finite roots if deg=6). A Z/3Z partition of these 6 points
// into two orbits {x, 1-1/x, 1/(1-x)} determines a cross-ratio lambda,
// from which we get the j-invariant of the associated elliptic curve:
//   disc = lambda^2 - lambda + 1
//   s = (1-lambda)*(lambda + sqrt(disc))^2
//   j = 256*(1 - s*(1-s))^3 / (s^2*(1-s)^2)

print "\n=== Elliptic j-invariants via Z/3Z orbits on branch points ===";
// FindOrbit (file scope) searches all C(6,3)=20 partitions of 6 branch points
// for a Z/3Z orbit {x, 1-1/x, 1/(1-x)}.

j_inv_K := AssociativeArray();
z2_data := AssociativeArray();

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

    // --- Z/3 check ---
    found_orb, lam := FindOrbit(rts_K);
    if not found_orb then
        printf "Complex #%o: no Z/3Z orbit found\n", ci;
    else
        // j-invariant from cross-ratio lambda
        F_lam := Parent(lam);
        disc := lam^2 - lam + 1;
        if disc eq 0 then
            printf "Complex #%o: Z/3 degenerate (disc=0)\n", ci;
        else
            is_sq, sq_v := IsSquare(disc);
            if not is_sq then
                PF2 := PolynomialRing(F_lam);
                F2_loc<sq2> := ext<F_lam | PF2![-disc,0,1]>;
                lam2 := F2_loc!lam;
                s := (1-lam2)*(lam2+sq2)^2;
            else
                s := (1-lam)*(lam+sq_v)^2;
            end if;

            if s eq 0 or s eq 1 then
                printf "Complex #%o: Z/3 degenerate (s=%o)\n", ci, s;
            else
                j := 2^8*(1-s*(1-s))^3/(s^2*(1-s)^2);
                abs_mp := AbsoluteMinimalPolynomial(j);
                j_inv_K[ci] := abs_mp;
                printf "Complex #%o: j abs min poly = %o\n", ci, abs_mp;
            end if;
        end if;
    end if;

    // --- Z/2 check ---
    found_z2, lam_z2 := FindZ2Pair(rts_K);
    if found_z2 then
        abs_mp_z2 := AbsoluteMinimalPolynomial(lam_z2);
        // j-invariant of the elliptic factor from the Z/2 quotient.
        // Set t = lam + sqrt(lam^2-1), then j = j_Legendre(-t^2)
        // = 256*(1+t^2+t^4)^3 / (t^4*(1+t^2)^2).
        F_z2 := Parent(lam_z2);
        disc_z2 := lam_z2^2 - 1;
        if disc_z2 eq 0 then
            printf "Complex #%o: Z/2 degenerate (disc=0)\n", ci;
        else
            is_sq_z2, sq_z2 := IsSquare(disc_z2);
            if not is_sq_z2 then
                PF_z2 := PolynomialRing(F_z2);
                F_z2_ext<sq_z2> := ext<F_z2 | PF_z2![-disc_z2,0,1]>;
                t_z2 := F_z2_ext!lam_z2 + sq_z2;
            else
                t_z2 := lam_z2 + sq_z2;
            end if;
            s_z2 := -t_z2^2;
            den_z2 := s_z2^2*(s_z2-1)^2;
            if den_z2 eq 0 then
                printf "Complex #%o: Z/2 degenerate (den=0)\n", ci;
            else
                j_z2 := 256*(s_z2^2 - s_z2 + 1)^3 / den_z2;
                abs_mp_j_z2 := AbsoluteMinimalPolynomial(j_z2);
                z2_data[ci] := <lam_z2, abs_mp_z2, abs_mp_j_z2>;
                printf "Complex #%o: extra Z/2, lambda min poly = %o, j min poly = %o\n",
                    ci, abs_mp_z2, abs_mp_j_z2;
            end if;
        end if;
    end if;

    // --- Z/2 weak check (Aut_red >= Z/2, includes both Z/2 and (Z/2)^2) ---
    if not found_z2 then
        found_z2w, z2w_type := FindZ2Weak(rts_K);
        if found_z2w then
            printf "Complex #%o: weak Z/2 detected (type=%o, Aut_red = Z/2 not (Z/2)^2)\n",
                ci, z2w_type;
        end if;
    end if;
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

// Z/2 summary: group by Igusa class
printf "\n=== Extra Z/2 automorphism on branch points ===\n";
printf "Complexes with extra Z/2: %o / %o\n", #Keys(z2_data), #Keys(genus2_K);
if #Keys(z2_data) gt 0 then
    for cl in inv_classes do
        z2_in_cl := Sort([ci : ci in Keys(z2_data) | IsDefined(abs_inv_K, ci)
            and abs_inv_K[ci] eq cl]);
        n_in_cl := #[ci : ci in Keys(abs_inv_K) | abs_inv_K[ci] eq cl];
        if #z2_in_cl gt 0 then
            printf "  Igusa class %o: %o / %o complexes have Z/2\n",
                cl, #z2_in_cl, n_in_cl;
            for ci in z2_in_cl do
                printf "    Complex #%o: lambda min poly = %o, j min poly = %o\n",
                    ci, z2_data[ci][2], z2_data[ci][3];
            end for;
        end if;
    end for;
end if;

// =====================================================================
// STEP 11: Z/3Z orbit analysis on Steiner complexes
// =====================================================================
// See pipeline_math.md §2.5 and klein_steiner_pryms.md.
// If sigma: (x:y:z) -> (y:z:x) preserves F, compute its induced permutation
// on the 28 bitangents and 63 complexes and list the Z/3-orbits.

print "\n=== Z/3Z action on Steiner complexes ===";

F_sigma := Evaluate(F_poly, [yq, zq, xq]);
if F_sigma ne F_poly then
    print "Quartic is NOT invariant under (x:y:z) -> (y:z:x). Skipping.";
else
    print "Quartic is invariant under sigma: (x:y:z) -> (y:z:x).";

    sigma_perm := [];
    for i in [1..28] do
        L := lines_K[i];
        img := NormalizeLine([L[3], L[1], L[2]]);
        found_j := 0;
        for j in [1..28] do
            if NormalizeLine(lines_K[j]) eq img then found_j := j; break; end if;
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

// =====================================================================
// STEP 12: Full Aut(C) orbit analysis on Steiner complexes
// =====================================================================
// If the quartic has only even-degree monomials, then sign changes
// (x:y:z) -> (-x:y:z), (x:-y:z) give extra (Z/2)^2 automorphisms.
// Together with coordinate permutations, this gives S3 x (Z/2)^2 = S4.

// Check: does F only have even-degree monomials in each variable?
all_even := true;
for exp in [0..4] do
    for exp2 in [0..4-exp] do
        exp3 := 4 - exp - exp2;
        c := MonomialCoefficient(F_poly, xq^exp * yq^exp2 * zq^exp3);
        if c ne 0 and (exp mod 2 ne 0 or exp2 mod 2 ne 0 or exp3 mod 2 ne 0) then
            all_even := false;
            break exp;
        end if;
    end for;
end for;

if all_even then
    print "\n=== Full Aut(C) orbit analysis (sign changes detected) ===";
    print "Quartic has only even-degree monomials => sign changes are automorphisms.";
    print "Aut(C) contains S3 x (Z/2)^2 = S4 (order 24).";

    // Build sign change permutation on the 28 bitangents: (x:y:z) -> (-x:y:z)
    eps_perm := [];
    for i in [1..28] do
        L := lines_K[i];
        // Line ax+by+cz=0 maps to -ax+by+cz=0, i.e. [-a, b, c]
        img := NormalizeLine([-L[1], L[2], L[3]]);
        found_j := 0;
        for j in [1..28] do
            if NormalizeLine(lines_K[j]) eq img then found_j := j; break; end if;
        end for;
        if found_j eq 0 then
            printf "Warning: sign change image of line %o not found\n", i;
        end if;
        Append(~eps_perm, found_j);
    end for;

    // Build all S4 elements as compositions of sigma, tau (if defined), eps
    // We need the transposition tau: (x:y:z) -> (y:x:z)
    tau_perm := [];
    for i in [1..28] do
        L := lines_K[i];
        img := NormalizeLine([L[2], L[1], L[3]]);
        found_j := 0;
        for j in [1..28] do
            if NormalizeLine(lines_K[j]) eq img then found_j := j; break; end if;
        end for;
        Append(~tau_perm, found_j);
    end for;

    // Generate the full group as permutations of [1..28]
    S28 := SymmetricGroup(28);
    g_sigma := S28 ! sigma_perm;
    g_tau := S28 ! tau_perm;
    g_eps := S28 ! eps_perm;
    G_aut := sub<S28 | g_sigma, g_tau, g_eps>;
    printf "Aut(C) on 28 bitangents: order %o\n", #G_aut;

    // Induced action on the 63 Steiner complexes
    function ApplyPermToComplex(perm_28, ci)
        pairs := steiner_data[ci][1];
        img_pairs := [[perm_28[p[1]], perm_28[p[2]]] : p in pairs];
        return FindComplexIdx(CanonicalComplex(img_pairs));
    end function;

    // Build S4 orbits on 63 complexes
    used_full := {};
    full_orbits := [];
    for ci in [1..63] do
        if ci in used_full then continue; end if;
        orb := {ci};
        for g in G_aut do
            pg := [i^g : i in [1..28]];
            img := ApplyPermToComplex(pg, ci);
            Include(~orb, img);
        end for;
        Append(~full_orbits, Sort(Setseq(orb)));
        used_full join:= orb;
    end for;

    Sort(~full_orbits, func<a,b | #a - #b>);
    printf "Aut(C) orbits on 63 complexes: %o orbits\n", #full_orbits;
    printf "Orbit sizes: %o\n", [#o : o in full_orbits];
    for idx in [1..#full_orbits] do
        o := full_orbits[idx];
        printf "  Orbit %o (size %o): %o\n", idx, #o, o;
    end for;

    // Check if orbits match Igusa classes
    printf "\nComparing Aut orbits to Igusa classes:\n";
    for idx in [1..#full_orbits] do
        o := full_orbits[idx];
        // Find which Igusa class(es) this orbit overlaps
        cls_in_orb := {};
        for ci in o do
            if IsDefined(abs_inv_K, ci) then
                Include(~cls_in_orb, abs_inv_K[ci]);
            end if;
        end for;
        if #cls_in_orb eq 1 then
            printf "  Orbit %o (size %o): single Igusa class\n", idx, #o;
        else
            printf "  Orbit %o (size %o): %o Igusa classes (!)\n", idx, #o, #cls_in_orb;
        end if;
    end for;
end if;

print "\n========================================";
printf "FINISHED: %o\n", label;
print "========================================";

end procedure;
