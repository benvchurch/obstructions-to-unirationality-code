/*
 * check_fermat_uniserial.m
 *
 * Verify that the F_2[Aut(C)]-module J(Fermat)[2] is uniserial with
 * composition series M1 < M3 < M5 < M6 (dims 1, 3, 5, 6) and each
 * successive extension non-split.
 */

SetOutputFile("results/fermat_uniserial.log" : Overwrite := true);
SetColumns(0);
F2 := GF(2);

// ---- Helpers (from aut_j2_modules.m) ----

function FindBitangents(F, Fq)
    P2 := Parent(F);
    x := P2.1; y := P2.2; z := P2.3;
    bits := [];
    Pt<t> := PolynomialRing(Fq);
    for a in Fq do
        for b in Fq do
            f_line := Evaluate(F, [t, 1, a*t + b]);
            if Degree(f_line) lt 0 then continue; end if;
            if f_line eq 0 then continue; end if;
            lc := LeadingCoefficient(f_line);
            f_norm := f_line / lc;
            is_sq, _ := IsSquare(f_norm);
            if is_sq then
                Append(~bits, [Fq | -a, -b, 1]);
            end if;
        end for;
    end for;
    for c in Fq do
        f_line := Evaluate(F, [1, c, t]);
        if Degree(f_line) lt 0 then continue; end if;
        if f_line eq 0 then continue; end if;
        lc := LeadingCoefficient(f_line);
        f_norm := f_line / lc;
        is_sq, _ := IsSquare(f_norm);
        if is_sq then
            Append(~bits, [Fq | c, -1, 0]);
        end if;
    end for;
    f_line := Evaluate(F, [0, 1, t]);
    if Degree(f_line) ge 0 and f_line ne 0 then
        lc := LeadingCoefficient(f_line);
        f_norm := f_line / lc;
        is_sq, _ := IsSquare(f_norm);
        if is_sq then
            Append(~bits, [Fq | 1, 0, 0]);
        end if;
    end if;
    bits_norm := [];
    for L in bits do
        for k in [1..3] do
            if L[k] ne 0 then
                Append(~bits_norm, [L[i]/L[k] : i in [1..3]]);
                break;
            end if;
        end for;
    end for;
    bits_uniq := [];
    for L in bits_norm do
        if not (L in bits_uniq) then
            Append(~bits_uniq, L);
        end if;
    end for;
    return bits_uniq;
end function;

function NormalizeLine(L)
    for k in [1..3] do
        if L[k] ne 0 then
            return [L[i]/L[k] : i in [1..3]];
        end if;
    end for;
    return L;
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
            if NormalizeLine(bits[j]) eq img_n then
                found := j;
                break;
            end if;
        end for;
        if found eq 0 then error "LinePermutation: image not found"; end if;
        Append(~perm, found);
    end for;
    return perm;
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

function AutToMatrix(g, Cpts, Fq)
    eqs := DefiningEquations(g);
    Pin := [];
    Pout := [];
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
    if #Pin lt 4 then error "AutToMatrix: not enough points"; end if;
    return PGL3FromImages(Pin, Pout, Fq);
end function;

// ---- Build the Fermat J[2] module ----

p := 41;
Fq := GF(p);
P2<x,y,z> := ProjectiveSpace(Fq, 2);
R := CoordinateRing(P2);
F := x^4 + y^4 + z^4;
C := Curve(P2, F);

printf "Fermat quartic over F_%o\n", p;
printf "Computing automorphisms...\n";
auts := Automorphisms(C);
printf "|Aut(C)| = %o\n", #auts;

printf "Finding bitangents...\n";
bits := FindBitangents(F, Fq);
printf "Found %o bitangents\n", #bits;
assert #bits eq 28;

printf "Computing rational points...\n";
Cpts_set := Points(C);
Cpts := [];
for pt in Cpts_set do
    v := Eltseq(pt);
    if &and[IsCoercible(Fq, c) : c in v] then
        Append(~Cpts, [Fq | c : c in v]);
    end if;
end for;
printf "%o rational points\n", #Cpts;

perms := [];
for g in auts do
    M := AutToMatrix(g, Cpts, Fq);
    perm := LinePermutation(M, bits);
    Append(~perms, perm);
end for;
printf "Built bitangent permutations for %o automorphisms\n", #perms;

printf "Building function field and class group...\n";
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
FF<uu> := FunctionField(f_u);
elt_t := FF ! t_var;
Cl, mp := ClassGroup(FF);
invs := Invariants(Cl);
printf "Class group invariants: %o\n", invs;

even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
dim := #even_idx;
printf "J[2] dimension = %o\n", dim;
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

J2_vec := [];
for i in [1..28] do
    if i eq ref then
        Append(~J2_vec, [F2 ! 0 : k in [1..dim]]);
    else
        v := ClassJ2(half_divs[i]);
        Append(~J2_vec, [F2 ! Integers() ! s : s in v]);
    end if;
end for;

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

G_mat := sub<GL(dim, F2) | gen_matrices_f2>;
printf "F_2-image has order %o, group %o\n", #G_mat, GroupName(G_mat);

Mod := GModule(G_mat);
printf "\nModule M: dim %o, irreducible? %o, semisimple? %o\n",
    Dimension(Mod), IsIrreducible(Mod), IsSemisimple(Mod);

indecs := IndecomposableSummands(Mod);
printf "Indecomposable summands: %o\n", #indecs;
assert #indecs eq 1;
printf "Module is indecomposable (single summand).\n";

// ========================================================
// RADICAL SERIES (top-down unique filtration for uniserial)
// ========================================================
printf "\n========================================\n";
printf "RADICAL SERIES\n";
printf "========================================\n";

rad_series := [* Mod *];
current := Mod;
for step in [1..10] do
    rad := JacobsonRadical(current);
    Append(~rad_series, rad);
    printf "rad^%o(M): dim %o\n", step, Dimension(rad);
    if Dimension(rad) eq 0 then break; end if;
    current := rad;
end for;

printf "\nRadical series dimensions:";
for i in [1..#rad_series] do
    printf " %o", Dimension(rad_series[i]);
end for;
printf "\n";

n_steps := #rad_series;
printf "Successive quotient dimensions:";
for i in [1..n_steps-1] do
    printf " %o", Dimension(rad_series[i]) - Dimension(rad_series[i+1]);
end for;
printf "\n";

// ========================================================
// SOCLE SERIES (bottom-up)
// ========================================================
printf "\n========================================\n";
printf "SOCLE SERIES\n";
printf "========================================\n";

soc1 := Socle(Mod);
printf "Socle(M) = S1: dim %o\n", Dimension(soc1);

// ========================================================
// MAXIMAL SUBMODULE UNIQUENESS (= uniseriality check)
// ========================================================
printf "\n========================================\n";
printf "UNISERIALITY: unique maximal submodule at each level\n";
printf "========================================\n";

printf "\nMaximal submodules of M (dim %o):\n", Dimension(Mod);
max_M := MaximalSubmodules(Mod);
printf "  Count: %o\n", #max_M;
for i in [1..#max_M] do
    printf "  maxsub %o: dim %o\n", i, Dimension(max_M[i]);
end for;

if #max_M eq 1 then
    M5 := max_M[1];
    printf "  UNIQUE maximal submodule M5, dim %o. Good.\n", Dimension(M5);

    printf "\nMaximal submodules of M5 (dim %o):\n", Dimension(M5);
    max_M5 := MaximalSubmodules(M5);
    printf "  Count: %o\n", #max_M5;
    for i in [1..#max_M5] do
        printf "  maxsub %o: dim %o\n", i, Dimension(max_M5[i]);
    end for;

    if #max_M5 eq 1 then
        M3 := max_M5[1];
        printf "  UNIQUE maximal submodule M3, dim %o. Good.\n", Dimension(M3);

        printf "\nMaximal submodules of M3 (dim %o):\n", Dimension(M3);
        max_M3 := MaximalSubmodules(M3);
        printf "  Count: %o\n", #max_M3;
        for i in [1..#max_M3] do
            printf "  maxsub %o: dim %o\n", i, Dimension(max_M3[i]);
        end for;

        if #max_M3 eq 1 then
            M1 := max_M3[1];
            printf "  UNIQUE maximal submodule M1, dim %o. Good.\n", Dimension(M1);
            printf "\nM1 irreducible? %o\n", IsIrreducible(M1);
        else
            printf "  WARNING: M3 has %o maximal submodules (not uniserial at this level).\n", #max_M3;
        end if;
    else
        printf "  WARNING: M5 has %o maximal submodules (not uniserial at this level).\n", #max_M5;
    end if;
else
    printf "  WARNING: M has %o maximal submodules (not uniserial at top level).\n", #max_M;
end if;

// ========================================================
// NON-SPLITTING OF EACH EXTENSION
// ========================================================
printf "\n========================================\n";
printf "NON-SPLITTING CHECKS\n";
printf "========================================\n";

// We check: for each step R[i+1] < R[i] in the radical series,
// does R[i+1] have a complement in R[i]?
// Equivalently: is there a submodule C of R[i] with
//   dim(C) = dim(R[i]) - dim(R[i+1])  and  C meet R[i+1] = 0?

for step in [1..n_steps-2] do
    big := rad_series[step];
    small := rad_series[step+1];
    codim := Dimension(big) - Dimension(small);
    if Dimension(small) eq 0 then continue; end if;

    printf "\nExtension: 0 -> rad^%o (dim %o) -> rad^%o (dim %o) -> quotient (dim %o) -> 0\n",
        step, Dimension(small), step-1, Dimension(big), codim;

    subs := Submodules(big);
    printf "  Total submodules of rad^%o: %o\n", step-1, #subs;

    has_complement := false;
    for S in subs do
        if Dimension(S) eq codim then
            inter := S meet small;
            if Dimension(inter) eq 0 then
                has_complement := true;
                break;
            end if;
        end if;
    end for;

    if has_complement then
        printf "  SPLITS: complement found.\n";
    else
        printf "  NON-SPLIT: no complement exists.\n";
    end if;
end for;

// ========================================================
// COMPOSITION FACTORS identification
// ========================================================
printf "\n========================================\n";
printf "COMPOSITION FACTORS\n";
printf "========================================\n";

cf := CompositionFactors(Mod);
printf "Number of composition factors: %o\n", #cf;
for i in [1..#cf] do
    printf "  factor %o: dim %o, abs irreducible? %o\n",
        i, Dimension(cf[i]), IsAbsolutelyIrreducible(cf[i]);
end for;

// Check which factors are isomorphic
if #cf ge 2 then
    printf "\nIsomorphism between composition factors:\n";
    for i in [1..#cf] do
        for j in [i+1..#cf] do
            if Dimension(cf[i]) eq Dimension(cf[j]) then
                iso := IsIsomorphic(cf[i], cf[j]);
                printf "  factor %o ~ factor %o? %o\n", i, j, iso;
            end if;
        end for;
    end for;
end if;

// ========================================================
// SUMMARY
// ========================================================
printf "\n========================================\n";
printf "SUMMARY\n";
printf "========================================\n";
printf "Fermat J[2] as F_2[Aut(C)]-module:\n";
printf "  dim = 6, indecomposable, non-semisimple\n";
printf "  Composition factors: ";
for i in [1..#cf] do
    if i gt 1 then printf ", "; end if;
    printf "dim %o", Dimension(cf[i]);
end for;
printf "\n";
printf "  Radical series dims:";
for i in [1..#rad_series] do
    printf " %o", Dimension(rad_series[i]);
end for;
printf "\n";

UnsetOutputFile();
quit;
