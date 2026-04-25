/*
 * bitangent_orbits.m
 *
 * Compute the orbit decomposition of Aut(C) ≅ PSL(2,7) on the 28 bitangent
 * lines of the Klein quartic twist, working over F_29.
 */

SetColumns(0);

Fq := GF(29);
P2<x,y,z> := ProjectiveSpace(Fq, 2);
F := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
     - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
C := Curve(P2, F);

// --- Find 28 bitangents over F_29 ---

function FindBitangents(F, Fq)
    P2 := Parent(F);
    x := P2.1; y := P2.2; z := P2.3;
    bits := [];
    Pt<t> := PolynomialRing(Fq);

    for a in Fq do
        for b in Fq do
            f_line := Evaluate(F, [t, 1, a*t + b]);
            if Degree(f_line) lt 0 or f_line eq 0 then continue; end if;
            lc := LeadingCoefficient(f_line);
            is_sq, _ := IsSquare(f_line / lc);
            if is_sq then
                Append(~bits, [Fq | -a, -b, 1]);
            end if;
        end for;
    end for;

    for c in Fq do
        f_line := Evaluate(F, [1, c, t]);
        if Degree(f_line) lt 0 or f_line eq 0 then continue; end if;
        lc := LeadingCoefficient(f_line);
        is_sq, _ := IsSquare(f_line / lc);
        if is_sq then
            Append(~bits, [Fq | c, -1, 0]);
        end if;
    end for;

    f_line := Evaluate(F, [0, 1, t]);
    if Degree(f_line) ge 0 and f_line ne 0 then
        lc := LeadingCoefficient(f_line);
        is_sq, _ := IsSquare(f_line / lc);
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

printf "Finding bitangents of Klein twist over F_29...\n";
bits := FindBitangents(F, Fq);
printf "Found %o bitangents.\n", #bits;
assert #bits eq 28;

// --- Automorphism group and permutation action on bitangents ---

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
                found := j; break;
            end if;
        end for;
        if found eq 0 then error "image not found"; end if;
        Append(~perm, found);
    end for;
    return perm;
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
    if #Pin lt 4 then error "too few points"; end if;
    return PGL3FromImages(Pin, Pout, Fq);
end function;

printf "Computing Aut(C)...\n";
auts := Automorphisms(C);
printf "|Aut(C / F_29)| = %o\n", #auts;

printf "Computing F_29-rational points...\n";
Cpts := [];
for pt in Points(C) do
    v := Eltseq(pt);
    if &and[IsCoercible(Fq, c) : c in v] then
        Append(~Cpts, [Fq | c : c in v]);
    end if;
end for;
printf "%o rational points.\n", #Cpts;

printf "Building permutation action on 28 bitangents...\n";
perm_elts := [];
for g in auts do
    M := AutToMatrix(g, Cpts, Fq);
    p := LinePermutation(M, bits);
    Append(~perm_elts, Sym(28) ! p);
end for;

G := sub<Sym(28) | perm_elts>;
printf "Permutation group on 28 points: order %o, name %o\n", #G, GroupName(G);

// --- Orbit decomposition ---
orbs := Orbits(G);
printf "\n%o orbits on the 28 bitangents:\n", #orbs;
Sort(~orbs, func<a,b | #a - #b>);
for i in [1..#orbs] do
    rep := Representative(orbs[i]);
    stab := Stabiliser(G, rep);
    printf "  Orbit %o: size %o, stabiliser order %o (%o), representative = bitangent #%o\n",
        i, #orbs[i], #stab, GroupName(stab), rep;
    printf "    line coeffs [a,b,c] (ax+by+cz=0): %o\n", bits[rep];
end for;

// Print all bitangent lines for reference
printf "\nAll 28 bitangent lines [a,b,c] (ax+by+cz=0):\n";
for i in [1..28] do
    printf "  #%o: %o\n", i, bits[i];
end for;

quit;
