/*******************************************************************************
 * phantom_cocycle_multi.m
 *
 * Compute the descent cocycle lambda for MULTIPLE quadric decomposition candidates.
 * Also check if (1/2)div(q1) is principal (eta = 0 in J) or nontrivial.
 *
 * For each (A, B, Q2) with f = A^2 + 3*B^2 - Q2^2:
 *   q1 = A + w*B, q3 = A - w*B  (w = sqrt(-3))
 *   On C: q1*q3 = q2^2
 ******************************************************************************/

P<a> := PolynomialRing(Rationals());
K<w> := NumberField(a^2 + 3);  // w = sqrt(-3)
Q := Rationals();

sigma := hom<K -> K | -w>;

function SigmaKx(elt, sigma)
    n := Numerator(elt);
    d := Denominator(elt);
    Kpol := Parent(n);
    sigma_n := Kpol ! [sigma(Coefficient(n, i)) : i in [0..Degree(n)]];
    sigma_d := Kpol ! [sigma(Coefficient(d, i)) : i in [0..Degree(d)]];
    return Parent(elt) ! (sigma_n / sigma_d);
end function;

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

// Test candidates: f(x,y,1) in the affine chart z=1
Kx<x> := FunctionField(K);
Poly3<X,Y,Z> := PolynomialRing(Q, 3);

// List of (A, B, Q2) triples (in homogeneous coords)
candidates := [
    // #1: the original candidate #8 from phantom search
    <2*X^2+X*Z+Y^2+Z^2, X*Y, X^2+Y*Z>,
    // #2: different cross term
    <2*X^2+Y*Z+Y^2+Z^2, X*Y, X^2+X*Z>,
    // #3: asymmetric A
    <3*X^2+X*Z+Y^2+Z^2, X*Y, X^2+Y*Z>,
    // #4: different B
    <2*X^2+X*Z+Y^2+Z^2, X*Z, X^2+Y*Z>,
    // #5: larger A coefficient
    <2*X^2+X*Y+Y^2+Z^2, X*Z, X^2+Y*Z>,
    // #6: multiple cross terms
    <2*X^2+X*Z+Y^2+Z^2, X*Y+Y*Z, X^2+Y*Z>,
    // #7: B has two terms
    <X^2+Y^2+2*Z^2+X*Z, Y*Z, X*Y+Z^2>,
    // #8: more variety
    <2*X^2+Y^2+Z^2+Y*Z, X*Y, X^2+X*Z>,
    // #9: asymmetric
    <3*X^2+Y^2+Z^2+X*Y, X*Z, X^2+Y*Z>,
    // #10
    <2*X^2+X*Z+Y^2+Z^2, X*Y, X^2+X*Z+Y*Z>
];

for idx := 1 to #candidates do
    Ah := candidates[idx][1];
    Bh := candidates[idx][2];
    Q2h := candidates[idx][3];
    fh := Ah^2 + 3*Bh^2 - Q2h^2;

    // Quick smoothness check
    P2<Xp,Yp,Zp> := ProjectiveSpace(Q, 2);
    C := Curve(P2, Evaluate(fh, [Xp,Yp,Zp]));
    if not IsNonsingular(C) then
        printf "#%o: SINGULAR\n\n", idx;
        continue;
    end if;
    g := Genus(C);
    if g ne 3 then
        printf "#%o: genus %o\n\n", idx, g;
        continue;
    end if;

    // Quick positive definiteness
    R := RealField(15);
    pi := Pi(R);
    min_val := R!100;
    N := 40;
    posdef := true;
    for i := 0 to N do
        phi := pi*R!i/R!N;
        sp := Sin(phi); cp := Cos(phi);
        for j := 0 to 2*N-1 do
            theta := 2*pi*R!j/(2*R!N);
            xv := sp*Cos(theta); yv := sp*Sin(theta); zv := cp;
            val := Evaluate(fh, [xv,yv,zv]);
            if val lt min_val then min_val := val; end if;
            if val le 0 then posdef := false; break; end if;
        end for;
        if not posdef then break; end if;
    end for;
    if not posdef then
        printf "#%o: NOT pos def (min=%o)\n\n", idx, min_val;
        continue;
    end if;

    // Quick Aut check at p=13
    P2p<xp,yp,zp> := ProjectiveSpace(GF(13), 2);
    fp13 := Evaluate(fh, [xp,yp,zp]);
    Cp := Curve(P2p, fp13);
    if not IsNonsingular(Cp) then
        aut_size := -1;
    else
        aut_size := #AutomorphismGroup(Cp);
    end if;

    printf "#%o: smooth g=3, pos def (min=%o), |Aut| mod 13 = %o\n", idx, min_val, aut_size;

    // Compute cocycle
    // Affine chart z=1
    Af := Evaluate(Ah, [x, K!0, K!1]);  // placeholder, need y
    // Actually need to work in function field of C
    // f(x,y,1) as poly in y
    faffine := Evaluate(fh, [x, K!0, K!1]);  // wrong, need y variable

    // Build f(x,y,1) as polynomial in y over K(x)
    Kxy<y> := PolynomialRing(Kx);
    // Evaluate fh with X=x, Y=y, Z=1
    // Need to manually construct since fh is in Q[X,Y,Z]
    fa := K!0;
    // Extract monomials from fh
    mons := Monomials(fh);
    cofs := Coefficients(fh);
    fpoly := Kxy ! 0;
    for i := 1 to #mons do
        m := mons[i];
        c := cofs[i];
        ex := Degree(m, X);
        ey := Degree(m, Y);
        ez := Degree(m, Z);
        // X^ex * Y^ey * Z^ez -> x^ex * y^ey * 1^ez
        fpoly +:= (K!c) * (Kx!x)^ex * y^ey;
    end for;

    if Degree(fpoly) ne 4 then
        printf "  f(x,y,1) has degree %o in y, skipping\n\n", Degree(fpoly);
        continue;
    end if;

    FF<yy> := FunctionField(fpoly);
    elt_x := FF ! x;
    elt_y := yy;

    // Build q1 = A(x,y,1) + w*B(x,y,1) and q3 = A - w*B, q2 = Q2(x,y,1)
    q1_val := FF ! 0;
    q3_val := FF ! 0;
    q2_val := FF ! 0;
    for i := 1 to #Monomials(Ah) do
        m := Monomials(Ah)[i]; c := Coefficients(Ah)[i];
        ex := Degree(m,X); ey := Degree(m,Y); ez := Degree(m,Z);
        q1_val +:= (K!c) * elt_x^ex * elt_y^ey;
        q3_val +:= (K!c) * elt_x^ex * elt_y^ey;
    end for;
    bval := FF ! 0;
    for i := 1 to #Monomials(Bh) do
        m := Monomials(Bh)[i]; c := Coefficients(Bh)[i];
        ex := Degree(m,X); ey := Degree(m,Y); ez := Degree(m,Z);
        bval +:= (K!c) * elt_x^ex * elt_y^ey;
    end for;
    q1_val +:= w * bval;
    q3_val -:= w * bval;
    for i := 1 to #Monomials(Q2h) do
        m := Monomials(Q2h)[i]; c := Coefficients(Q2h)[i];
        ex := Degree(m,X); ey := Degree(m,Y); ez := Degree(m,Z);
        q2_val +:= (K!c) * elt_x^ex * elt_y^ey;
    end for;

    // Verify q1*q3 = q2^2
    check := q1_val * q3_val eq q2_val^2;
    printf "  q1*q3 = q2^2? %o\n", check;
    if not check then
        printf "  FAILED verification\n\n";
        continue;
    end if;

    // Compute divisors
    D_q1 := Divisor(q1_val);
    D_q3 := Divisor(q3_val);

    ok1, D_half1 := HalfDiv(D_q1);
    ok2, D_half3 := HalfDiv(D_q3);
    printf "  div(q1) all even? %o, div(q3) all even? %o\n", ok1, ok2;

    if not (ok1 and ok2) then
        printf "  Divisors not all even\n\n";
        continue;
    end if;

    // Check if (1/2)div(q1) is principal
    V0, phi0 := RiemannRochSpace(D_half1);
    printf "  dim L((1/2)div(q1)) = %o", Dimension(V0);
    if Dimension(V0) ge 1 then
        printf " => eta = 0 (TRIVIAL)";
    else
        printf " => eta != 0 (NONTRIVIAL)";
    end if;
    printf "\n";

    // Compute cocycle
    ddiff := D_half1 - D_half3;
    V, phi := RiemannRochSpace(-ddiff);
    if Dimension(V) eq 0 then
        printf "  No function found for cocycle\n\n";
        continue;
    end if;

    fn := phi(V.1);
    coeffs_fn := Eltseq(fn);
    sigma_coeffs := [SigmaKx(c, sigma) : c in coeffs_fn];
    sigma_fn := &+[FF ! sigma_coeffs[i] * elt_y^(i-1) : i in [1..#sigma_coeffs]];
    lambda := fn * sigma_fn;
    lambda_coeffs := Eltseq(lambda);

    // Check if constant
    is_const := true;
    for i := 2 to #lambda_coeffs do
        if lambda_coeffs[i] ne 0 then is_const := false; break; end if;
    end for;

    if is_const then
        lam := lambda_coeffs[1];
        printf "  lambda = %o\n", lam;
        if lam in Rationals() then
            lam_q := Rationals() ! lam;
            if lam_q lt 0 then
                printf "  *** PHANTOM: lambda = %o < 0, NOT a norm ***\n", lam_q;
            elif lam_q eq 0 then
                printf "  lambda = 0 (degenerate)\n";
            else
                printf "  lambda = %o > 0, need to check norm\n", lam_q;
                // Check if lam_q = a^2 + 3*b^2 for some a,b in Q
                // Quick: if lam_q is a positive rational, it's a norm iff
                // v_p(lam_q) is even for all p ≡ 2 mod 3
                printf "  (Norm check: positive, so might be a norm)\n";
            end if;
        else
            printf "  lambda in K, not Q — this shouldn't happen\n";
        end if;
    else
        printf "  lambda NOT constant: %o\n", lambda;
    end if;
    printf "\n";

    delete FF;
    delete Kxy;
end for;

printf "Done.\n";
quit;
