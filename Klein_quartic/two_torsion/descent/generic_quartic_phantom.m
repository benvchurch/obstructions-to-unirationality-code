// Task 4: Construct quartic WITH phantom 2-torsion from quadric decomposition
//
// Construction: f = Q1*Q3 - Q2^2 where Q1, Q3 conjugate over K = Q(sqrt(-3))
//
// Write Q1 = A + w*B, Q3 = A - w*B (w = sqrt(-3)), Q2 over Q.
// Then f = A^2 + 3*B^2 - Q2^2.
//
// The class eta = [(1/2)div(q1)] in J[2] is Galois-invariant (since q1*q3 = q2^2
// on C implies q1/q3 = (q1/q2)^2, so sigma(eta) = eta always).
// If decomposition doesn't exist over Q, eta is NOT in V_rat.
//
// Candidate: A = 2x^2+y^2+z^2, B = xy, Q2 = x^2+yz
// f = (2x^2+y^2+z^2)^2 + 3(xy)^2 - (x^2+yz)^2
//   = 3x^4 + 7x^2y^2 + y^4 - 2x^2yz + 4x^2z^2 + y^2z^2 + z^4

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);

// Test several (A, B, Q2) triples
// Construction: f = A^2 + 3*B^2 - Q2^2

candidates := [];

// Candidate 1: A=2x^2+y^2+z^2, B=xy, Q2=x^2+yz
A := 2*x^2+y^2+z^2; B := x*y; Q2 := x^2+y*z;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 2: A=2x^2+y^2+z^2, B=xz, Q2=x^2+yz
A := 2*x^2+y^2+z^2; B := x*z; Q2 := x^2+y*z;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 3: A=x^2+2y^2+z^2, B=xy, Q2=y^2+xz
A := x^2+2*y^2+z^2; B := x*y; Q2 := y^2+x*z;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 4: A=2x^2+y^2+z^2, B=xy+xz, Q2=x^2+yz
A := 2*x^2+y^2+z^2; B := x*y+x*z; Q2 := x^2+y*z;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 5: A=x^2+y^2+2z^2, B=yz, Q2=z^2+xy
A := x^2+y^2+2*z^2; B := y*z; Q2 := z^2+x*y;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 6: larger A, asymmetric B
A := 3*x^2+y^2+z^2; B := x*y; Q2 := x^2+y*z;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 7: different Q2
A := 2*x^2+y^2+z^2; B := x*y; Q2 := x^2+y^2;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

// Candidate 8: cross terms in A too
A := 2*x^2+y^2+z^2+x*z; B := x*y; Q2 := x^2+y*z;
Append(~candidates, <A, B, Q2, A^2+3*B^2-Q2^2>);

printf "=== Testing quartics from quadric decompositions over Q(sqrt(-3)) ===\n\n";

for idx := 1 to #candidates do
    f := candidates[idx][4];

    // Smoothness
    P2<X,Y,Z> := ProjectiveSpace(Q, 2);
    C := Curve(P2, Evaluate(f, [X,Y,Z]));
    if not IsNonsingular(C) then
        printf "#%o: SINGULAR\n", idx;
        continue;
    end if;
    g := Genus(C);
    if g ne 3 then
        printf "#%o: genus %o (not 3)\n", idx, g;
        continue;
    end if;

    // Positive definiteness
    R := RealField(15);
    pi := Pi(R);
    min_val := R!100;
    N := 60;
    posdef := true;
    for i := 0 to N do
        phi := pi*R!i/R!N;
        sp := Sin(phi); cp := Cos(phi);
        for j := 0 to 2*N-1 do
            theta := 2*pi*R!j/(2*R!N);
            xv := sp*Cos(theta); yv := sp*Sin(theta); zv := cp;
            val := Evaluate(f, [xv,yv,zv]);
            if val lt min_val then min_val := val; end if;
            if val le 0 then posdef := false; break; end if;
        end for;
        if not posdef then break; end if;
    end for;
    if not posdef then
        printf "#%o: NOT positive definite (min=%o)\n", idx, min_val;
        continue;
    end if;

    printf "#%o: smooth, genus 3, pos def (min=%o)\n", idx, min_val;
    printf "  A=%o, B=%o, Q2=%o\n", candidates[idx][1], candidates[idx][2], candidates[idx][3];
    printf "  f = %o\n", f;

    // Aut check
    aut_one := true;
    for p in [7, 13, 29, 37] do
        P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
        fp := Evaluate(f, [xp,yp,zp]);
        Cp := Curve(P2p, fp);
        if not IsNonsingular(Cp) then
            printf "  p=%o: bad red\n", p;
            continue;
        end if;
        Ap := AutomorphismGroup(Cp);
        printf "  p=%o: |Aut|=%o\n", p, #Ap;
        if #Ap ne 1 then aut_one := false; end if;
    end for;

    // L-polynomial: check #J(F_p) always even
    printf "  L-poly data:\n";
    all_even := true;
    for p in [5,7,11,13,17,19,23,29,31] do
        P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
        fp := Evaluate(f, [xp,yp,zp]);
        Cp := Curve(P2p, fp);
        if not IsNonsingular(Cp) then continue; end if;
        n1 := #RationalPoints(Cp);
        Cp2 := BaseChange(Cp, GF(p^2));
        n2 := #RationalPoints(Cp2);
        Cp3 := BaseChange(Cp, GF(p^3));
        n3 := #RationalPoints(Cp3);
        a1 := p+1-n1;
        a2 := (a1^2-(p^2+1-n2)) div 2;
        a3 := (a1^3-3*a1*a2-(p^3+1-n3)) div 3;
        Jp := 1+a1+a2+a3+p*a2+p^2*a1+p^3;
        v2 := Valuation(Jp, 2);
        printf "    p=%o: #J=%o, v2=%o\n", p, Jp, v2;
        if v2 eq 0 then all_even := false; end if;
    end for;

    if aut_one and all_even then
        printf "  *** PROMISING: Aut=1, #J always even ***\n";
    elif all_even then
        printf "  #J always even but Aut != 1\n";
    elif aut_one then
        printf "  Aut=1 but J[2](Q) = 0\n";
    end if;
    printf "\n";
end for;

printf "Done.\n";
quit;
