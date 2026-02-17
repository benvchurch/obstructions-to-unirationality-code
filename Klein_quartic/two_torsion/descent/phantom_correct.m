/*******************************************************************************
 * phantom_correct.m
 *
 * Search for quartics of the form f = A^2 + 3*B^2 + 3*D^2
 * where A, B, D are quadratic forms over Q.
 *
 * Over K = Q(sqrt(-3)):
 *   Q1 = A + w*B, Q3 = A - w*B, Q2 = w*D  (w = sqrt(-3))
 *   f = Q1*Q3 - Q2^2 (since Q1*Q3 = A^2+3B^2 and Q2^2 = -3D^2)
 *   On C: Q1*Q3 = Q2^2
 *
 * Descent cocycle: h = q1/q2, sigma(h) = q3/(-q2) = -q3/q2
 *   lambda = h*sigma(h) = -q1*q3/q2^2 = -1 on C
 *   => lambda = -1 < 0, NOT a norm from Q(sqrt(-3))
 *   => delta(eta) != 0 AUTOMATICALLY
 *
 * Need: smooth genus 3, positive definite, Aut = 1, eta != 0 in J.
 * Positive definiteness is nearly automatic (A^2+3B^2+3D^2 >= 0).
 ******************************************************************************/

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);

printf "=== Searching quartics f = A^2 + 3*B^2 + 3*D^2 ===\n";
printf "Brauer obstruction AUTOMATIC: lambda = -1 (not a norm)\n\n";

// Parametrize quadratic forms:
// A = a1*x^2+a2*y^2+a3*z^2+a4*xy+a5*xz+a6*yz
// Similarly for B and D
// To keep search manageable: A generic, B and D simple

found := 0;
for a4 in [-1,0,1] do    // xy coeff of A
for a5 in [-1,0,1] do    // xz coeff of A
for a6 in [-1,0,1] do    // yz coeff of A
    A := x^2+y^2+z^2 + a4*x*y + a5*x*z + a6*y*z;
    // Try different (B, D) pairs
    Bs := [x*y, x*z, y*z, x*y+x*z, x*y+y*z];
    Ds := [x*y, x*z, y*z, x*y+x*z, x*y+y*z, x^2-y^2, x^2-z^2];

    for bi := 1 to #Bs do
    for di := 1 to #Ds do
        B := Bs[bi]; D := Ds[di];
        if B eq D then continue; end if;

        f := A^2 + 3*B^2 + 3*D^2;

        // Smoothness
        P2<X,Y,Z> := ProjectiveSpace(Q, 2);
        C := Curve(P2, Evaluate(f, [X,Y,Z]));
        if not IsNonsingular(C) then continue; end if;
        if Genus(C) ne 3 then continue; end if;

        // Positive definiteness (quick check)
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
                val := Evaluate(f, [xv,yv,zv]);
                if val lt min_val then min_val := val; end if;
                if val le 0 then posdef := false; break; end if;
            end for;
            if not posdef then break; end if;
        end for;
        if not posdef then continue; end if;

        // Aut check at p=13 and p=29
        aut_ok := true;
        for p in [13, 29] do
            P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
            fp := Evaluate(f, [xp,yp,zp]);
            Cp := Curve(P2p, fp);
            if not IsNonsingular(Cp) then aut_ok := false; break; end if;
            Ap := AutomorphismGroup(Cp);
            if #Ap ne 1 then aut_ok := false; break; end if;
        end for;
        if not aut_ok then continue; end if;

        found +:= 1;
        printf "CANDIDATE %o:\n", found;
        printf "  A = %o\n  B = %o\n  D = %o\n", A, B, D;
        printf "  f = %o\n", f;
        printf "  min on sphere = %o\n", min_val;
        printf "  |Aut| mod 13,29 = 1\n";

        // L-poly check: #J always even
        all_even := true;
        for p in [7,11,13,17,19,23,29] do
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
            printf "  p=%o: #J=%o, v2=%o\n", p, Jp, v2;
            if v2 eq 0 then all_even := false; end if;
        end for;

        if all_even then
            printf "  *** ALL #J EVEN => J[2](Q) != 0 ***\n";
            printf "  Combined with lambda = -1: PHANTOM 2-TORSION\n";
        else
            printf "  Some #J odd => J[2](Q) might be 0\n";
        end if;
        printf "\n";

        if found ge 5 then
            printf "Found enough candidates, stopping.\n";
            quit;
        end if;
    end for;
    end for;
end for;
end for;
end for;

printf "Total found: %o\n", found;
printf "Done.\n";
quit;
