// Verify candidate #8: f = 3x^4+4x^3z+7x^2y^2-2x^2yz+5x^2z^2+2xy^2z+2xz^3+y^4+y^2z^2+z^4
// From A=2x^2+xz+y^2+z^2, B=xy, Q2=x^2+yz

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);
f := 3*x^4 + 4*x^3*z + 7*x^2*y^2 - 2*x^2*y*z + 5*x^2*z^2 + 2*x*y^2*z + 2*x*z^3 + y^4 + y^2*z^2 + z^4;

// === L-polynomial and #J(F_p) ===
printf "L-polynomial data:\n";
all_even := true;
min_v2 := 100;
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "  p=%o: bad reduction\n", p;
        continue;
    end if;

    n1 := #RationalPoints(Cp);
    Cp2 := BaseChange(Cp, GF(p^2));
    n2 := #RationalPoints(Cp2);
    Cp3 := BaseChange(Cp, GF(p^3));
    n3 := #RationalPoints(Cp3);

    a1 := p + 1 - n1;
    a2 := (a1^2 - (p^2 + 1 - n2)) div 2;
    a3 := (a1^3 - 3*a1*a2 - (p^3 + 1 - n3)) div 3;
    Jp := 1 + a1 + a2 + a3 + p*a2 + p^2*a1 + p^3;
    v2 := Valuation(Jp, 2);
    printf "  p=%o: #C=%o, L=[1,%o,%o,%o], #J=%o, v2=%o\n",
        p, n1, a1, a2, a3, Jp, v2;
    if v2 eq 0 then all_even := false; end if;
    if v2 lt min_v2 then min_v2 := v2; end if;
end for;
printf "All #J even: %o, min v2 = %o\n\n", all_even, min_v2;

// === Bitangent search ===
printf "Searching for rational bitangent lines (|coeff| <= 5):\n";
bt_count := 0;
Qu<u> := PolynomialRing(Q);
bound := 5;
for a := -bound to bound do
for b := -bound to bound do
for c := -bound to bound do
    if a eq 0 and b eq 0 and c eq 0 then continue; end if;
    first := 0;
    if a ne 0 then first := a; elif b ne 0 then first := b; else first := c; end if;
    if first lt 0 then continue; end if;
    g := GCD(GCD(Abs(a), Abs(b)), Abs(c));
    if g ne 1 then continue; end if;

    if c ne 0 then
        fu := Evaluate(f, [u, Qu!1, Qu!(Q!(-a)/Q!(c))*u + Qu!(Q!(-b)/Q!(c))]);
    elif b ne 0 then
        fu := Evaluate(f, [u, Qu!(Q!(-a)/Q!(b))*u + Qu!(Q!(-c)/Q!(b)), Qu!1]);
    else
        fu := Evaluate(f, [Qu!(Q!(-b)/Q!(a)) + Qu!(Q!(-c)/Q!(a))*u, u, Qu!1]);
    end if;

    if Degree(fu) ne 4 then continue; end if;

    disc := Discriminant(fu);
    if disc eq 0 then
        gf := GCD(fu, Derivative(fu));
        if Degree(gf) eq 2 then
            bt_count +:= 1;
            printf "  Bitangent: %o*X + %o*Y + %o*Z = 0\n", a, b, c;
            printf "    f|_line = %o\n", fu;
        end if;
    end if;
end for; end for; end for;
printf "Total bitangents found: %o\n\n", bt_count;

printf "Done.\n";
quit;
