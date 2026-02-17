// Check 2-rank of J(C)(F_p) via L-polynomial / point counting
// If #J(F_p) is odd for any good prime, then J[2](Q) = 0.

Q := Rationals();

printf "=== Candidate #5: x^4+x^3*y+3*x^2*y^2+x^2*y*z+3*x^2*z^2+y^4+3*y^2*z^2+y*z^3+z^4 ===\n";
printf "=== Candidate #6: x^4+x^3*y+3*x^2*y^2+4*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4 ===\n";
printf "=== Candidate #7: x^4+2*x^3*y+5*x^2*y^2+x^2*y*z+5*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4 ===\n\n";

for ci := 1 to 3 do
    idx := [5,6,7][ci];
    printf "--- Candidate #%o ---\n", idx;

    for p in [5,7,11,13,17,19,23,29,31,37,41,43,47,53] do
        P2<x,y,z> := ProjectiveSpace(GF(p), 2);
        if ci eq 1 then
            fp := x^4+x^3*y+3*x^2*y^2+x^2*y*z+3*x^2*z^2+y^4+3*y^2*z^2+y*z^3+z^4;
        elif ci eq 2 then
            fp := x^4+x^3*y+3*x^2*y^2+4*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4;
        else
            fp := x^4+2*x^3*y+5*x^2*y^2+x^2*y*z+5*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4;
        end if;
        Cp := Curve(P2, fp);
        if not IsNonsingular(Cp) then
            printf "  p=%o: bad reduction\n", p;
            continue;
        end if;

        // Count points over F_p, F_{p^2}, F_{p^3}
        n1 := #RationalPoints(Cp);
        // For F_{p^2}: base change
        Cp2 := BaseChange(Cp, GF(p^2));
        n2 := #RationalPoints(Cp2);
        // For F_{p^3}
        Cp3 := BaseChange(Cp, GF(p^3));
        n3 := #RationalPoints(Cp3);

        // L-polynomial coefficients
        a1 := p + 1 - n1;
        a2 := (a1^2 - (p^2 + 1 - n2)) div 2;
        a3_num := a1^3 - 3*a1*a2 - (p^3 + 1 - n3);
        a3 := a3_num div 3;

        // #J(F_p) = L(1) = 1 + a1 + a2 + a3 + p*a2 + p^2*a1 + p^3
        Jp := 1 + a1 + a2 + a3 + p*a2 + p^2*a1 + p^3;

        two_val := Valuation(Jp, 2);
        printf "  p=%o: #C(F_p)=%o, #J(F_p)=%o, v_2(#J)=%o\n", p, n1, Jp, two_val;
    end for;
    printf "\n";
end for;

printf "Done.\n";
quit;
