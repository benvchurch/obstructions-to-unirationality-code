// Phase 4: Bitangent line search for Aut=1 candidates
// Candidates from previous run:
// #5: x^4+x^3*y+3*x^2*y^2+x^2*y*z+3*x^2*z^2+y^4+3*y^2*z^2+y*z^3+z^4
// #6: x^4+x^3*y+3*x^2*y^2+4*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4
// #7: x^4+2*x^3*y+5*x^2*y^2+x^2*y*z+5*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4

Q := Rationals();
Qu<u> := PolynomialRing(Q);

// Define candidates as functions that evaluate at (x,y,z) in Qu
// #5: f = x^4+x^3*y+3*x^2*y^2+x^2*y*z+3*x^2*z^2+y^4+3*y^2*z^2+y*z^3+z^4
f5 := func< x, y, z | x^4+x^3*y+3*x^2*y^2+x^2*y*z+3*x^2*z^2+y^4+3*y^2*z^2+y*z^3+z^4 >;
// #6
f6 := func< x, y, z | x^4+x^3*y+3*x^2*y^2+4*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4 >;
// #7
f7 := func< x, y, z | x^4+2*x^3*y+5*x^2*y^2+x^2*y*z+5*x^2*z^2+y^4+5*y^2*z^2+y*z^3+z^4 >;

cands := [<5, f5>, <6, f6>, <7, f7>];

for ci := 1 to #cands do
    idx := cands[ci][1];
    f := cands[ci][2];
    printf "=== Candidate #%o ===\n", idx;
    n_bt := 0;
    bound := 5;
    for a in [-bound..bound] do
    for b in [-bound..bound] do
    for c in [-bound..bound] do
        if a eq 0 and b eq 0 and c eq 0 then continue; end if;
        // Normalize: first nonzero positive
        first := 0;
        if a ne 0 then first := a; elif b ne 0 then first := b; else first := c; end if;
        if first lt 0 then continue; end if;
        g := GCD(GCD(Abs(a), Abs(b)), Abs(c));
        if g gt 1 then continue; end if;

        // Line: a*x + b*y + c*z = 0
        // Substitute to get univariate poly in u
        // Clear denominators: (x,y,z) = (c*u, c, -(a*u+b)) if c!=0
        //                     (x,y,z) = (b*u, -a*u, b) if c=0, b!=0 -- wait
        // Actually: if c!=0, solve z=-(ax+by)/c. Set x=u, y=1 => z=-(au+b)/c
        // To avoid fractions, set x=c*u, y=c, z=-(a*u+b). Then f scales by c^4.
        if c ne 0 then
            Fu := f(Qu!(c*u), Qu!c, Qu!(-(a*u+b)));
        elif b ne 0 then
            // Line: ax+by=0 => y=-ax/b. Set x=b*u, y=-a*u, z=1
            // Then line: a*b*u + b*(-a*u) = 0. OK.
            // To keep z free: set x=b*u, y=-a*u, z=b
            Fu := f(Qu!(b*u), Qu!(-a*u), Qu!b);
        else
            // a*x = 0 => x = 0. Set y=u, z=1
            Fu := f(Qu!0, u, Qu!1);
        end if;

        if Degree(Fu) lt 2 then continue; end if;

        // Check if Fu is a perfect square
        G := GCD(Fu, Derivative(Fu));
        if Degree(G) eq 2 and Degree(Fu) eq 4 then
            lc_ratio := LeadingCoefficient(Fu) / LeadingCoefficient(G)^2;
            if Fu eq lc_ratio * G^2 then
                n_bt +:= 1;
                printf "  BITANGENT: %o*x+%o*y+%o*z=0\n", a, b, c;
                printf "    F|_l = %o * (%o)^2\n", lc_ratio, G;
            end if;
        end if;
    end for;
    end for;
    end for;
    printf "  Total bitangents (|coeff|<=%o): %o\n\n", bound, n_bt;
end for;

printf "Done.\n";
quit;
