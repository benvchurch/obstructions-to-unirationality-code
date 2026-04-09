/*******************************************************************************
 * quadric_rational.m
 *
 * Search for Q-rational quadric decompositions of X^4+Y^4+Z^4 = Q1*Q3 - Q2^2.
 * For each Q2 with integer coefficients in [-5,5], check if F+Q2^2 factors
 * as a product of two quadratic forms over Q.
 ******************************************************************************/

R<X,Y,Z> := PolynomialRing(Rationals(), 3);
Ff := X^4 + Y^4 + Z^4;

count := 0;
found := 0;

for a in [-5..5] do for b in [-5..5] do for c in [-5..5] do
for d in [-5..5] do for ef in [-5..5] do for ff_ in [-5..5] do
    Q2 := a*X^2 + b*Y^2 + c*Z^2 + d*X*Y + ef*X*Z + ff_*Y*Z;
    if Q2 eq 0 then continue; end if;
    // Avoid duplicates: Q2 and -Q2 give the same Q2^2
    // Normalize: first nonzero coeff positive
    coeffs := [a,b,c,d,ef,ff_];
    first_nonzero := 0;
    for i in [1..6] do
        if coeffs[i] ne 0 then first_nonzero := coeffs[i]; break; end if;
    end for;
    if first_nonzero lt 0 then continue; end if;

    G := Ff + Q2^2;
    fac := Factorization(G);

    // Check if G factors into two quadratic factors
    degs := [TotalDegree(f[1]) : f in fac];
    has_quad_pair := false;

    if #fac eq 2 and degs[1] eq 2 and degs[2] eq 2
       and fac[1][2] eq 1 and fac[2][2] eq 1 then
        has_quad_pair := true;
        Q1_ := fac[1][1]; Q3_ := fac[2][1];
        // Fix scalar
        scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
        if scalar ne 1 then Q1_ := scalar*Q1_; end if;
    elif #fac eq 1 and degs[1] eq 2 and fac[1][2] eq 2 then
        // G = Q^2, so Q1 = Q3 = Q
        has_quad_pair := true;
        Q1_ := fac[1][1]; Q3_ := fac[1][1];
        scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
        if scalar ne 1 then Q1_ := scalar*Q1_; end if;
    elif #fac ge 2 then
        // Check if we can group factors into two degree-2 groups
        // Handle: 4 linear factors, 2 linear + 1 quadratic, etc.
        if &+[degs[i]*fac[i][2] : i in [1..#fac]] eq 4 then
            // Try all ways to split factors into two groups of total degree 2
            // For simplicity, enumerate small cases
            if #fac eq 4 and &and[degs[i] eq 1 and fac[i][2] eq 1 : i in [1..4]] then
                // 4 linear factors: 3 ways to pair them
                for pair in [[1,2],[1,3],[1,4]] do
                    i1 := pair[1]; i2 := pair[2];
                    rest := [j : j in [1..4] | j ne i1 and j ne i2];
                    Q1_ := fac[i1][1]*fac[i2][1];
                    Q3_ := fac[rest[1]][1]*fac[rest[2]][1];
                    scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
                    if scalar ne 1 then Q1_ := scalar*Q1_; end if;
                    if Q1_*Q3_ - Q2^2 eq Ff then
                        has_quad_pair := true;
                        break;
                    end if;
                end for;
            elif #fac eq 3 then
                // Try grouping
                for i in [1..#fac] do
                    if degs[i]*fac[i][2] eq 2 then
                        Q1_ := fac[i][1]^fac[i][2];
                        others := &*[fac[j][1]^fac[j][2] : j in [1..#fac] | j ne i];
                        if TotalDegree(others) eq 2 then
                            Q3_ := others;
                            scalar := LeadingCoefficient(G) / LeadingCoefficient(Q1_*Q3_);
                            if scalar ne 1 then Q1_ := scalar*Q1_; end if;
                            if Q1_*Q3_ - Q2^2 eq Ff then
                                has_quad_pair := true;
                                break;
                            end if;
                        end if;
                    end if;
                end for;
            end if;
        end if;
    end if;

    count +:= 1;
    if count mod 10000 eq 0 then
        printf "Checked %o Q2 values so far, found %o decompositions\n", count, found;
    end if;

    if has_quad_pair then
        if Q1_*Q3_ - Q2^2 eq Ff then
            found +:= 1;
            printf "FOUND: Q2 = %o\n", Q2;
            printf "  Q1 = %o\n  Q3 = %o\n\n", Q1_, Q3_;
        end if;
    end if;
end for; end for; end for;
end for; end for; end for;

printf "\nTotal Q2 checked: %o\n", count;
printf "Decompositions found: %o\n", found;

if found eq 0 then
    print "";
    print "No Q-rational decompositions found with coefficients in [-5,5].";
    print "This is consistent with a Brauer obstruction on the space of";
    print "quadric decompositions.";
end if;

quit;
