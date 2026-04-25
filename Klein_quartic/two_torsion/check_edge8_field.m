// Determine the field over which the 2-isogeny between
// j1 = -11664/625 and j2 = 3538944/25 is defined.

QQ := Rationals();
PQ<x> := PolynomialRing(QQ);

j1 := -11664/625;
j2 := 3538944/25;

function CurveFromJ(j)
    c := j / (j - 1728);
    return EllipticCurve([QQ| -27*c, -54*c]);
end function;

E1 := MinimalModel(CurveFromJ(j1));
E2 := MinimalModel(CurveFromJ(j2));

printf "E1 (j=%o): %o\n  cond = %o\n", j1, aInvariants(E1), Factorization(Conductor(E1));
printf "E2 (j=%o): %o\n  cond = %o\n", j2, aInvariants(E2), Factorization(Conductor(E2));

// 2-division polynomials
f1 := DivisionPolynomial(E1, 2);
f2 := DivisionPolynomial(E2, 2);
printf "\nE1 2-div poly factors: %o\n", Factorization(f1);
printf "E2 2-div poly factors: %o\n", Factorization(f2);

// Build all 2-isogenous curves to E1 over Q via rational 2-torsion
printf "\n=== 2-isogenous curves to E1 (rational kernel) ===\n";
for fac in Factorization(f1) do
    if Degree(fac[1]) ne 1 then continue; end if;
    xP := -Coefficient(fac[1], 0);
    ker := PQ![xP, 1]; // IsogenyFromKernel wants monic poly (x - xP) but as list
    // Use Velu's formula directly: for 2-isogeny with kernel (xP, 0),
    // the isogenous curve has a4' = a4 - 5*(3*xP^2 + 2*a2*xP + a4_orig)...
    // Actually just use IsogenyFromKernel properly
    Ep := IsogenyFromKernel(E1, PQ![-xP, 1]);
    Ep := MinimalModel(Ep);
    printf "  kernel x=%o => j = %o, cond = %o\n", xP, jInvariant(Ep), Factorization(Conductor(Ep));

    // Check if Ep is isogenous to E2 over Q
    if IsIsogenous(Ep, E2) then
        printf "  *** ISOGENOUS to E2 over Q! ***\n";
    end if;

    // Check if any twist of Ep is isogenous to E2
    for d in [-200..200] do
        if d eq 0 then continue; end if;
        if not IsSquarefree(d) then continue; end if;
        Et := QuadraticTwist(Ep, d);
        if IsIsogenous(Et, E2) then
            printf "  *** twist(Ep, %o) ~ E2 => 2-isogeny over Q(sqrt(%o)) ***\n", d, d;
        end if;
    end for;
end for;

// Same for E2
printf "\n=== 2-isogenous curves to E2 (rational kernel) ===\n";
for fac in Factorization(f2) do
    if Degree(fac[1]) ne 1 then continue; end if;
    xP := -Coefficient(fac[1], 0);
    Ep := IsogenyFromKernel(E2, PQ![-xP, 1]);
    Ep := MinimalModel(Ep);
    printf "  kernel x=%o => j = %o, cond = %o\n", xP, jInvariant(Ep), Factorization(Conductor(Ep));
    if IsIsogenous(Ep, E1) then
        printf "  *** ISOGENOUS to E1 over Q! ***\n";
    end if;
    for d in [-200..200] do
        if d eq 0 then continue; end if;
        if not IsSquarefree(d) then continue; end if;
        Et := QuadraticTwist(E1, d);
        if IsIsogenous(Et, Ep) then
            printf "  *** twist(E1, %o) ~ Ep => related over Q(sqrt(%o)) ***\n", d, d;
        end if;
    end for;
end for;

// Direct approach: compute a_p sign pattern and match Kronecker
printf "\n=== a_p sign pattern (E1 vs E2) ===\n";
signs := [];
non_twist := 0;
for p in PrimesInInterval(2, 500) do
    if Conductor(E1) mod p eq 0 or Conductor(E2) mod p eq 0 then continue; end if;
    a1 := TraceOfFrobenius(E1, p);
    a2 := TraceOfFrobenius(E2, p);
    if a1 eq 0 and a2 eq 0 then continue; end if;
    if a1 eq 0 or a2 eq 0 then
        if a1 ne a2 then non_twist +:= 1; end if;
        continue;
    end if;
    if Abs(a1) ne Abs(a2) then
        non_twist +:= 1;
        continue;
    end if;
    sgn := a2 div a1;
    Append(~signs, <p, sgn>);
end for;
printf "Sign data points: %o, non-twist mismatches: %o\n", #signs, non_twist;

if non_twist gt 0 then
    printf "E1 and E2 are NOT twists of each other.\n";
    printf "But they may be twist-isogenous (twist composed with isogeny).\n";

    // For each 2-isogenous E1' of E1, check twist relation with E2
    printf "\n=== Twist-isogeny: for each E1' 2-isogenous to E1, compare a_p with E2 ===\n";
    for fac in Factorization(f1) do
        if Degree(fac[1]) ne 1 then continue; end if;
        xP := -Coefficient(fac[1], 0);
        Ep := MinimalModel(IsogenyFromKernel(E1, PQ![-xP, 1]));
        printf "\nE1' (j=%o):\n", jInvariant(Ep);

        signs_ep := [];
        non_tw_ep := 0;
        for p in PrimesInInterval(2, 500) do
            if Conductor(Ep) mod p eq 0 or Conductor(E2) mod p eq 0 then continue; end if;
            ap1 := TraceOfFrobenius(Ep, p);
            ap2 := TraceOfFrobenius(E2, p);
            if ap1 eq 0 and ap2 eq 0 then continue; end if;
            if ap1 eq 0 or ap2 eq 0 then
                if ap1 ne ap2 then non_tw_ep +:= 1; end if;
                continue;
            end if;
            if Abs(ap1) ne Abs(ap2) then
                non_tw_ep +:= 1;
                continue;
            end if;
            Append(~signs_ep, <p, ap2 div ap1>);
        end for;
        printf "  Sign data: %o points, %o non-twist mismatches\n", #signs_ep, non_tw_ep;

        if non_tw_ep eq 0 and #signs_ep gt 5 then
            // Match Kronecker
            for d in [-500..500] do
                if d eq 0 then continue; end if;
                if not IsSquarefree(d) then continue; end if;
                match := true;
                for s in signs_ep do
                    if KroneckerSymbol(d, s[1]) ne s[2] then
                        match := false; break;
                    end if;
                end for;
                if match then
                    printf "  d = %o: Kronecker match => E2 = twist(E1', %o)\n", d, d;
                    printf "  => 2-isogeny E1 -> E2 defined over Q(sqrt(%o))\n", d;
                end if;
            end for;
        end if;
    end for;
end if;

// Conductors
printf "\nCond(E1) = %o\n", Factorization(Conductor(E1));
printf "Cond(E2) = %o\n", Factorization(Conductor(E2));

printf "\nDone.\n";
quit;
