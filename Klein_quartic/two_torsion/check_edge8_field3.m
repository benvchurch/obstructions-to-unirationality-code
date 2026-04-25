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

// 2-isogeny from E1
E1p := MinimalModel(IsogenyFromKernel(E1, PQ![-1862, 1]));

printf "E1': %o\n", aInvariants(E1p);
printf "E2:  %o\n", aInvariants(E2);
printf "j(E1') = %o, j(E2) = %o\n", jInvariant(E1p), jInvariant(E2);

// Find twist: use c-invariants
c4_1, c6_1 := Explode(cInvariants(E1p));
c4_2, c6_2 := Explode(cInvariants(E2));
printf "\nc4(E1') = %o, c6(E1') = %o\n", c4_1, c6_1;
printf "c4(E2)  = %o, c6(E2)  = %o\n", c4_2, c6_2;

// For twist by u: c4' = u^4 * c4, c6' = u^6 * c6
// So u^4 = c4_2/c4_1, u^6 = c6_2/c6_1
// => u^2 = (c6_2/c6_1) / (c4_2/c4_1) = c6_2 * c4_1 / (c6_1 * c4_2)
u2 := (c6_2 * c4_1) / (c6_1 * c4_2);
printf "\nu^2 = %o\n", u2;
printf "Factored num: %o\n", Factorization(Abs(Numerator(u2)));
printf "Factored den: %o\n", Factorization(Denominator(u2));

// d = squarefree part of u^2 (the twist discriminant)
n := Numerator(u2);
d_val := Denominator(u2);
printf "\nu^2 = %o/%o\n", n, d_val;

// Verify: twist E1p by the value and check
// u^2 should be rational, and d = squarefree_part(u^2)
// QuadraticTwist(E, d) where d is the squarefree part
function SquarefreePart(n)
    if n eq 0 then return 0; end if;
    sign := n gt 0 select 1 else -1;
    n := Abs(n);
    fac := Factorization(n);
    sfp := 1;
    for f in fac do
        if f[2] mod 2 eq 1 then sfp *:= f[1]; end if;
    end for;
    return sign * sfp;
end function;

sfp := SquarefreePart(Numerator(u2)) * SquarefreePart(Denominator(u2));
// Actually for a/b, sqfree part is sqfree(a*b) up to sign
sfp2 := SquarefreePart(Numerator(u2) * Denominator(u2));
printf "Squarefree part of u^2: %o or %o\n", sfp, sfp2;

// Try twisting by sfp
Et := QuadraticTwist(E1p, sfp2);
Et := MinimalModel(Et);
printf "\ntwist(E1', %o): %o\n", sfp2, aInvariants(Et);
printf "  j = %o, cond = %o\n", jInvariant(Et), Factorization(Conductor(Et));
printf "  same as E2? %o\n", aInvariants(Et) eq aInvariants(E2);
printf "  isogenous to E2? %o\n", IsIsogenous(Et, E2);

// Try negative
Et2 := QuadraticTwist(E1p, -sfp2);
Et2 := MinimalModel(Et2);
printf "\ntwist(E1', %o): %o\n", -sfp2, aInvariants(Et2);
printf "  j = %o, cond = %o\n", jInvariant(Et2), Factorization(Conductor(Et2));
printf "  same as E2? %o\n", aInvariants(Et2) eq aInvariants(E2);
printf "  isogenous to E2? %o\n", IsIsogenous(Et2, E2);

// Also: maybe E1' and E2 are actually isomorphic over Q?
printf "\nIsomorphic E1' ~ E2? %o\n", IsIsomorphic(E1p, E2);

// Check: is QuadraticTwist doing what we think?
printf "\n=== Brute force twist search (wider range) ===\n";
for d in [-1000..1000] do
    if d eq 0 then continue; end if;
    if not IsSquarefree(d) then continue; end if;
    Et := MinimalModel(QuadraticTwist(E1p, d));
    if IsIsomorphic(Et, E2) then
        printf "  E2 = twist(E1', %o) [isomorphic]\n", d;
    end if;
end for;
printf "Brute force done.\n";

// Maybe try IsQuadraticTwist
printf "\n=== IsQuadraticTwist test ===\n";
is_tw, d_tw := IsQuadraticTwist(E1p, E2);
printf "IsQuadraticTwist(E1', E2) = %o", is_tw;
if is_tw then printf ", d = %o\n", d_tw; else printf "\n"; end if;

printf "\nDone.\n";
quit;
