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
// 2-isogeny from E2
E2p := MinimalModel(IsogenyFromKernel(E2, PQ![2499, 1]));

printf "E1:  j=%o, cond=%o, ainvs=%o\n", jInvariant(E1), Factorization(Conductor(E1)), aInvariants(E1);
printf "E1': j=%o, cond=%o, ainvs=%o\n", jInvariant(E1p), Factorization(Conductor(E1p)), aInvariants(E1p);
printf "E2:  j=%o, cond=%o, ainvs=%o\n", jInvariant(E2), Factorization(Conductor(E2)), aInvariants(E2);
printf "E2': j=%o, cond=%o, ainvs=%o\n", jInvariant(E2p), Factorization(Conductor(E2p)), aInvariants(E2p);

printf "\nE1' isogenous to E2 over Q? %o\n", IsIsogenous(E1p, E2);
printf "E2' isogenous to E1 over Q? %o\n", IsIsogenous(E2p, E1);

// E1' has same j as E2 but different conductor => they are twists
// Find the twist
printf "\n=== Finding twist d: E2 = twist(E1', d) ===\n";
for d in [-500..500] do
    if d eq 0 then continue; end if;
    if not IsSquarefree(d) then continue; end if;
    Et := QuadraticTwist(E1p, d);
    Et := MinimalModel(Et);
    if aInvariants(Et) eq aInvariants(E2) then
        printf "  E2 = twist(E1', %o) [exact model match]\n", d;
    end if;
    if IsIsogenous(Et, E2) then
        printf "  twist(E1', %o) ~ E2 over Q\n", d;
    end if;
end for;

// a_p comparison: E1' vs E2
printf "\n=== a_p: E1' vs E2 ===\n";
signs := [];
for p in PrimesInInterval(2, 300) do
    if Conductor(E1p) mod p eq 0 or Conductor(E2) mod p eq 0 then continue; end if;
    a1 := TraceOfFrobenius(E1p, p);
    a2 := TraceOfFrobenius(E2, p);
    if a1 eq 0 then continue; end if;
    printf "%4o | %6o | %6o | %o\n", p, a1, a2, a1 eq a2 select "=" else (a1 eq -a2 select "-" else "?");
    if Abs(a1) eq Abs(a2) and a1 ne 0 then
        Append(~signs, <p, a2 div a1>);
    end if;
end for;

// Match Kronecker symbol
printf "\n=== Kronecker match ===\n";
for d in [-500..500] do
    if d eq 0 then continue; end if;
    if not IsSquarefree(d) then continue; end if;
    match := true;
    for s in signs do
        if KroneckerSymbol(d, s[1]) ne s[2] then
            match := false; break;
        end if;
    end for;
    if match then
        printf "  d = %o matches => E2 is twist of E1' by %o\n", d, d;
        printf "  => the 2-isogeny E1 -> E2 is defined over Q(sqrt(%o))\n", d;
    end if;
end for;

printf "\nDone.\n";
quit;
