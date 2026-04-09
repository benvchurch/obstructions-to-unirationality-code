/*******************************************************************************
 * check_isogeny2.m - Finer analysis: check within/between j-classes
 * Also identify the elliptic curves via Cremona labels if possible.
 ******************************************************************************/

load "two_torsion/bitangent_data.m";
K := Parent(bitangent_lines[1][1]);
w := K.1;

PQ<v> := PolynomialRing(Rationals());

mp1_Q := v^2 + 13856*v - 26578688;
mp23_Q := v^4 - 103439*v^3 + 6670405329*v^2 + 31128229267744*v + 148381159092130048;

function TraceFromJ(j_val, Fq)
    if j_val eq 0 then
        E := EllipticCurve([Fq| 0, 1]);
        return true, TraceOfFrobenius(E);
    elif j_val eq Fq!1728 then
        E := EllipticCurve([Fq| 1, 0]);
        return true, TraceOfFrobenius(E);
    else
        denom := j_val - Fq!1728;
        if denom eq 0 then return false, 0; end if;
        c := 27*j_val / denom;
        try
            E := EllipticCurve([Fq| -c, -2*c]);
            return true, TraceOfFrobenius(E);
        catch e
            return false, 0;
        end try;
    end if;
end function;

// Check if mp23 factors into two quadratics over Q
fac23 := Factorization(mp23_Q);
printf "mp23 factors over Q: %o\n", [<Degree(f[1]), f[2]> : f in fac23];

// Check: does mp23 factor over Q(sqrt(7))?
Q7<s7> := NumberField(v^2 - 7);
PQ7<u7> := PolynomialRing(Q7);
fac23_Q7 := Factorization(PQ7!mp23_Q);
printf "mp23 factors over Q(sqrt(7)): %o\n", [<Degree(f[1]), f[2]> : f in fac23_Q7];

// Check: does mp23 factor over Q(sqrt(-7))?
Qm7<sm7> := NumberField(v^2 + 7);
PQm7<um7> := PolynomialRing(Qm7);
fac23_Qm7 := Factorization(PQm7!mp23_Q);
printf "mp23 factors over Q(sqrt(-7)): %o\n", [<Degree(f[1]), f[2]> : f in fac23_Qm7];

// The splitting field of mp1 is Q(sqrt(7*3^2*2^14*17^2)) = Q(sqrt(7))
// since disc = 2^14 * 3^2 * 7 * 17^2 and sqrt of that is 2^7*3*17*sqrt(7)
// So j1 in Q(sqrt(7)).

// Construct E over Q(sqrt(7)) with j = j1
Q7<r7> := QuadraticField(7);
j1_val := -6928 + 3264*r7;
j1_conj := -6928 - 3264*r7;

printf "\nj1 = %o\n", j1_val;
printf "j1' = %o\n", j1_conj;

// Construct elliptic curves
c1 := 27*j1_val/(j1_val - 1728);
E1 := EllipticCurve([Q7| -c1, -2*c1]);
c1c := 27*j1_conj/(j1_conj - 1728);
E1c := EllipticCurve([Q7| -c1c, -2*c1c]);

printf "\nE1 (j=%o): %o\n", j1_val, aInvariants(E1);
printf "E1' (j=%o): %o\n", j1_conj, aInvariants(E1c);

// Check isogeny between E1 and E1'
try
    iso, deg := IsIsogenous(E1, E1c);
    printf "E1 isogenous to E1': %o", iso;
    if iso then printf " (degree %o)", deg; end if;
    print "";
catch e
    print "IsIsogenous failed, checking via traces...";
    // Compare traces at split primes
    mismatch := false;
    for p in PrimesInInterval(5, 200) do
        if p eq 7 then continue; end if;
        Fp := GF(p);
        PFp<t> := PolynomialRing(Fp);
        f := PFp!mp1_Q;
        fac := Factorization(f);
        if not &and[Degree(ff[1]) eq 1 : ff in fac] then continue; end if;
        roots := [-Coefficient(ff[1], 0) : ff in fac];
        if #roots lt 2 then continue; end if;
        ok1, a1 := TraceFromJ(roots[1], Fp);
        ok2, a2 := TraceFromJ(roots[2], Fp);
        if not ok1 or not ok2 then continue; end if;
        if a1 ne a2 and a1 ne -a2 then
            printf "  p=%o: a_p = %o vs %o -- DIFFERENT\n", p, a1, a2;
            mismatch := true;
        end if;
    end for;
    if not mismatch then
        print "  All |a_p| match => E1 and E1' are twist-isogenous";
    end if;
end try;

// Now: identify E1 by looking at traces
// E1 over Q(sqrt(7)) -- check a_p for rational primes that split in Q(sqrt(7))
print "\n=== Identifying E1 via L-function ===";
printf "Conductor analysis:\n";

// Try to find a minimal model
try
    E1min := MinimalModel(E1);
    printf "Minimal model E1: %o\n", aInvariants(E1min);
    printf "Conductor: %o\n", Conductor(E1min);
catch e
    print "MinimalModel/Conductor not available over this field";
end try;

// Check if E1 is the base change of a curve over Q
// If so, the traces at split primes (p splits in Q(sqrt(7))) should match
// a rational curve's a_p
print "\n=== Trace data for E1 at various primes ===";
print "Looking for matching rational elliptic curve...";
// Compute a_p for E1 at rational primes splitting in Q(sqrt(7))
// p splits in Q(sqrt(7)) iff (7/p) = 1, i.e., 7 is a square mod p
ap_data := [];
for p in PrimesInInterval(5, 100) do
    if p eq 7 then continue; end if;
    Fp := GF(p);
    is_sq := IsSquare(Fp!7);
    if not is_sq then continue; end if;

    PFp<t> := PolynomialRing(Fp);
    f := PFp!mp1_Q;
    fac := Factorization(f);
    if not &and[Degree(ff[1]) eq 1 : ff in fac] then continue; end if;
    j1p := -Coefficient(fac[1][1], 0);
    ok, ap := TraceFromJ(j1p, Fp);
    if not ok then continue; end if;
    Append(~ap_data, <p, ap>);
end for;

printf "a_p data: %o\n", ap_data;

// Try to match with small conductor curves from Cremona database
print "\n=== Searching Cremona database ===";
// Check conductors up to 1000
D := CremonaDatabase();
for N in [1..1000] do
    if N gt LargestConductor(D) then break; end if;
    if NumberOfIsogenyClasses(D, N) eq 0 then continue; end if;
    curves := EllipticCurves(D, N);
    for E_Q in curves do
        match := true;
        matched_count := 0;
        for dat in ap_data do
            p := dat[1]; ap_want := dat[2];
            if N mod p eq 0 then continue; end if;
            ap_E := TraceOfFrobenius(E_Q, p);
            if ap_E ne ap_want and ap_E ne -ap_want then
                match := false;
                break;
            end if;
            matched_count +:= 1;
        end for;
        if match and matched_count ge 3 then
            printf "MATCH: N=%o, curve %o, j=%o\n",
                N, CremonaReference(E_Q), jInvariant(E_Q);
        end if;
    end for;
end for;

// Same for j23 curves
print "\n=== Trace data for j23 curves ===";
ap_data_23 := [];
for p in PrimesInInterval(5, 100) do
    Fp := GF(p);
    PFp<t> := PolynomialRing(Fp);
    f := PFp!mp23_Q;
    fac := Factorization(f);
    if not &and[Degree(ff[1]) eq 1 : ff in fac] then continue; end if;
    roots := [-Coefficient(ff[1], 0) : ff in fac];
    aps := [];
    all_ok := true;
    for r in roots do
        ok, ap := TraceFromJ(r, Fp);
        if not ok then all_ok := false; break; end if;
        Append(~aps, ap);
    end for;
    if not all_ok then continue; end if;
    Append(~ap_data_23, <p, aps>);
end for;

printf "a_p data for j23: %o\n", ap_data_23;

print "\nSearching Cremona database for j23 match...";
for N in [1..1000] do
    if N gt LargestConductor(D) then break; end if;
    if NumberOfIsogenyClasses(D, N) eq 0 then continue; end if;
    curves := EllipticCurves(D, N);
    for E_Q in curves do
        match := true;
        matched_count := 0;
        for dat in ap_data_23 do
            p := dat[1]; aps_want := dat[2];
            if N mod p eq 0 then continue; end if;
            ap_E := TraceOfFrobenius(E_Q, p);
            if not exists{a : a in aps_want | ap_E eq a or ap_E eq -a} then
                match := false;
                break;
            end if;
            matched_count +:= 1;
        end for;
        if match and matched_count ge 2 then
            printf "MATCH: N=%o, curve %o, j=%o\n",
                N, CremonaReference(E_Q), jInvariant(E_Q);
        end if;
    end for;
end for;
