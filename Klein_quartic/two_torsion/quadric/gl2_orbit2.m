/*******************************************************************************
 * gl2_orbit2.m
 *
 * Verify single GL2 orbit for p=13 using sampling + orbit generation.
 ******************************************************************************/

p := 13;
Fp := GF(p);
R<x,y,z> := PolynomialRing(Fp, 3);
F := x^4 + y^4 + z^4;
im := Sqrt(Fp!-1);
printf "p = %o, i = %o\n\n", p, im;

mons := [x^2, y^2, z^2, x*y, x*z, y*z];

function QtoV(Q)
    return [MonomialCoefficient(Q, m) : m in mons];
end function;

// Reference
Q1r := x^2 + im*z^2;
Q2r := im*y^2;
Q3r := x^2 - im*z^2;
assert Q1r*Q3r - Q2r^2 eq F;
v1 := QtoV(Q1r); v2 := QtoV(Q2r); v3 := QtoV(Q3r);

// Generate orbit Q2 set
orbit_Q2 := {};
for a in Fp do for b in Fp do for c in Fp do for d in Fp do
    det := a*d - b*c;
    if det eq 0 or det^2 ne Fp!1 then continue; end if;
    nv2 := [a*c*v1[k] + (a*d+b*c)*v2[k] + b*d*v3[k] : k in [1..6]];
    Include(~orbit_Q2, nv2);
end for; end for; end for; end for;
printf "Distinct Q2 in orbit: %o\n\n", #orbit_Q2;

// Search 1: all diagonal Q2 (13^3 = 2197)
printf "--- Diagonal Q2 search ---\n";
diag_total := 0;
diag_in := 0;
diag_out := 0;
for a1 in Fp do for a2 in Fp do for a3 in Fp do
    Q2 := a1*x^2 + a2*y^2 + a3*z^2;
    G := F + Q2^2;
    fac := Factorization(G);
    deg2 := [pair : pair in fac | TotalDegree(pair[1]) eq 2];
    is_decomp := false;
    if #deg2 eq 2 and deg2[1][2] eq 1 and deg2[2][2] eq 1 then
        prod := deg2[1][1]*deg2[2][1];
        lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
        if lc*prod eq G then is_decomp := true; end if;
    elif #deg2 eq 1 and deg2[1][2] eq 2 then
        prod := deg2[1][1]^2;
        lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
        if lc*prod eq G then is_decomp := true; end if;
    end if;
    if is_decomp then
        diag_total +:= 1;
        if QtoV(Q2) in orbit_Q2 then diag_in +:= 1;
        else diag_out +:= 1;
            printf "  NOT in orbit: Q2 = %o\n", Q2;
        end if;
    end if;
end for; end for; end for;
printf "Diagonal: %o decomps, %o in orbit, %o outside\n\n", diag_total, diag_in, diag_out;

// Search 2: Q2 with one cross term + diagonal (13^4 each, 3 families)
printf "--- Q2 = a*x^2+b*y^2+c*z^2+d*xy search ---\n";
ct1_total := 0; ct1_in := 0; ct1_out := 0;
for a1 in Fp do for a2 in Fp do for a3 in Fp do for a4 in Fp do
    Q2 := a1*x^2 + a2*y^2 + a3*z^2 + a4*x*y;
    G := F + Q2^2;
    fac := Factorization(G);
    deg2 := [pair : pair in fac | TotalDegree(pair[1]) eq 2];
    is_decomp := false;
    if #deg2 eq 2 and deg2[1][2] eq 1 and deg2[2][2] eq 1 then
        prod := deg2[1][1]*deg2[2][1];
        lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
        if lc*prod eq G then is_decomp := true; end if;
    elif #deg2 eq 1 and deg2[1][2] eq 2 then
        prod := deg2[1][1]^2;
        lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
        if lc*prod eq G then is_decomp := true; end if;
    end if;
    if is_decomp then
        ct1_total +:= 1;
        if QtoV(Q2) in orbit_Q2 then ct1_in +:= 1;
        else ct1_out +:= 1;
            if ct1_out le 3 then printf "  NOT in orbit: Q2 = %o\n", Q2; end if;
        end if;
    end if;
end for; end for; end for; end for;
printf "+xy: %o decomps, %o in, %o out\n\n", ct1_total, ct1_in, ct1_out;

// Search 3: random Q2 with all 6 coefficients
printf "--- Random Q2 search (1000 samples) ---\n";
rand_total := 0; rand_in := 0; rand_out := 0;
for trial in [1..1000] do
    coeffs := [Random(Fp) : k in [1..6]];
    Q2 := &+[coeffs[k]*mons[k] : k in [1..6]];
    G := F + Q2^2;
    fac := Factorization(G);
    deg2 := [pair : pair in fac | TotalDegree(pair[1]) eq 2];
    is_decomp := false;
    if #deg2 eq 2 and deg2[1][2] eq 1 and deg2[2][2] eq 1 then
        prod := deg2[1][1]*deg2[2][1];
        lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
        if lc*prod eq G then is_decomp := true; end if;
    elif #deg2 eq 1 and deg2[1][2] eq 2 then
        prod := deg2[1][1]^2;
        lc := LeadingCoefficient(G)/LeadingCoefficient(prod);
        if lc*prod eq G then is_decomp := true; end if;
    end if;
    if is_decomp then
        rand_total +:= 1;
        if QtoV(Q2) in orbit_Q2 then rand_in +:= 1;
        else rand_out +:= 1;
            printf "  NOT in orbit: Q2 = %o\n", Q2;
        end if;
    end if;
end for;
printf "Random: %o decomps in 1000 samples, %o in orbit, %o outside\n\n", rand_total, rand_in, rand_out;

// Summary
printf "=== SUMMARY for p=%o ===\n", p;
printf "Orbit has %o distinct Q2 values\n", #orbit_Q2;
printf "All tested decompositions in orbit? %o\n", diag_out + ct1_out + rand_out eq 0;

// Theoretical: orbit size should be |SL2|/1 = p(p^2-1)
// But Q2 values have multiplicity (multiple triples per Q2)
// Number of Q2 values = orbit size / multiplicity
// For p=5: 120 triples, 30 Q2 values -> mult = 4
printf "Theoretical |SL2| = %o\n", p*(p^2-1);
printf "Orbit Q2 count / p = %o (should be integer)\n", #orbit_Q2;

quit;
