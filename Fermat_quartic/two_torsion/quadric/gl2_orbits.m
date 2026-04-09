/*******************************************************************************
 * gl2_orbits.m
 *
 * GL2 orbit structure of quadric decompositions F = Q1*Q3 - Q2^2
 * for F = x^4+y^4+z^4.
 *
 * Merged from: gl2_orbit.m, gl2_orbit_Qi.m, bitangent_gl2.m,
 *              bitangent_gl2_exact.m
 * (gl2_orbit2.m dropped: sampling subsumed by exhaustive check)
 *
 * GL2 action on (Q1,Q2,Q3) via M -> g*M*g^T on symmetric matrix
 *   M = [[Q1,Q2],[Q2,Q3]]:
 *   Q1' = a^2*Q1 + 2ab*Q2 + b^2*Q3
 *   Q2' = ac*Q1 + (ad+bc)*Q2 + bd*Q3
 *   Q3' = c^2*Q1 + 2cd*Q2 + d^2*Q3
 * Preserves det(M) = Q1*Q3-Q2^2 up to det(g)^2.
 *
 * Contents:
 *   Part 1: Exhaustive single-orbit verification over F_p
 *   Part 2: GL2(Q(i)) orbit structure
 *   Part 3: Bitangent decompositions over Q(zeta_8) and GL2 connections
 *   Part 4: Veronese conic analysis for bitangent targets
 ******************************************************************************/

// =========== PART 1: EXHAUSTIVE SINGLE-ORBIT VERIFICATION OVER F_p ===========
printf "=== PART 1: EXHAUSTIVE SINGLE-ORBIT VERIFICATION OVER F_p ===\n\n";

for p in [5, 13] do
    printf "============================================\n";
    printf "p = %o\n", p;
    printf "============================================\n";
    Fp := GF(p);
    R<x,y,z> := PolynomialRing(Fp, 3);
    F := x^4 + y^4 + z^4;
    im := Sqrt(Fp!-1);
    printf "i = %o\n", im;

    // Check smoothness / factorization of F
    fF := Factorization(F);
    printf "F factors into %o piece(s)\n", #fF;
    for pair in fF do
        printf "  (%o)^%o  deg %o\n", pair[1], pair[2], TotalDegree(pair[1]);
    end for;

    mons := [x^2, y^2, z^2, x*y, x*z, y*z];

    function QtoV(Q)
        return [MonomialCoefficient(Q, m) : m in mons];
    end function;

    // Reference decomposition
    Q1r := x^2 + im*z^2;
    Q2r := im*y^2;
    Q3r := x^2 - im*z^2;
    assert Q1r*Q3r - Q2r^2 eq F;

    v1 := QtoV(Q1r); v2 := QtoV(Q2r); v3 := QtoV(Q3r);

    // Generate GL2 orbit (det(g)^2 = 1)
    orbit_Q2_set := {};
    orbit_count := 0;
    for a in Fp do for b in Fp do for c in Fp do for d in Fp do
        det := a*d - b*c;
        if det eq 0 or det^2 ne Fp!1 then continue; end if;

        nv2 := [a*c*v1[k] + (a*d+b*c)*v2[k] + b*d*v3[k] : k in [1..6]];
        Include(~orbit_Q2_set, nv2);
        orbit_count +:= 1;
    end for; end for; end for; end for;

    printf "GL2 elements with det^2=1: %o\n", orbit_count;
    printf "Distinct Q2 in orbit: %o\n", #orbit_Q2_set;
    printf "|SL2(F_%o)| = %o\n\n", p, p*(p^2-1);

    // Exhaustive search over all Q2
    total := 0;
    in_orb := 0;
    out_orb := 0;

    for a1 in Fp do for a2 in Fp do for a3 in Fp do
    for a4 in Fp do for a5 in Fp do for a6 in Fp do
        Q2 := a1*x^2+a2*y^2+a3*z^2+a4*x*y+a5*x*z+a6*y*z;
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
            total +:= 1;
            coeffs := [Fp!a1,Fp!a2,Fp!a3,Fp!a4,Fp!a5,Fp!a6];
            if coeffs in orbit_Q2_set then
                in_orb +:= 1;
            else
                out_orb +:= 1;
                if out_orb le 3 then
                    printf "  NOT in orbit: Q2 = %o\n", Q2;
                end if;
            end if;
        end if;
    end for; end for; end for;
    end for; end for; end for;

    printf "Total Q2 giving decomposition: %o\n", total;
    printf "  In orbit: %o\n  Outside orbit: %o\n", in_orb, out_orb;
    printf "SINGLE GL2 ORBIT? %o\n\n", out_orb eq 0;

    // Check: if F itself factors into two quadrics, those give
    // "degenerate" decompositions (Q2=0)
    zero_vec := [Fp!0 : k in [1..6]];
    if zero_vec in orbit_Q2_set then
        printf "Q2=0 is in the orbit.\n";
    else
        printf "Q2=0 is NOT in the orbit.\n";
        if #[pair : pair in fF | TotalDegree(pair[1]) eq 2] ge 2 then
            printf "  But F does factor into quadrics!\n";
        end if;
    end if;
    printf "\n";
end for;

// =========== PART 2: GL2(Q(i)) ORBIT STRUCTURE ===========
printf "=== PART 2: GL2(Q(i)) ORBIT STRUCTURE ===\n\n";

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

mons := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z];

function QtoV(Q)
    return [MonomialCoefficient(Q, m) : m in mons];
end function;

function VtoQ(v)
    return &+[v[k]*mons[k] : k in [1..6]];
end function;

// Three S3-basic decompositions
base := [
    <X^2+i*Z^2, i*Y^2, X^2-i*Z^2>,       // x<->yz
    <Y^2+i*Z^2, i*X^2, Y^2-i*Z^2>,       // y<->xz
    <X^2+i*Y^2, i*Z^2, X^2-i*Y^2>        // z<->xy
];

// GL2 elements to apply (small ones)
gl2_elts := [
    [K!1, K!0, K!0, K!1],    // identity
    [K!0, K!1, K!1, K!0],    // swap (det=-1)
    [K!1, K!1, K!0, K!1],    // upper shear (det=1)
    [K!1, K!0, K!1, K!1],    // lower shear (det=1)
    [K!1, K!1, K!1, K!0],    // det=-1
    [K!1, K!-1, K!1, K!0],   // det=-1
    [K!1, K!i, K!0, K!1],    // det=1
    [K!1, K!0, K!i, K!1],    // det=1
    [K!i, K!0, K!0, K!1],    // det=i
    [K!1, K!0, K!0, K!i],    // det=i
    [K!i, K!1, K!0, K!1],    // det=i
    [K!1, K!1, K!-1, K!1],   // det=2
    [K!1, K!i, K!i, K!1],    // det=2
    [K!1, K!i, K!1, K!0]     // det=-i
];

decomps := [];
for b in base do
    v1 := QtoV(b[1]); v2 := QtoV(b[2]); v3 := QtoV(b[3]);
    for g in gl2_elts do
        a := g[1]; bb := g[2]; c := g[3]; d := g[4];
        det := a*d - bb*c;
        if det eq 0 then continue; end if;
        if det^2 ne 1 then continue; end if;

        nv1 := [a^2*v1[k]+2*a*bb*v2[k]+bb^2*v3[k] : k in [1..6]];
        nv2 := [a*c*v1[k]+(a*d+bb*c)*v2[k]+bb*d*v3[k] : k in [1..6]];
        nv3 := [c^2*v1[k]+2*c*d*v2[k]+d^2*v3[k] : k in [1..6]];

        Q1n := VtoQ(nv1); Q2n := VtoQ(nv2); Q3n := VtoQ(nv3);
        Append(~decomps, <Q1n, Q2n, Q3n>);
    end for;
end for;

// Also add the memory one explicitly
Append(~decomps, <2*X^2+2*i*Z^2, X^2+i*Y^2+i*Z^2, X^2+i*Y^2>);

// Verify all
printf "Checking %o candidate decompositions...\n", #decomps;
valid := [];
for j in [1..#decomps] do
    d := decomps[j];
    if d[1]*d[3] - d[2]^2 eq FK then
        Append(~valid, d);
    end if;
end for;
printf "%o valid decompositions\n\n", #valid;

// Deduplicate by Q2 (up to scalar)
unique := [];
seen := {};
for d in valid do
    v := QtoV(d[2]);
    norm_v := v;
    for k in [1..6] do
        if v[k] ne 0 then
            norm_v := [v[j]/v[k] : j in [1..6]];
            break;
        end if;
    end for;
    if norm_v notin seen then
        Include(~seen, norm_v);
        Append(~unique, d);
    end if;
end for;

printf "=== %o DISTINCT DECOMPOSITIONS (by Q2) ===\n\n", #unique;
for j in [1..#unique] do
    d := unique[j];
    printf "#%o: Q1 = %o\n    Q2 = %o\n    Q3 = %o\n\n", j, d[1], d[2], d[3];
end for;

// --- GL2(Q(i)) orbit connections ---
printf "=== GL2(Q(i)) ORBIT CONNECTIONS ===\n";
printf "(reference = decomp #1)\n\n";

ref := unique[1];
v1r := QtoV(ref[1]); v2r := QtoV(ref[2]); v3r := QtoV(ref[3]);

all_connected := true;
for j in [2..#unique] do
    tgt := unique[j];
    v2t := QtoV(tgt[2]);
    printf "--- Connecting #1 -> #%o ---\n", j;
    printf "  Target Q2 = %o\n", tgt[2];

    // Solve: u1*v1r[k] + u2*v2r[k] + u3*v3r[k] = v2t[k]
    M := Matrix(K, 3, 6, v1r cat v2r cat v3r);
    rhs := Vector(K, v2t);
    ok, sol := IsConsistent(M, rhs);

    if not ok then
        printf "  NO SOLUTION for (u1,u2,u3) - NOT in orbit!\n\n";
        all_connected := false;
        continue;
    end if;

    u1 := sol[1]; u2 := sol[2]; u3 := sol[3];
    printf "  (ac, ad+bc, bd) = (%o, %o, %o)\n", u1, u2, u3;

    found_g := false;

    if u3 eq 0 then
        if u1 ne 0 then
            // b=0 case
            if u2^2 eq 1 then
                a := K!1; b := K!0; c := u1; d := u2;
                det := a*d - b*c;
                if det ne 0 and det^2 eq 1 then
                    printf "  g = [[1,0],[%o,%o]], det=%o  ***\n", c, d, det;
                    found_g := true;
                end if;
            end if;

            if not found_g then
                for a_try in [u2, -u2, i*u2, -i*u2] do
                    if a_try eq 0 then continue; end if;
                    a := a_try; b := K!0; c := u1/a; d := u2/a;
                    det := a*d - b*c;
                    if det ne 0 and det^2 eq 1 then
                        printf "  g = [[%o,0],[%o,%o]], det=%o  ***\n", a, c, d, det;
                        found_g := true;
                        break;
                    end if;
                end for;
            end if;

            if not found_g and u2^2 eq 1 then
                a := K!1; c := u1; b := u2/u1; d := K!0;
                det := -u2;
                printf "  g = [[1,%o],[%o,0]], det=%o  ***\n", b, c, det;
                found_g := true;
            end if;
        elif u2 ne 0 then
            // u1=0, u3=0
            if u2^2 eq 1 then
                a := K!1; b := K!0; c := K!0; d := u2;
                det := u2;
                printf "  g = [[1,0],[0,%o]], det=%o  ***\n", d, det;
                found_g := true;
            end if;
            if not found_g then
                a := K!0; d := K!0; b := K!1; c := u2;
                det := -c;
                if det^2 eq 1 then
                    printf "  g = [[0,1],[%o,0]], det=%o  ***\n", c, det;
                    found_g := true;
                end if;
            end if;
        end if;
    else
        // u3 != 0: quadratic in r = a/b
        disc := u2^2 - 4*u1*u3;
        printf "  Quadratic for r=a/b: %o*r^2-%o*r+%o=0, disc=%o\n", u3, u2, u1, disc;

        PK<xx> := PolynomialRing(K);
        fdisc := Factorization(xx^2 - disc);
        has_sqrt := false;
        sq := K!0;
        for pair in fdisc do
            if Degree(pair[1]) eq 1 then
                has_sqrt := true;
                sq := -Evaluate(pair[1], 0)/LeadingCoefficient(pair[1]);
                break;
            end if;
        end for;

        if has_sqrt then
            printf "  sqrt(disc) = %o\n", sq;
            for sign in [1, -1] do
                r := (u2 + sign*sq) / (2*u3);
                if r eq 0 then continue; end if;
                a := r; b := K!1; c := u1/r; d := u3;
                det := a*d - b*c;
                if det eq 0 then continue; end if;

                if det^2 ne 1 then
                    printf "  sign=%o: det=%o, det^2=%o (not 1, adjusting...)\n", sign, det, det^2;
                    continue;
                end if;

                printf "  sign=%o: g=[[%o,1],[%o,%o]], det=%o  ***\n", sign, r, c, d, det;

                // Full verification
                nv1 := [a^2*v1r[k]+2*a*b*v2r[k]+b^2*v3r[k] : k in [1..6]];
                nv2 := [a*c*v1r[k]+(a*d+b*c)*v2r[k]+b*d*v3r[k] : k in [1..6]];
                nv3 := [c^2*v1r[k]+2*c*d*v2r[k]+d^2*v3r[k] : k in [1..6]];
                Q1n := VtoQ(nv1); Q2n := VtoQ(nv2); Q3n := VtoQ(nv3);
                ver := Q1n*Q3n - Q2n^2;
                printf "  Verified: Q1'Q3'-Q2'^2 = F? %o\n", ver eq FK;
                printf "  Q2' matches target? %o\n", QtoV(Q2n) eq v2t;
                found_g := true;
                break;
            end for;

            if not found_g then
                printf "  Neither root gives det^2=1.  Trying det^2=-1...\n";
            end if;
        else
            printf "  Discriminant NOT a square in Q(i)!\n";
        end if;
    end if;

    if not found_g then
        printf "  *** COULD NOT CONNECT ***\n";
        all_connected := false;
    end if;
    printf "\n";
end for;

printf "=== SUMMARY ===\n";
printf "All decompositions in single GL2(Q(i))-orbit (det^2=1)? %o\n\n", all_connected;

// Clean up Q(i) variables
delete RK; delete K; delete P;

// =========== PART 3: BITANGENT DECOMPOSITIONS OVER Q(zeta_8) ===========
printf "=== PART 3: BITANGENT DECOMPOSITIONS OVER Q(zeta_8) ===\n\n";

P<x> := PolynomialRing(Rationals());
K<s> := NumberField(x^4 + 1);  // s = zeta_8
im := s^2;           // i
sr2 := s - s^3;      // sqrt(2)
sr_2 := s + s^3;     // sqrt(-2)

RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

L1 := X+Y+Z; L2 := X+Y-Z; L3 := X-Y+Z; L4 := X-Y-Z;

mons := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z];

function QtoV(Q)
    return [MonomialCoefficient(Q, m) : m in mons];
end function;

function VtoQ(v)
    return &+[v[k]*mons[k] : k in [1..6]];
end function;

// Rational decomposition, normalized to F = Q1*Q3 - Q2^2
Q1_R := ((X-Y)^2+Z^2) / sr2;
Q2_R := im*(X^2+Y^2-Z^2) / sr2;
Q3_R := ((X+Y)^2+Z^2) / sr2;
assert Q1_R*Q3_R - Q2_R^2 eq FK;
printf "Rational decomposition (normalized):\n";
printf "  Q1 = ((x-y)^2+z^2)/sqrt(2)\n  Q2 = i(x^2+y^2-z^2)/sqrt(2)\n  Q3 = ((x+y)^2+z^2)/sqrt(2)\n\n";

v1r := QtoV(Q1_R); v2r := QtoV(Q2_R); v3r := QtoV(Q3_R);

// All 6 bitangent decompositions
printf "--- All 6 bitangent decompositions ---\n\n";

bitan := [
    <L1*L2, sr_2*(X^2+X*Y+Y^2), -(X+Y)^2-Z^2, "L1*L2">,
    <L3*L4, sr_2*(X^2-X*Y+Y^2), -(X-Y)^2-Z^2, "L3*L4">,
    <L1*L3, sr_2*(X^2+X*Z+Z^2), -(X+Z)^2-Y^2, "L1*L3">,
    <L2*L4, sr_2*(X^2-X*Z+Z^2), -(X-Z)^2-Y^2, "L2*L4">,
    <L1*L4, sr_2*(Y^2+Y*Z+Z^2), X^2+(Y+Z)^2, "L1*L4">,
    <L2*L3, sr_2*(Y^2-Y*Z+Z^2), X^2+(Y-Z)^2, "L2*L3">
];

for idx in [1..#bitan] do
    b := bitan[idx];
    ver := b[1]*b[3] - b[2]^2;
    printf "%o: Q1=%o, Q3=%o\n", b[4], b[1], b[3];
    printf "  Q1*Q3-Q2^2 = F? %o\n", ver eq FK;
    if ver ne FK then
        printf "  ERROR: got %o\n", ver;
    end if;
end for;

// --- GL2 orbit connections: rational -> each bitangent decomposition ---
printf "\n--- GL2 orbit connections: rational -> bitangent ---\n\n";

for idx in [1..#bitan] do
    b := bitan[idx];
    if b[1]*b[3] - b[2]^2 ne FK then continue; end if;

    v2t := QtoV(b[2]);
    printf "--- %o ---\n", b[4];

    M := Matrix(K, 3, 6, v1r cat v2r cat v3r);
    rhs := Vector(K, v2t);
    ok, sol := IsConsistent(M, rhs);

    if not ok then
        printf "  Different theta characteristic (no Q2 solution)\n\n";
        continue;
    end if;

    u1 := sol[1]; u2 := sol[2]; u3 := sol[3];
    printf "  (ac, ad+bc, bd) = (%o, %o, %o)\n", u1, u2, u3;

    // Find g and apply full transform
    candidates := [];

    if u3 eq 0 and u1 ne 0 then
        if u2^2 eq 1 then
            Append(~candidates, <K!1, K!0, u1, u2>);
            Append(~candidates, <K!1, u2/u1, u1, K!0>);
        end if;
        for a_try in [im, -im] do
            aa := a_try; det_try := u2/aa;
            if det_try^2 eq 1 then
                Append(~candidates, <aa, K!0, u1/aa, u2/aa>);
            end if;
        end for;
    elif u3 ne 0 then
        disc := u2^2 - 4*u1*u3;
        PK<xx> := PolynomialRing(K);
        fdisc := Factorization(xx^2 - disc);
        sq := K!0;
        for pair in fdisc do
            if Degree(pair[1]) eq 1 then
                sq := -Evaluate(pair[1], 0)/LeadingCoefficient(pair[1]);
                break;
            end if;
        end for;
        for sign in [1, -1] do
            r := (u2 + sign*sq) / (2*u3);
            if r eq 0 then continue; end if;
            aa := r; bb := K!1; cc := u1/r; dd := u3;
            det := aa*dd - bb*cc;
            if det ne 0 and det^2 eq 1 then
                Append(~candidates, <aa, bb, cc, dd>);
            end if;
        end for;
    elif u1 eq 0 and u2 ne 0 then
        if u2^2 eq 1 then
            Append(~candidates, <K!1, K!0, K!0, u2>);
        end if;
    end if;

    if #candidates eq 0 then
        printf "  Could not find any g with det^2=1\n\n";
        continue;
    end if;

    // Try each candidate, pick the one where Q1' is proportional to target Q1
    tv1 := QtoV(b[1]);
    best := 0;
    for ci in [1..#candidates] do
        cand := candidates[ci];
        a := cand[1]; b_val := cand[2]; c := cand[3]; d := cand[4];
        nv1 := [a^2*v1r[k]+2*a*b_val*v2r[k]+b_val^2*v3r[k] : k in [1..6]];

        ratio := K!0;
        is_prop := true;
        for k in [1..6] do
            if tv1[k] ne 0 then
                if ratio eq 0 then
                    ratio := nv1[k] / tv1[k];
                elif nv1[k] / tv1[k] ne ratio then
                    is_prop := false; break;
                end if;
            elif nv1[k] ne 0 then
                is_prop := false; break;
            end if;
        end for;
        if is_prop and ratio ne 0 then best := ci; break; end if;
    end for;

    if best eq 0 then best := 1; end if;
    cand := candidates[best];
    a := cand[1]; b_val := cand[2]; c := cand[3]; d := cand[4];
    det := a*d - b_val*c;
    printf "  g = [[%o, %o], [%o, %o]], det = %o\n", a, b_val, c, d, det;

    nv1 := [a^2*v1r[k]+2*a*b_val*v2r[k]+b_val^2*v3r[k] : k in [1..6]];
    nv2 := [a*c*v1r[k]+(a*d+b_val*c)*v2r[k]+b_val*d*v3r[k] : k in [1..6]];
    nv3 := [c^2*v1r[k]+2*c*d*v2r[k]+d^2*v3r[k] : k in [1..6]];
    Q1n := VtoQ(nv1); Q2n := VtoQ(nv2); Q3n := VtoQ(nv3);

    printf "  Q1' = %o\n", Q1n;
    printf "  Q2' = %o\n", Q2n;
    printf "  Q3' = %o\n", Q3n;
    printf "  Q1'Q3'-Q2'^2 = F? %o\n", Q1n*Q3n - Q2n^2 eq FK;

    // Check proportionality
    ratio := K!0;
    is_prop := true;
    for k in [1..6] do
        if tv1[k] ne 0 then
            if ratio eq 0 then
                ratio := QtoV(Q1n)[k] / tv1[k];
            elif QtoV(Q1n)[k] / tv1[k] ne ratio then
                is_prop := false; break;
            end if;
        elif QtoV(Q1n)[k] ne 0 then
            is_prop := false; break;
        end if;
    end for;

    if is_prop and ratio ne 0 then
        printf "  Q1' = (%o) * %o  [proportional, ratio^2 = %o]\n", ratio, b[4], ratio^2;
    else
        printf "  Q1' NOT proportional to %o\n", b[4];
    end if;
    printf "\n";
end for;

// --- Theta characteristic classification over F_p ---
printf "--- Theta characteristic classification over F_p ---\n\n";

p := 73;
Fp := GF(p);
im_p := Sqrt(Fp!-1); s3_p := Sqrt(Fp!-3);
A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1; u := KC.2;

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

LL := [t+u+1, t+u-1, t-u+1, t-u-1];
BB := [HalfPositive(Divisor(KC!LL[j])) : j in [1..4]];
vv1 := BB[1] - BB[2]; vv2 := BB[1] - BB[3];
q1_ref := KC!(2*t^2 + (1-s3_p)*u^2 + (1+s3_p));
_, half_ref := HalfDiv(Divisor(q1_ref));

function ClassifyHalf(half_D)
    labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_D - a0*half_ref - a1*vv1 - a2*vv2;
        if IsPrincipal(test) then
            return labels[4*a0+2*a1+a2+1];
        end if;
    end for; end for; end for;
    return "UNKNOWN";
end function;

// Embed Q(zeta_8) -> F_p
s_p := Sqrt(Sqrt(Fp!-1));
if s_p^4 ne Fp!-1 then
    s_p := Sqrt(-Sqrt(Fp!-1));
    if s_p^4 ne Fp!-1 then
        s_p := Sqrt(Fp!-1) * Sqrt(Sqrt(Fp!-1));
    end if;
end if;
printf "Reduction to F_%o: s -> %o (s^4 = %o)\n\n", p, s_p, s_p^4;

// Classify each bitangent pair
pairs := [
    <(t+u)^2-1, "L1*L2">,
    <(t-u)^2-1, "L3*L4">,
    <t^2-u^2+2*t+1, "L1*L3">,
    <t^2-u^2-2*t+1, "L2*L4">,
    <t^2-u^2-2*u-1, "L1*L4">,
    <t^2-u^2+2*u-1, "L2*L3">
];

for pair in pairs do
    q1_p := KC!(pair[1]);
    D := Divisor(q1_p);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf(half);
        printf "%o: class = %o\n", pair[2], cls;
    else
        printf "%o: odd multiplicities\n", pair[2];
    end if;
end for;

// Clean up
delete RK; delete K; delete P;
delete Caff; delete A2; delete KC;

// =========== PART 4: VERONESE CONIC ANALYSIS FOR BITANGENT TARGETS ===========
printf "\n=== PART 4: VERONESE CONIC ANALYSIS FOR BITANGENT TARGETS ===\n\n";

P<x> := PolynomialRing(Rationals());
K<s> := NumberField(x^4 + 1);  // s = zeta_8
im := s^2;           // i
sr2 := s - s^3;      // sqrt(2)
sr_2 := s + s^3;     // sqrt(-2)

RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

L1 := X+Y+Z; L2 := X+Y-Z; L3 := X-Y+Z; L4 := X-Y-Z;
printf "Bitangent lines:\n  L1=%o, L2=%o, L3=%o, L4=%o\n\n", L1, L2, L3, L4;

// Reference decomposition
Q1ref := L1*L2;
Q2ref := sr_2*(X^2+X*Y+Y^2);
Q3ref := -(X+Y)^2-Z^2;
assert Q1ref*Q3ref - Q2ref^2 eq FK;
printf "Reference: F = L1*L2 * (-(x+y)^2-z^2) - [sqrt(-2)(x^2+xy+y^2)]^2\n\n";

mons := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z];
function QtoV(Q) return [MonomialCoefficient(Q, m) : m in mons]; end function;
function VtoQ(v) return &+[v[k]*mons[k] : k in [1..6]]; end function;

v1r := QtoV(Q1ref); v2r := QtoV(Q2ref); v3r := QtoV(Q3ref);

// Try all 6 bitangent products as Q1' targets
targets := [
    <L1*L2, "L1*L2">, <L3*L4, "L3*L4">,
    <L1*L3, "L1*L3">, <L2*L4, "L2*L4">,
    <L1*L4, "L1*L4">, <L2*L3, "L2*L3">
];

printf "--- Which bitangent products Q1' are on the Veronese conic? ---\n\n";

for tgt in targets do
    tv := QtoV(tgt[1]);
    printf "--- Target Q1' = %o = %o ---\n", tgt[2], tgt[1];

    // Q1' = a^2*Q1ref + 2ab*Q2ref + b^2*Q3ref
    // Solve for (alpha, beta, gamma) = (a^2, 2ab, b^2)
    M := Matrix(K, 3, 6, v1r cat v2r cat v3r);
    rhs := Vector(K, tv);
    ok, sol := IsConsistent(M, rhs);

    if not ok then
        printf "  Not in span of {Q1,Q2,Q3} - IMPOSSIBLE\n\n";
        continue;
    end if;

    alpha := sol[1]; beta := sol[2]; gamma := sol[3];
    printf "  alpha=%o, beta=%o, gamma=%o  (Q1'=alpha*Q1+beta*Q2+gamma*Q3)\n", alpha, beta, gamma;

    // Check Veronese: alpha*gamma = (beta/2)^2?
    veronese := alpha*gamma - (beta/2)^2;
    printf "  Veronese check: alpha*gamma - (beta/2)^2 = %o\n", veronese;

    if veronese ne 0 then
        printf "  NOT on Veronese conic - cannot be Q1' for any g\n\n";
        continue;
    end if;

    // Solve: a^2 = alpha, b^2 = gamma, ab = beta/2
    printf "  ON Veronese conic! Finding a,b...\n";

    a_val := K!0; b_val := K!0;
    if beta ne 0 then
        r := 2*alpha/beta;
        PK<xx> := PolynomialRing(K);
        fgamma := Factorization(xx^2 - gamma);
        for pair in fgamma do
            if Degree(pair[1]) eq 1 then
                b_val := -Evaluate(pair[1], 0)/LeadingCoefficient(pair[1]);
                break;
            end if;
        end for;
        if b_val eq 0 then
            printf "  gamma=%o has no sqrt in Q(zeta_8)\n\n", gamma;
            continue;
        end if;
        a_val := r * b_val;
        printf "  a = %o, b = %o\n", a_val, b_val;
        assert a_val^2 eq alpha;
        assert b_val^2 eq gamma;
        assert a_val*b_val eq beta/2;
    else
        // beta = 0: ab = 0
        if gamma eq 0 then
            PK<xx> := PolynomialRing(K);
            falpha := Factorization(xx^2 - alpha);
            for pair in falpha do
                if Degree(pair[1]) eq 1 then
                    a_val := -Evaluate(pair[1], 0)/LeadingCoefficient(pair[1]);
                    break;
                end if;
            end for;
            if a_val eq 0 then printf "  No sqrt(alpha) in Q(zeta_8)\n\n"; continue; end if;
            b_val := K!0;
        else
            PK<xx> := PolynomialRing(K);
            fgamma := Factorization(xx^2 - gamma);
            for pair in fgamma do
                if Degree(pair[1]) eq 1 then
                    b_val := -Evaluate(pair[1], 0)/LeadingCoefficient(pair[1]);
                    break;
                end if;
            end for;
            if b_val eq 0 then printf "  No sqrt(gamma) in Q(zeta_8)\n\n"; continue; end if;
            a_val := K!0;
        end if;
    end if;

    // Complete g = [[a,b],[c,d]] with det^2 = 1
    found := false;

    // Try c=0 first
    if a_val ne 0 then
        for d_try in [K!1/a_val, -K!1/a_val, im/a_val, -im/a_val] do
            c_val := K!0;
            det := a_val*d_try - b_val*c_val;
            if det^2 eq 1 then
                d_val := d_try;
                nv1 := [a_val^2*v1r[k]+2*a_val*b_val*v2r[k]+b_val^2*v3r[k] : k in [1..6]];
                nv2 := [a_val*c_val*v1r[k]+(a_val*d_val+b_val*c_val)*v2r[k]+b_val*d_val*v3r[k] : k in [1..6]];
                nv3 := [c_val^2*v1r[k]+2*c_val*d_val*v2r[k]+d_val^2*v3r[k] : k in [1..6]];
                Q1n := VtoQ(nv1); Q2n := VtoQ(nv2); Q3n := VtoQ(nv3);
                ver := Q1n*Q3n - Q2n^2;

                printf "\n  g = [[%o, %o], [%o, %o]], det = %o\n", a_val, b_val, c_val, d_val, det;
                printf "  Q1' = %o\n", Q1n;
                printf "  Q2' = %o\n", Q2n;
                printf "  Q3' = %o\n", Q3n;
                printf "  Q1'*Q3' - Q2'^2 = F? %o\n", ver eq FK;
                printf "  Q1' = %o? %o\n", tgt[2], Q1n eq tgt[1];
                found := true;
                break;
            end if;
        end for;
    end if;

    // Try d=0 if c=0 didn't work
    if not found and b_val ne 0 then
        for c_try in [K!1/b_val, -K!1/b_val, im/b_val, -im/b_val] do
            c_val := c_try;
            d_val := K!0;
            det := a_val*d_val - b_val*c_val;
            if det^2 eq 1 then
                nv1 := [a_val^2*v1r[k]+2*a_val*b_val*v2r[k]+b_val^2*v3r[k] : k in [1..6]];
                nv2 := [a_val*c_val*v1r[k]+(a_val*d_val+b_val*c_val)*v2r[k]+b_val*d_val*v3r[k] : k in [1..6]];
                nv3 := [c_val^2*v1r[k]+2*c_val*d_val*v2r[k]+d_val^2*v3r[k] : k in [1..6]];
                Q1n := VtoQ(nv1); Q2n := VtoQ(nv2); Q3n := VtoQ(nv3);
                ver := Q1n*Q3n - Q2n^2;

                printf "\n  g = [[%o, %o], [%o, %o]], det = %o\n", a_val, b_val, c_val, d_val, det;
                printf "  Q1' = %o\n", Q1n;
                printf "  Q2' = %o\n", Q2n;
                printf "  Q3' = %o\n", Q3n;
                printf "  Q1'*Q3' - Q2'^2 = F? %o\n", ver eq FK;
                printf "  Q1' = %o? %o\n", tgt[2], Q1n eq tgt[1];
                found := true;
                break;
            end if;
        end for;
    end if;

    if not found then
        printf "  Could not find g with det^2=1 over Q(zeta_8)\n";
    end if;
    printf "\n";
end for;

quit;
