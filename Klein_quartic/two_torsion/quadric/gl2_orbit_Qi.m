/*******************************************************************************
 * gl2_orbit_Qi.m
 *
 * Explicit Q(i) decompositions F = Q1*Q3 - Q2^2 and GL2(Q(i)) orbit check.
 *
 * Strategy:
 * 1. List known decompositions + generate more via GL2 elements
 * 2. Deduplicate by Q2
 * 3. For each distinct Q2, solve for the GL2 element connecting to reference
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

printf "=== Q(i) DECOMPOSITIONS & GL2 ORBIT ===\n\n";

mons := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z];

function QtoV(Q)
    return [MonomialCoefficient(Q, m) : m in mons];
end function;

function VtoQ(v)
    return &+[v[k]*mons[k] : k in [1..6]];
end function;

// =========================================================================
// Phase 1: Build decompositions from known ones + GL2 transforms
// =========================================================================

// Three S3-basic decompositions
base := [
    <X^2+i*Z^2, i*Y^2, X^2-i*Z^2>,       // x<->yz
    <Y^2+i*Z^2, i*X^2, Y^2-i*Z^2>,       // y<->xz
    <X^2+i*Y^2, i*Z^2, X^2-i*Y^2>        // z<->xy
];

// GL2 elements to apply (small ones)
// g = [[a,b],[c,d]]
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
    [K!1, K!i, K!i, K!1],    // det=1+1=2? no, 1-i^2=1+1=2
    [K!1, K!i, K!1, K!0]     // det=-i
];

decomps := [];
for b in base do
    v1 := QtoV(b[1]); v2 := QtoV(b[2]); v3 := QtoV(b[3]);
    for g in gl2_elts do
        a := g[1]; bb := g[2]; c := g[3]; d := g[4];
        det := a*d - bb*c;
        if det eq 0 then continue; end if;
        // Only keep det^2 = 1 (so Q1'Q3'-Q2'^2 = F)
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

// =========================================================================
// Phase 2: For each pair, find g in GL2(Q(i)) with det^2=1
// =========================================================================
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
    // where u1=ac, u2=ad+bc, u3=bd
    // Magma convention: sol*M = rhs, so M is 3x6 with rows v1r,v2r,v3r
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
        // bd = 0. Try b=0 and d=0 cases.
        if u1 ne 0 then
            // b=0: c=u1, d=u2, det=u2
            a := K!1; b := K!0; c := u1; d := u2;
            det := a*d - b*c;
            if det ne 0 and det^2 eq 1 then
                printf "  g = [[1,0],[%o,%o]], det=%o  ***\n", c, d, det;
                found_g := true;
            end if;

            // d=0: b=u2/u1, c=u1, det=-u2
            if not found_g then
                b := u2/u1; d := K!0; c := u1;
                det := K!1*d - b*c;
                if det ne 0 and det^2 eq 1 then
                    printf "  g = [[1,%o],[%o,0]], det=%o  ***\n", b, c, det;
                    found_g := true;
                end if;
            end if;

            // Try other a values for b=0 case to get det^2=1
            if not found_g then
                // det = d = u2/a for b=0 case.  Need (u2/a)^2 = 1 => a = +-u2 or a = +-i*u2
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

            // d=0, try different a for det^2=1
            if not found_g then
                // det = -bc = -u1*a/... hmm this is trickier
                // det = a*0 - (u2/u1*a)*u1/a ... let me redo
                // With d=0: a arbitrary, c=u1/a, b=u2*a/u1 (from bc=u2, since ad=0)
                // Wait: u1=ac, u2=ad+bc, u3=bd=0. With d=0: u2=bc.
                // So c = u1/a, b = u2/c = u2*a/u1.
                // det = a*0 - b*c = -(u2*a/u1)*(u1/a) = -u2.
                // Need det^2 = u2^2 = 1. So this works iff u2^2 = 1.
                if u2^2 eq 1 then
                    a := K!1; c := u1; b := u2/u1; d := K!0;
                    det := -u2;
                    printf "  g = [[1,%o],[%o,0]], det=%o  ***\n", b, c, det;
                    found_g := true;
                end if;
            end if;
        elif u2 ne 0 then
            // u1=0, u3=0: ac=0, bd=0. If a=0,d=0: bc=u2
            a := K!0; d := K!0; b := K!1; c := u2;
            det := -c;
            if det^2 eq 1 then
                printf "  g = [[0,1],[%o,0]], det=%o  ***\n", c, det;
                found_g := true;
            end if;
            if not found_g then
                // a=0,b=0: impossible (det=0)
                // a!=0,b=0: ac=0 means c=0, then ad+bc=ad=u2
                // bd=0. det=ad. Need ad=u2 and (ad)^2=1 => u2^2=1
                if u2^2 eq 1 then
                    a := K!1; b := K!0; c := K!0; d := u2;
                    det := u2;
                    printf "  g = [[1,0],[0,%o]], det=%o  ***\n", d, det;
                    found_g := true;
                end if;
            end if;
        end if;
    else
        // u3 != 0: quadratic in r = a/b
        // u3*r^2 - u2*r + u1 = 0
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
                // a=r, b=1 => c=u1/r, d=u3
                a := r; b := K!1; c := u1/r; d := u3;
                det := a*d - b*c;
                if det eq 0 then continue; end if;

                // Need det^2 = 1. If not, rescale: a -> a/s, b -> b/s
                // where s^2 = det^2.  Then det -> det/s^2... no, that changes det.
                // Actually g -> g/s gives det -> det/s^2.  Need det/s^2 = +-1 or +-i.
                // Hmm, let me just try to rescale b.
                // With b general: a=r*b, c=u1/(r*b), d=u3/b.
                // det = r*b*(u3/b) - b*(u1/(r*b)) = r*u3 - u1/r.
                // This is independent of b!  So det is determined by r.
                // det = r*u3 - u1/r = (r^2*u3 - u1)/r.
                // From quadratic: r^2*u3 = u2*r - u1, so r^2*u3-u1 = u2*r-2*u1.
                // det = (u2*r - 2*u1)/r = u2 - 2*u1/r.

                if det^2 ne 1 then
                    printf "  sign=%o: det=%o, det^2=%o (not 1, adjusting...)\n", sign, det, det^2;
                    // Can we find b such that det of [[r*b,b],[u1/(r*b),u3/b]] has det^2=1?
                    // det = r*b*u3/b - b*u1/(r*b) = r*u3 - u1/r (independent of b!)
                    // So no help from b.  Try the other root.
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
                // The action with det^2 = -1 gives Q1'Q3'-Q2'^2 = -F.
                // Not what we want.  But maybe we can compose with another element.
                // For now, just report.
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
printf "All decompositions in single GL2(Q(i))-orbit (det^2=1)? %o\n", all_connected;

quit;
