/*******************************************************************************
 * bitangent_gl2.m
 *
 * Connect the rational decomposition to bitangent-product ones via GL2.
 * Work over Q(zeta_8) where i, sqrt(2), sqrt(-2) all exist.
 *
 * 6 bitangent pairs, 3 S3-orbits:
 *   {L1L2, L3L4}: paired by (x,y) sign flip
 *   {L1L3, L2L4}: paired by (x,z) sign flip
 *   {L1L4, L2L3}: paired by (y,z) sign flip
 ******************************************************************************/

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

// =========================================================================
// Rational decomposition, normalized to F = Q1*Q3 - Q2^2
// =========================================================================
Q1_R := ((X-Y)^2+Z^2) / sr2;
Q2_R := im*(X^2+Y^2-Z^2) / sr2;
Q3_R := ((X+Y)^2+Z^2) / sr2;
assert Q1_R*Q3_R - Q2_R^2 eq FK;
printf "Rational decomposition (normalized):\n";
printf "  Q1 = ((x-y)^2+z^2)/sqrt(2)\n  Q2 = i(x^2+y^2-z^2)/sqrt(2)\n  Q3 = ((x+y)^2+z^2)/sqrt(2)\n\n";

v1r := QtoV(Q1_R); v2r := QtoV(Q2_R); v3r := QtoV(Q3_R);

// =========================================================================
// All 6 bitangent decompositions: F = (LiLj)(Qij_3) - (sqrt(-2)*Pij)^2
// where Pij is the "tangent quadric" at the bitangent pair
// =========================================================================
printf "=== ALL 6 BITANGENT DECOMPOSITIONS ===\n\n";

bitan := [
    // L1L2 = (x+y)^2-z^2; tangent: x^2+xy+y^2; Q3 = -(x+y)^2-z^2
    <L1*L2, sr_2*(X^2+X*Y+Y^2), -(X+Y)^2-Z^2, "L1*L2">,
    // L3L4 = (x-y)^2-z^2; tangent: x^2-xy+y^2; Q3 = -(x-y)^2-z^2
    <L3*L4, sr_2*(X^2-X*Y+Y^2), -(X-Y)^2-Z^2, "L3*L4">,
    // L1L3 = (x+z)^2-y^2; tangent: x^2+xz+z^2; Q3 = -(x+z)^2-y^2
    <L1*L3, sr_2*(X^2+X*Z+Z^2), -(X+Z)^2-Y^2, "L1*L3">,
    // L2L4 = (x-z)^2-y^2; tangent: x^2-xz+z^2; Q3 = -(x-z)^2-y^2
    <L2*L4, sr_2*(X^2-X*Z+Z^2), -(X-Z)^2-Y^2, "L2*L4">,
    // L1L4 = x^2-(y+z)^2; tangent: y^2+yz+z^2; Q3 = x^2+(y+z)^2
    <L1*L4, sr_2*(Y^2+Y*Z+Z^2), X^2+(Y+Z)^2, "L1*L4">,
    // L2L3 = x^2-(y-z)^2; tangent: y^2-yz+z^2; Q3 = x^2+(y-z)^2
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

// =========================================================================
// GL2 connections: rational -> each bitangent decomposition
// =========================================================================
printf "\n=== GL2 ORBIT CONNECTIONS ===\n\n";

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

    // Find g and apply full transform.  Try ALL valid g's and pick best.
    candidates := [];

    if u3 eq 0 and u1 ne 0 then
        // b=0: c=u1/a, d=u2/a. det=u2. Try a=1.
        if u2^2 eq 1 then
            Append(~candidates, <K!1, K!0, u1, u2>);
        end if;
        // d=0: c=u1/a, b=u2/c=u2*a/u1. det=-u2.
        if u2^2 eq 1 then
            Append(~candidates, <K!1, u2/u1, u1, K!0>);
        end if;
        // Also try with i factors
        for a_try in [im, -im] do
            // b=0: det = u2/a_try
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
        det := a*d - b_val*c;

        nv1 := [a^2*v1r[k]+2*a*b_val*v2r[k]+b_val^2*v3r[k] : k in [1..6]];
        nv1_list := nv1;
        // Check proportionality to target Q1
        ratio := K!0;
        is_prop := true;
        for k in [1..6] do
            if tv1[k] ne 0 then
                if ratio eq 0 then
                    ratio := nv1_list[k] / tv1[k];
                elif nv1_list[k] / tv1[k] ne ratio then
                    is_prop := false; break;
                end if;
            elif nv1_list[k] ne 0 then
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

// =========================================================================
// Which theta characteristics correspond to which bitangent pairs?
// =========================================================================
printf "=== THETA CHARACTERISTIC CLASSIFICATION ===\n\n";

// For each bitangent decomposition, classify the 2-torsion class at p=73
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

// Reduce a K-element to F_p: embed Q(zeta_8) -> F_p
// s = zeta_8 in F_p: need s^4=-1 and s^8=1. s is a primitive 8th root.
s_p := Sqrt(Sqrt(Fp!-1));  // This might not be a primitive 8th root
// Check: we need s_p^4 = -1
if s_p^4 ne Fp!-1 then
    // Try another root
    s_p := Sqrt(-Sqrt(Fp!-1));
    if s_p^4 ne Fp!-1 then
        s_p := Sqrt(Fp!-1) * Sqrt(Sqrt(Fp!-1));
    end if;
end if;
printf "Reduction to F_%o: s -> %o (s^4 = %o)\n\n", p, s_p, s_p^4;

function RedToFp(c)
    // c is in K = Q(s) where s=zeta_8
    // c = a0 + a1*s + a2*s^2 + a3*s^3
    coeffs := Eltseq(c);
    return &+[Fp!coeffs[j]*s_p^(j-1) : j in [1..4]];
end function;

// Classify each bitangent pair
pairs := [
    <(t+u)^2-1, "L1*L2">,       // (x+y)^2-z^2, affine z=1
    <(t-u)^2-1, "L3*L4">,       // (x-y)^2-z^2
    <t^2-u^2+2*t+1, "L1*L3">,   // Actually (x+z)^2-y^2 = x^2-y^2+2xz+z^2 -> t^2-u^2+2t+1
    <t^2-u^2-2*t+1, "L2*L4">,   // (x-z)^2-y^2 = t^2-u^2-2t+1
    <t^2-u^2-2*u-1, "L1*L4">,   // x^2-(y+z)^2 -> t^2-u^2-2u-1
    <t^2-u^2+2*u-1, "L2*L3">    // x^2-(y-z)^2 -> t^2-u^2+2u-1
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

quit;
