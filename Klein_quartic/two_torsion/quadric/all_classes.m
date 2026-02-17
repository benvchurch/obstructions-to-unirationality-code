/*******************************************************************************
 * all_classes.m
 *
 * Compute the 2-torsion class for all rational quadric decompositions
 * of F = x^4+y^4+z^4 found by the search (up to scaling).
 ******************************************************************************/

p := 73;
Fp := GF(p);
im := Sqrt(Fp!-1);
s3 := Sqrt(Fp!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n\n", p, im, s3;

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

// Set up classification basis
L := [t+u+1, t+u-1, t-u+1, t-u-1];
B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
v1 := B[1] - B[2];
v2 := B[1] - B[3];

// eta reference
q1_ref := KC!(2*t^2 + (1-s3)*u^2 + (1+s3));
_, half_ref := HalfDiv(Divisor(q1_ref));

function Classify(half_D)
    labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_D - a0*half_ref - a1*v1 - a2*v2;
        if IsPrincipal(test) then
            return labels[4*a0+2*a1+a2+1];
        end if;
    end for; end for; end for;
    return "UNKNOWN";
end function;

// =========================================================================
// The three decompositions from S3 symmetry
// =========================================================================
printf "=== RATIONAL DECOMPOSITIONS 2F = Q1*Q3 + Q2^2 ===\n\n";

// Decomposition 1: Q1 = (x-y)^2+z^2, affine z=1: (t-u)^2+1
printf "--- Decomp 1: Q1 = (x-y)^2+z^2 ---\n";
q1a := KC!((t-u)^2 + 1);
D1 := Divisor(q1a);
ok1, h1 := HalfDiv(D1);
printf "  HalfDiv: %o, class = %o\n\n", ok1, ok1 select Classify(h1) else "N/A";

// Decomposition 1': Q3 = (x+y)^2+z^2, affine z=1: (t+u)^2+1
printf "--- Decomp 1': Q3 = (x+y)^2+z^2 ---\n";
q3a := KC!((t+u)^2 + 1);
D3 := Divisor(q3a);
ok3, h3 := HalfDiv(D3);
printf "  HalfDiv: %o, class = %o\n", ok3, ok3 select Classify(h3) else "N/A";
if ok1 and ok3 then
    printf "  Q1 and Q3 same class? %o\n\n", IsPrincipal(h1-h3);
end if;

// Decomposition 2: Q1 = (y-z)^2+x^2 = x^2+y^2-2yz+z^2, affine z=1: t^2+u^2-2u+1
printf "--- Decomp 2: Q1 = x^2+(y-z)^2 ---\n";
q1b := KC!(t^2 + u^2 - 2*u + 1);
D1b := Divisor(q1b);
ok1b, h1b := HalfDiv(D1b);
printf "  HalfDiv: %o, class = %o\n\n", ok1b, ok1b select Classify(h1b) else "N/A";

// Decomposition 2': Q3 = x^2+(y+z)^2, affine z=1: t^2+u^2+2u+1
printf "--- Decomp 2': Q3 = x^2+(y+z)^2 ---\n";
q3b := KC!(t^2 + u^2 + 2*u + 1);
D3b := Divisor(q3b);
ok3b, h3b := HalfDiv(D3b);
printf "  HalfDiv: %o, class = %o\n\n", ok3b, ok3b select Classify(h3b) else "N/A";

// Decomposition 3: Q1 = (x-z)^2+y^2, affine z=1: (t-1)^2+u^2
printf "--- Decomp 3: Q1 = (x-z)^2+y^2 ---\n";
q1c := KC!((t-1)^2 + u^2);
D1c := Divisor(q1c);
ok1c, h1c := HalfDiv(D1c);
printf "  HalfDiv: %o, class = %o\n\n", ok1c, ok1c select Classify(h1c) else "N/A";

// Decomposition 3': Q3 = (x+z)^2+y^2, affine z=1: (t+1)^2+u^2
printf "--- Decomp 3': Q3 = (x+z)^2+y^2 ---\n";
q3c := KC!((t+1)^2 + u^2);
D3c := Divisor(q3c);
ok3c, h3c := HalfDiv(D3c);
printf "  HalfDiv: %o, class = %o\n\n", ok3c, ok3c select Classify(h3c) else "N/A";

// =========================================================================
// c=-9/2 decomposition: F = (7/9)*Q1*Q3 + (-2/9)*Q2^2
// Q1 = (x+y)^2+z^2 (same as Decomp 1' Q3), Q3 = x^2-10/7*xy+y^2+1/7*z^2
// =========================================================================
printf "--- c=-9/2 decomp: Q3_new = x^2-10/7*xy+y^2+1/7*z^2 ---\n";
// Affine z=1: t^2-10/7*tu+u^2+1/7
q3_new := KC!(t^2 - (Fp!10/Fp!7)*t*u + u^2 + Fp!1/Fp!7);
D3_new := Divisor(q3_new);
ok_new, h_new := HalfDiv(D3_new);
printf "  HalfDiv: %o, class = %o\n\n", ok_new, ok_new select Classify(h_new) else "N/A";

// =========================================================================
// Summary
// =========================================================================
printf "=== SUMMARY ===\n";
printf "Rational decomposition 2F = Q1*Q3 + Q2^2 exists!\n";
printf "Three families from S3 symmetry.\n";
printf "Classes realized by rational Q1:\n";
if ok1 then printf "  (x-y)^2+z^2 -> %o\n", Classify(h1); end if;
if ok3 then printf "  (x+y)^2+z^2 -> %o\n", Classify(h3); end if;
if ok1b then printf "  x^2+(y-z)^2 -> %o\n", Classify(h1b); end if;
if ok3b then printf "  x^2+(y+z)^2 -> %o\n", Classify(h3b); end if;
if ok1c then printf "  (x-z)^2+y^2 -> %o\n", Classify(h1c); end if;
if ok3c then printf "  (x+z)^2+y^2 -> %o\n", Classify(h3c); end if;

quit;
