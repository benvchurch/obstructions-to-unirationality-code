/*******************************************************************************
 * bitangent_gl2_exact.m
 *
 * Starting from the bitangent decomposition F = L1*L2 * Q3 - Q2^2 (over Q(sqrt(-2))),
 * apply GL2 elements to find all decompositions where Q1 is exactly a bitangent product.
 *
 * Reference: Q1 = L1*L2, Q2 = sqrt(-2)(x^2+xy+y^2), Q3 = -(x+y)^2-z^2
 ******************************************************************************/

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

// =========================================================================
// Try all 6 bitangent products as Q1' targets
// =========================================================================
targets := [
    <L1*L2, "L1*L2">, <L3*L4, "L3*L4">,
    <L1*L3, "L1*L3">, <L2*L4, "L2*L4">,
    <L1*L4, "L1*L4">, <L2*L3, "L2*L3">
];

printf "=== WHICH BITANGENT PRODUCTS Q1' ARE IN THE GL2 ORBIT? ===\n\n";

for tgt in targets do
    tv := QtoV(tgt[1]);
    printf "--- Target Q1' = %o = %o ---\n", tgt[2], tgt[1];

    // Q1' = a^2*Q1ref + 2ab*Q2ref + b^2*Q3ref
    // Solve for (a^2, 2ab, b^2) = (alpha, beta, gamma) with alpha*gamma = (beta/2)^2
    // This is a linear system in alpha,beta,gamma + Veronese constraint

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
    // a/b = alpha/(beta/2) = 2*alpha/beta (if beta != 0)
    // or b/a = gamma/(beta/2) = 2*gamma/beta
    printf "  ON Veronese conic! Finding a,b...\n";

    if beta ne 0 then
        // a/b = 2*alpha/beta.  Let r = a/b.
        r := 2*alpha/beta;
        // b^2 = gamma, so b = sqrt(gamma)
        PK<xx> := PolynomialRing(K);
        fgamma := Factorization(xx^2 - gamma);
        b_val := K!0;
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
        // beta = 0: ab = 0.  Either a=0 or b=0.
        if gamma eq 0 then
            // b=0: Q1' = alpha*Q1.  a^2=alpha.
            PK<xx> := PolynomialRing(K);
            falpha := Factorization(xx^2 - alpha);
            a_val := K!0;
            for pair in falpha do
                if Degree(pair[1]) eq 1 then
                    a_val := -Evaluate(pair[1], 0)/LeadingCoefficient(pair[1]);
                    break;
                end if;
            end for;
            if a_val eq 0 then printf "  No sqrt(alpha) in Q(zeta_8)\n\n"; continue; end if;
            b_val := K!0;
        else
            // a=0: Q1' = gamma*Q3.  b^2=gamma.
            PK<xx> := PolynomialRing(K);
            fgamma := Factorization(xx^2 - gamma);
            b_val := K!0;
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

    // Now complete g = [[a,b],[c,d]] with det^2 = 1.
    // Try c=0: det = ad. Need d with (ad)^2=1, i.e., d = +-1/a or +-i/a
    // But if a=0, try d=0 instead.
    found := false;
    for c_val in [K!0] do
        if a_val eq 0 then continue; end if;
        for d_try in [K!1/a_val, -K!1/a_val, im/a_val, -im/a_val] do
            det := a_val*d_try - b_val*c_val;
            if det^2 eq 1 then
                d_val := d_try;
                // Compute full triple
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
        if found then break; end if;
    end for;

    // Also try d=0 for cases where c=0 didn't work or a=0
    if not found then
        for d_val in [K!0] do
            if b_val eq 0 then continue; end if;
            // det = -b*c.  Need c with (bc)^2=1, i.e., c=+-1/b or +-i/b
            for c_try in [K!1/b_val, -K!1/b_val, im/b_val, -im/b_val] do
                c_val := c_try;
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
            if found then break; end if;
        end for;
    end if;

    if not found then
        printf "  Could not find g with det^2=1 over Q(zeta_8)\n";
    end if;
    printf "\n";
end for;

quit;
