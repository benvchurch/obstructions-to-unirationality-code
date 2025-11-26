/*******************************************************************************
 * explicit_auts.m
 *
 * Explicitly construct automorphisms of D: v^2 = q1 on C: u^4+t^4+1=0.
 *
 * Strategy: each aut of C lifts to D iff q1(alpha(t,u))/q1(t,u) is a square
 * in the function field of C. If it lifts, we get 2 lifts (v -> +-c*v).
 *
 * Aut(C) for Fermat quartic: monomial maps (x:y:z) -> (zeta4^a x_s(1) : ...)
 * In affine coords (t,u) = (x/z, y/z), C: t^4+u^4+1=0.
 *
 * We test all 96 automorphisms of C.
 ******************************************************************************/

primes := [13, 19, 37];

for p in primes do
    Fp := GF(p);
    has_sqrt3 := IsSquare(Fp!(-3));
    has_sqrt1 := IsSquare(Fp!(-1));
    if not has_sqrt3 then continue; end if;
    w := Sqrt(Fp!(-3));
    printf "=== p = %o (sqrt(-1)? %o) ===\n", p, has_sqrt1;

    // Function field of C
    Fpt<t> := FunctionField(Fp);
    Ku<u> := PolynomialRing(Fpt);
    FC<uu> := FunctionField(u^4 + t^4 + 1);
    elt_t := FC!t;
    elt_u := uu;

    q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);

    // Automorphisms of C in affine coords (t,u):
    // Projective: (x:y:z) -> (a*x_s1 : b*x_s2 : x_s3)
    // where s in S3, a^4=b^4=1
    // Affine: (t,u) = (x/z, y/z). If z goes to x_s3, then:
    //   new_t = a*x_s1/x_s3, new_u = b*x_s2/x_s3
    // where x=t*1, y=u*1, z=1

    // Build all 4th roots of unity in Fp (or Fp2 if needed)
    // Only +-1 if sqrt(-1) doesn't exist
    if has_sqrt1 then
        i_val := Sqrt(Fp!(-1));
        roots4 := [Fp!1, i_val, Fp!(-1), -i_val];
    else
        roots4 := [Fp!1, Fp!(-1)];
    end if;

    // Permutations of (x,y,z) = (t,u,1):
    // s = id: (t,u,1)
    // s = (12): (u,t,1)
    // s = (13): (1,u,t) -> affine (1/t, u/t)
    // s = (23): (t,1,u) -> affine (t/u, 1/u)
    // s = (123): (u,1,t) -> affine (u/t, 1/t)
    // s = (132): (1,t,u) -> affine (1/u, t/u)

    // For each permutation, give the new (t', u') as functions of (t, u)
    // s = id:   new_z = 1,   new_t = t/1 = t,   new_u = u/1 = u
    // s = (12): new_z = 1,   new_t = u,          new_u = t
    // s = (13): new_z = t,   new_t = 1/t,        new_u = u/t
    // s = (23): new_z = u,   new_t = t/u,        new_u = 1/u
    // s = (123): new_z = t,  new_t = u/t,        new_u = 1/t
    // s = (132): new_z = u,  new_t = 1/u,        new_u = t/u

    perms := [
        <"id",   elt_t, elt_u, FC!1>,     // z=1
        <"(12)", elt_u, elt_t, FC!1>,     // z=1
        <"(13)", FC!1/elt_t, elt_u/elt_t, elt_t>,  // z=t
        <"(23)", elt_t/elt_u, FC!1/elt_u, elt_u>,  // z=u
        <"(123)", elt_u/elt_t, FC!1/elt_t, elt_t>,  // z=t
        <"(132)", FC!1/elt_u, elt_t/elt_u, elt_u>   // z=u
    ];

    lift_count := 0;

    for perm in perms do
        name := perm[1];
        base_t := perm[2];
        base_u := perm[3];
        base_z := perm[4];
        for a in roots4 do
            for b in roots4 do
                // The automorphism sends (x:y:z) -> (a*x_s1 : b*x_s2 : x_s3)
                // In affine: new_t = a * base_t, new_u = b * base_u
                // But wait: we also need to scale. The projective map is:
                // (x':y':z') = (a*f1(x,y,z) : b*f2(x,y,z) : f3(x,y,z))
                // Affine: t' = a*f1/f3, u' = b*f2/f3
                new_t := a * base_t;
                new_u := b * base_u;

                // Check: this should be an aut of C, i.e., new_t^4 + new_u^4 + 1 = 0
                // (after dividing by z'^4)
                // Actually: (new_t)^4 + (new_u)^4 + 1 = a^4*base_t^4 + b^4*base_u^4 + 1
                // = base_t^4 + base_u^4 + 1 (since a^4=b^4=1)
                // And base_t = f1/f3, base_u = f2/f3, so
                // base_t^4 + base_u^4 + 1 = (f1^4+f2^4+f3^4)/f3^4
                // = (x^4+y^4+z^4)/f3^4 (since the permutation just rearranges)
                // But x^4+y^4+z^4 = t^4+u^4+1 = 0 on C.
                // So new_t^4 + new_u^4 + 1 = 0. Good.

                // Compute q1 at the new point
                q1_new := 2*new_t^2 + (1-w)*new_u^2 + (1+w);
                ratio := q1_new / q1;

                // Check if ratio is a perfect square in FC
                if IsSquare(ratio) then
                    lift_count +:= 1;
                end if;
            end for;
        end for;
    end for;

    // Total: lift_count monomial auts that lift.
    // Each lifts to 2 auts of D (v -> +-sqrt(ratio)*v).
    printf "  Monomial auts of C over F_%o: %o\n", p, #roots4^2 * 6;
    printf "  Of these, %o preserve the double cover (q1_new/q1 is a square)\n", lift_count;
    printf "  |Aut(D)| = 2 * %o = %o\n\n", lift_count, 2*lift_count;
end for;

quit;
