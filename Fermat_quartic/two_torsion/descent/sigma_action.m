/*******************************************************************************
 * sigma_action2.m
 *
 * Determine the sigma-action on Aut(D) using the Frobenius approach.
 * Work over F_{p^2} where p ≡ 2 mod 3, so Frobenius acts as w -> -w.
 *
 * Also compute group-theoretic data to constrain the sigma-action.
 ******************************************************************************/

// === Part 1: Group theory of G = C2^2.SL(2,3) ===
// Use SmallGroup to construct G abstractly and compute invariants
printf "=== Part 1: Abstract group theory ===\n\n";

// C2^2.SL(2,3) has order 96. Find it in the small groups database.
// We know: order 96, center C2, quotient by center = C4^2:C3
found := false;
for i in [1..NumberOfSmallGroups(96)] do
    H := SmallGroup(96, i);
    if #Center(H) eq 2 and GroupName(H) eq "C2^2.SL(2,3)" then
        printf "Found: SmallGroup(96, %o) = %o\n", i, GroupName(H);
        printf "  Center = %o\n", GroupName(Center(H));

        Q := H / Center(H);
        printf "  H/Z(H) = %o, order %o\n", GroupName(Q), #Q;
        printf "  Ab(H) = %o\n", AbelianQuotientInvariants(H);
        printf "  Ab(H/Z(H)) = %o\n", AbelianQuotientInvariants(Q);

        // Hom(H/Z(H), Z/2Z) = Hom(Ab(H/Z(H)), Z/2Z)
        ab_Q := AbelianQuotientInvariants(Q);
        hom_dim := #[x : x in ab_Q | x mod 2 eq 0];
        printf "  dim Hom(H/Z(H), Z/2Z) = %o\n", hom_dim;

        // Aut(H)
        AutH := AutomorphismGroup(H);
        printf "  |Aut(H)| = %o\n", #AutH;
        printf "  |Out(H)| = %o\n", #AutH div (#H div #Center(H));

        found := true;
        break;
    end if;
end for;

if not found then
    printf "Trying all groups of order 96 with center C2...\n";
    for i in [1..NumberOfSmallGroups(96)] do
        H := SmallGroup(96, i);
        if #Center(H) eq 2 then
            printf "SmallGroup(96,%o): %o, center=%o\n",
                i, GroupName(H), GroupName(Center(H));
        end if;
    end for;
end if;

// === Part 2: Frobenius approach at p=5 ===
printf "\n=== Part 2: Frobenius at p=5 over F_25 ===\n\n";
p := 5;
Fp2 := GF(p^2);
w := Sqrt(Fp2!(-3));
printf "p=%o, F_%o, w=sqrt(-3)=%o, w^%o=%o (should be -w=%o)\n",
    p, p^2, w, p, w^p, -w;
assert w^p eq -w;

// Function field of C over F_25
Fpt<t> := FunctionField(Fp2);
Ku<u> := PolynomialRing(Fpt);
fC := u^4 + t^4 + 1;
printf "C: u^4+t^4+1, irreducible? %o\n", IsIrreducible(fC);

if IsIrreducible(fC) then
    FC<uu> := FunctionField(fC);
    printf "Genus(C) = %o\n", Genus(FC);

    q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
    Kv<v> := PolynomialRing(FC);
    fD := v^2 - q1;
    printf "D: v^2=q1, irreducible? %o\n", IsIrreducible(fD);

    if IsIrreducible(fD) then
        FD<vv> := FunctionField(fD);
        printf "Genus(D) = %o\n\n", Genus(FD);

        printf "Computing Aut(D/F_25)...\n";
        time A, mp := AutomorphismGroup(FD);
        printf "|Aut(D)| = %o\n", #A;

        phi, G := CosetAction(A, sub<A | Id(A)>);
        printf "GroupName = %o\n\n", GroupName(G);

        // Find deck involution
        deck_G := Identity(G);
        for g in G do
            if Order(g) ne 2 then continue; end if;
            a := g @@ phi;
            aut := mp(a);
            if aut(vv) eq -vv and aut(FD!uu) eq FD!uu then
                deck_G := g;
                break;
            end if;
        end for;
        printf "Deck involution found, in center? %o\n\n", deck_G in Center(G);

        // === Frobenius action ===
        // The p-Frobenius on F_{p^2} sends x -> x^p.
        // For an automorphism alpha of D, the Frobenius conjugate is:
        // alpha^Frob: same map but with all F_{p^2}-coefficients raised to p-th power.
        //
        // In the function field FD, elements are expressed as a + b*vv where a,b in FC.
        // Elements of FC are c0 + c1*uu + c2*uu^2 + c3*uu^3 where ci in F_{p^2}(t).
        //
        // To apply Frobenius to an element of FD: raise all F_{p^2} coefficients to p.
        // This sends w -> w^p = -w.

        printf "=== Computing Frobenius action on Aut(D) ===\n";

        // Define Frobenius on F_{p^2}
        frob := map<Fp2 -> Fp2 | x :-> x^p>;

        // Apply Frobenius to an element of Fpt = F_{p^2}(t)
        function FrobFpt(elt)
            n := Numerator(elt);
            d := Denominator(elt);
            Kpol := Parent(n);
            fn := Kpol ! [frob(Coefficient(n, i)) : i in [0..Degree(n)]];
            fd := Kpol ! [frob(Coefficient(d, i)) : i in [0..Degree(d)]];
            return Fpt ! (fn / fd);
        end function;

        // Apply Frobenius to an element of FC
        function FrobFC(elt)
            coeffs := Eltseq(elt);
            return &+[FC ! FrobFpt(coeffs[i]) * uu^(i-1) : i in [1..#coeffs]];
        end function;

        // Apply Frobenius to an element of FD
        function FrobFD(elt)
            coeffs := Eltseq(elt);  // [a, b] where elt = a + b*vv
            return &+[FD ! FrobFC(coeffs[i]) * vv^(i-1) : i in [1..#coeffs]];
        end function;

        // For each automorphism alpha of D, compute alpha^Frob:
        // alpha^Frob(x) = Frob(alpha(Frob^{-1}(x)))
        // Since Frob^2 = id on F_{p^2}, Frob^{-1} = Frob.
        // So alpha^Frob(x) = Frob(alpha(Frob(x)))

        // Check: is Frob(q1) = sigma(q1)?
        frob_q1 := FrobFC(q1);
        sq1 := 2*(FC!t)^2 + (1+w)*uu^2 + (1-w);
        printf "Frob(q1) = sigma(q1)? %o\n\n", frob_q1 eq sq1;

        // For each generator of A, compute the Frobenius conjugate
        printf "Computing Frobenius conjugates of generators...\n";
        ngens := Ngens(A);
        frob_images := [];

        for i in [1..ngens] do
            printf "\nGenerator %o:\n", i;
            aut := mp(A.i);

            // Original action
            img_t := aut(FD!t);
            img_u := aut(FD!uu);
            img_v := aut(vv);
            vc := Eltseq(img_v);
            printf "  alpha: t->..., u->..., v->(%o)+(%o)*v\n", vc[1], vc[2];

            // Frobenius conjugate: alpha^Frob(x) = Frob(alpha(Frob(x)))
            // Compute on generators of FD: t, uu, vv
            //
            // alpha^Frob(t):
            // Frob(t) = t (since t is transcendental, Frob only acts on constants)
            // Actually, Frob(t) = t (the indeterminate is fixed, only coefficients change)
            // alpha(t) = img_t
            // Frob(img_t) = FrobFD(img_t)
            frob_img_t := FrobFD(img_t);

            // alpha^Frob(uu):
            frob_img_u := FrobFD(img_u);

            // alpha^Frob(vv):
            // Frob(vv): what is this?
            // vv^2 = q1. Frob(vv)^2 = Frob(q1) = sigma(q1).
            // But vv is in FD where vv^2 = q1, NOT sigma(q1).
            // So Frob(vv) is NOT in FD!
            //
            // The issue: Frobenius maps D to sigma(D), not D to D.
            // We need D to be defined over F_p for Frobenius to act on Aut(D).
            //
            // But D is defined over F_{p^2} when w ∈ F_{p^2}\F_p.
            // Frobenius maps D -> sigma(D), not D -> D.
            // So Frob does NOT give an automorphism of D.
            //
            // To get the sigma-action on Aut(D), we need:
            // sigma_tilde(alpha) = psi_0^{-1} o Frob o alpha o Frob^{-1} o psi_0
            // where psi_0: D -> sigma(D) is the isomorphism.
            //
            // Actually: the sigma-action is just conjugation:
            // sigma_tilde(alpha) is defined by: alpha^sigma is an aut of sigma(D),
            // and sigma_tilde(alpha) = psi_0 o alpha^sigma o psi_0^{-1} : D -> D.
            //
            // alpha^sigma: for each generator of K(sigma(D)),
            // alpha^sigma(x) = Frob(alpha(Frob^{-1}(x)))

            printf "  [Need isomorphism psi_0 to conjugate - computing below]\n";
        end for;

        // === Compute isomorphism psi_0: D -> sigma(D) ===
        printf "\n=== Computing isomorphism D <-> sigma(D) ===\n";

        function HalfDiv(D)
            B := D - D;
            for pl in Support(D) do
                val := Valuation(D, pl);
                if val mod 2 ne 0 then return false, B; end if;
                B := B + (val div 2) * pl;
            end for;
            return true, B;
        end function;

        D_q1 := Divisor(q1);
        D_sq1 := Divisor(sq1);
        ok1, half_q1 := HalfDiv(D_q1);
        ok2, half_sq1 := HalfDiv(D_sq1);
        printf "Half-divisors exist? q1: %o, sigma(q1): %o\n", ok1, ok2;

        if ok1 and ok2 then
            V, rr := RiemannRochSpace(half_q1 - half_sq1);
            dim := Dimension(V);
            printf "dim RR = %o\n", dim;

            if dim eq 0 then
                V, rr := RiemannRochSpace(half_sq1 - half_q1);
                dim := Dimension(V);
                printf "dim RR (other direction) = %o\n", dim;
            end if;

            if dim gt 0 then
                f_func := rr(V.1);
                printf "f found.\n";

                // f^2 * q1 / sigma(q1) should be a constant c
                c_val := f_func^2 * q1 / sq1;
                printf "c = f^2 * q1 / sigma(q1) is constant? ";
                c_coeffs := Eltseq(c_val);
                is_const := (#c_coeffs le 1) or
                    (&and[c_coeffs[i] eq FC!0 : i in [2..#c_coeffs]]);
                printf "%o\n", is_const;

                if is_const then
                    c := c_coeffs[1];
                    printf "c = %o\n\n", c;

                    // psi_0: D -> sigma(D) sends v -> f*v (and t->t, u->u)
                    // On the function field level:
                    // psi_0*: K(sigma(D)) -> K(D) sends sv -> f*v
                    //
                    // sigma_tilde(alpha) = psi_0 o alpha^sigma o psi_0^{-1}
                    //
                    // For alpha with: t -> T, u -> U, v -> C*v (C in FC)
                    // alpha^sigma has: t -> Frob(T), u -> Frob(U), sv -> Frob(C)*sv
                    //   [since Frobenius acts on the formula]
                    //
                    // psi_0^{-1}: v -> (1/f)*sv  [on function fields]
                    //
                    // sigma_tilde(alpha)(v):
                    //   v --(psi_0^{-1})--> (1/f(t,u))*sv
                    //   --(alpha^sigma)--> (Frob(C)(Frob(T),Frob(U)) / f(Frob(T),Frob(U))) * sv
                    //                      ... no wait.
                    //
                    // Actually the Frobenius approach doesn't directly work because
                    // Frobenius maps between D and sigma(D), not within D.
                    //
                    // Let me just compute directly:
                    // sigma_tilde(alpha)(v) = [Frob(C)(t,u) * f(t,u) / f(T,U)] * v
                    //   where T = alpha(t), U = alpha(u) (same for both alpha and sigma_tilde)
                    //   and Frob(C) is C with F_{p^2}-coefficients Frobeniused.

                    printf "=== Sigma-tilde action on generators ===\n";
                    for i in [1..ngens] do
                        printf "\nGenerator %o:\n", i;
                        aut := mp(A.i);
                        img_t := aut(FD!t);  // T in FD
                        img_u := aut(FD!uu); // U in FD
                        img_v := aut(vv);     // C*vv in FD

                        vc := Eltseq(img_v);  // [a, C] where img_v = a + C*vv
                        C_orig := vc[2];       // C in FC

                        // Frobenius of C (on FC)
                        C_frob := FrobFC(C_orig);

                        // f at (t,u) and f at (T,U)
                        // f is in FC. To evaluate f at (T,U), we use the automorphism
                        // that sends t->T, u->U on FC.
                        // Since alpha acts on FD ⊃ FC, we can just apply alpha to f viewed in FD.
                        f_at_TU_FD := aut(FD!f_func);
                        // Extract FC part (should be in FC since f ∈ FC and alpha maps FC to FC)
                        f_at_TU_coeffs := Eltseq(f_at_TU_FD);
                        f_at_TU := f_at_TU_coeffs[1];  // constant term in vv
                        printf "  f(t,u) = ..., f(T,U) = ...\n";

                        // sigma_tilde(alpha) acts as:
                        // t -> T (same as alpha)
                        // u -> U (same as alpha)
                        // v -> [Frob(C) * f / f(T,U)] * v
                        new_C := FD ! (C_frob * f_func / f_at_TU);
                        new_img_v := new_C * vv;
                        printf "  original v-coeff C = %o\n", C_orig;
                        printf "  Frob(C) = %o\n", C_frob;
                        printf "  sigma_tilde v-coeff = %o\n", C_frob * f_func / f_at_TU;

                        // Check if sigma_tilde(alpha) = alpha (i.e., new_C = C_orig)
                        printf "  sigma_tilde = alpha? %o\n", new_C eq FD!C_orig;

                        // If not, check if sigma_tilde(alpha) = iota * alpha
                        printf "  sigma_tilde = iota*alpha? %o\n", new_C eq FD!(-C_orig);

                        // Now identify sigma_tilde(alpha) as an element of G
                        // by checking which element of G has the same action
                        printf "  Identifying sigma_tilde(gen%o) in G...\n", i;
                        sigma_img_t := FrobFD(img_t);
                        sigma_img_u := FrobFD(img_u);

                        target_found := false;
                        for g in G do
                            a := g @@ phi;
                            a_aut := mp(a);
                            if a_aut(FD!t) eq sigma_img_t and
                               a_aut(FD!uu) eq sigma_img_u and
                               a_aut(vv) eq new_img_v then
                                printf "  sigma_tilde(gen%o) = ", i;
                                if g eq Identity(G) then
                                    printf "identity\n";
                                elif g eq deck_G then
                                    printf "deck involution\n";
                                else
                                    printf "element of order %o\n", Order(g);
                                end if;
                                gi := phi(A.i);
                                printf "  gen%o as perm: %o\n", i, gi;
                                printf "  sigma_tilde as perm: %o\n", g;
                                printf "  Same? %o\n", g eq gi;
                                printf "  Differ by deck? %o\n", g eq gi * deck_G;
                                Append(~frob_images, g);
                                target_found := true;
                                break;
                            end if;
                        end for;
                        if not target_found then
                            printf "  WARNING: sigma_tilde image not found!\n";
                            // Debug: check t and u images
                            printf "  Expected t-image: %o\n", sigma_img_t;
                            printf "  Expected u-image: %o\n", sigma_img_u;
                        end if;
                    end for;

                    // If we found both generator images, construct the sigma-action
                    if #frob_images eq ngens then
                        printf "\n=== Sigma-action summary ===\n";
                        gen_perms := [phi(A.i) : i in [1..ngens]];
                        printf "Generators: %o\n", gen_perms;
                        printf "Sigma-images: %o\n", frob_images;
                        same := &and[gen_perms[i] eq frob_images[i] : i in [1..ngens]];
                        printf "Sigma acts TRIVIALLY on Aut(D)? %o\n\n", same;

                        if not same then
                            // Check if sigma is an inner automorphism
                            // i.e., there exists h in G with sigma(g) = h*g*h^-1 for all g
                            printf "Checking if sigma is inner...\n";
                            is_inner := false;
                            for h in G do
                                works := true;
                                for i in [1..ngens] do
                                    if h * gen_perms[i] * h^-1 ne frob_images[i] then
                                        works := false;
                                        break;
                                    end if;
                                end for;
                                if works then
                                    printf "Sigma = conjugation by h (order %o)\n", Order(h);
                                    printf "h = %o\n", h;
                                    printf "h in center? %o\n", h in Center(G);
                                    is_inner := true;
                                    break;
                                end if;
                            end for;

                            if not is_inner then
                                printf "Sigma is an OUTER automorphism of Aut(D).\n";
                            end if;
                        end if;

                        // === Key computation: does g * sigma(g) = iota have a solution? ===
                        printf "\n=== Descent criterion ===\n";
                        printf "Checking: exists g in Aut(D) with g * sigma(g) = iota?\n";
                        descent_possible := false;
                        for g in G do
                            // sigma(g): compute from generators
                            // Actually, we need sigma as a map G -> G
                            // For now, just check if sigma is trivial or inner
                            break;
                        end for;

                        // Construct sigma as a group homomorphism
                        // sigma sends gen_perms[i] -> frob_images[i]
                        // Check if this extends to a well-defined automorphism
                        sigma_map := hom<G -> G | frob_images>;
                        printf "Sigma map well-defined? ";
                        // Verify on all elements (spot check)
                        printf "(checking on generators)\n";
                        for i in [1..ngens] do
                            printf "  sigma(gen%o) = gen%o? %o, or deck*gen%o? %o\n",
                                i, i, sigma_map(gen_perms[i]) eq gen_perms[i],
                                i, sigma_map(gen_perms[i]) eq deck_G * gen_perms[i];
                        end for;

                        printf "\nChecking g * sigma(g) = iota:\n";
                        count := 0;
                        for g in G do
                            if g * sigma_map(g) eq deck_G then
                                count +:= 1;
                                if count le 5 then
                                    printf "  SOLUTION: g of order %o\n", Order(g);
                                end if;
                            end if;
                        end for;
                        printf "Total solutions: %o\n", count;

                        if count gt 0 then
                            printf "\n*** D DESCENDS TO Q AS A CURVE! ***\n";
                        else
                            printf "\n*** D does NOT descend to Q as a curve ***\n";
                        end if;
                    end if;
                end if;
            end if;
        end if;
    end if;
end if;

quit;
