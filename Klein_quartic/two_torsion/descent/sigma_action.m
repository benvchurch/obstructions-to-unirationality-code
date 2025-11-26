/*******************************************************************************
 * sigma_action.m
 *
 * Compute the sigma-action (from Gal(Q(sqrt(-3))/Q)) on Aut(D).
 *
 * Strategy: work over F_p^2 where p ≡ 2 mod 3, so that sqrt(-3) ∈ F_p^2 \ F_p
 * and the Frobenius sigma_p acts as w -> -w = w^p.
 * Then Aut(D/F_p^2) = Aut(D/F_p_bar) (for large enough p), and the Frobenius
 * action on Aut(D) corresponds to the Galois action we want.
 *
 * Alternative approach: work over F_p where both w,-w exist, define D and
 * sigma(D) separately, find the isomorphism, and compute the action.
 ******************************************************************************/

// === Part 1: Out(Aut(D)) ===
// First compute Out(G) for G = C2^2.SL(2,3) abstractly
// Use p=13 result to get G as permutation group

p := 13;
Fp := GF(p);
w := Sqrt(Fp!(-3));
printf "=== Computing Aut(D) at p=%o (w=%o) ===\n", p, w;

Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FC<uu> := FunctionField(u^4 + t^4 + 1);
q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
Kv<v> := PolynomialRing(FC);
FD<vv> := FunctionField(v^2 - q1);

printf "Computing Aut(D)...\n";
time A, mp := AutomorphismGroup(FD);
phi, G := CosetAction(A, sub<A | Id(A)>);
printf "|Aut(D)| = %o, structure = %o\n", #G, GroupName(G);
printf "Center = %o\n\n", GroupName(Center(G));

// Compute automorphism group of G
printf "=== Outer automorphism group ===\n";
// Convert to PC group for better Aut computation (G is solvable)
PC, pc_iso := PCGroup(G);
printf "PC group order = %o\n", #PC;
AutPC := AutomorphismGroup(PC);
printf "|Aut(G)| = %o\n", #AutPC;
printf "|Inn(G)| = |G/Z(G)| = %o\n", #G div #Center(G);
out_order := #AutPC div (#G div #Center(G));
printf "|Out(G)| = %o\n\n", out_order;

// === Part 2: sigma-action via direct computation ===
// sigma sends w -> -w. Define sigma(D): v^2 = sigma(q1) on C.
// sigma(q1) = 2t^2 + (1+w)u^2 + (1-w)
printf "=== Direct sigma-action computation ===\n";

sq1 := 2*(FC!t)^2 + (1+w)*uu^2 + (1-w);
Kv2<v2> := PolynomialRing(FC);
sD<svv> := FunctionField(v2^2 - sq1);
printf "Genus(sigma(D)) = %o\n", Genus(sD);

// Compute Aut(sigma(D))
printf "Computing Aut(sigma(D))...\n";
time sA, smp := AutomorphismGroup(sD);
sphi, sG := CosetAction(sA, sub<sA | Id(sA)>);
printf "|Aut(sigma(D))| = %o, structure = %o\n", #sG, GroupName(sG);
printf "IsIsomorphic to Aut(D)? %o\n\n", IsIsomorphic(G, sG);

// Find isomorphism D -> sigma(D) via Riemann-Roch
// f with div(f) = (1/2)div(sigma(q1)) - (1/2)div(q1)
printf "=== Constructing isomorphism D -> sigma(D) ===\n";

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
printf "div(q1) all even? %o, div(sigma(q1)) all even? %o\n", ok1, ok2;

if ok1 and ok2 then
    // f with div(f) = half_sq1 - half_q1
    V, rr := RiemannRochSpace(half_q1 - half_sq1);
    printf "dim L(half_q1 - half_sq1) = %o\n", Dimension(V);

    if Dimension(V) gt 0 then
        f_iso := rr(V.1);
        printf "f = %o\n", f_iso;

        // Verify: f^2 * q1 should equal c * sigma(q1) for some constant c
        ratio := f_iso^2 * q1 / sq1;
        printf "f^2 * q1 / sigma(q1) = %o\n", ratio;
        printf "Is this constant? %o\n\n", Degree(MinimalPolynomial(ratio, Fpt)) le 1;

        // The isomorphism psi_0: D -> sigma(D) sends v -> f*v
        // (i.e., on function fields: sigma(D) -> D maps svv -> f_iso * vv)
        //
        // The sigma-tilde action on Aut(D):
        // For alpha in Aut(D), sigma_tilde(alpha) = psi_0^{-1} o alpha^sigma o psi_0
        //
        // alpha^sigma is the "same" automorphism but of sigma(D):
        // if alpha sends (t, u, v) -> (a(t,u), b(t,u), c(t,u,v)),
        // then alpha^sigma sends (t, u, sv) -> (a(t,u), b(t,u), c(t,u,sv))
        // (just replace w by -w in the coefficients of the automorphism)
        //
        // For the computation, we'll use a different approach:
        // Build an explicit isomorphism between G and sG by matching generators.

        // Find deck involutions of both D and sigma(D)
        deck_G := Identity(G);
        for g in G do
            if Order(g) eq 2 then
                a := g @@ phi;
                aut := mp(a);
                if aut(vv) eq -vv and aut(FD!uu) eq FD!uu then
                    deck_G := g;
                    break;
                end if;
            end if;
        end for;
        printf "Deck involution of D found, order = %o\n", Order(deck_G);

        sdeck_G := Identity(sG);
        for g in sG do
            if Order(g) eq 2 then
                a := g @@ sphi;
                aut := smp(a);
                if aut(svv) eq -svv and aut(sD!uu) eq sD!uu then
                    sdeck_G := g;
                    break;
                end if;
            end if;
        end for;
        printf "Deck involution of sigma(D) found, order = %o\n\n", Order(sdeck_G);

        // Now compute sigma-tilde action on generators of G
        // For each generator g_i of A:
        //   1. Get the automorphism alpha_i = mp(g_i) of D
        //   2. alpha_i acts on FD: t -> alpha_i(t), uu -> alpha_i(uu), vv -> alpha_i(vv)
        //   3. "Conjugate" alpha_i: swap w <-> -w in the images
        //      This gives an automorphism alpha_i^sigma of sigma(D)
        //   4. Conjugate by psi_0: sigma_tilde(alpha_i) = psi_0^{-1} o alpha_i^sigma o psi_0
        //
        // The tricky part is step 3: extracting and conjugating w.
        // Over F_p, w is just a field element, so "conjugating" means
        // applying the F_p-linear map that sends w -> -w.
        // But w is in F_p (not F_p^2), so this map is NOT a field automorphism!
        //
        // Alternative approach: use F_p^2 with p ≡ 2 mod 3

        printf "=== Note: sigma-action via coordinate swap ===\n";
        printf "Since w and -w are both in F_p, the 'sigma' operation\n";
        printf "is a substitution in the defining equations, not a field\n";
        printf "automorphism. We compute it by defining a map on coordinates.\n\n";

        // For the Fermat quartic C, sigma acts trivially (C is defined over Q).
        // So sigma acts on Aut(C) by conjugating coefficients.
        // The automorphisms of C involve 4th roots of unity (i = sqrt(-1))
        // and permutations. Over Q, sigma_{sqrt(-3)} does NOT affect sqrt(-1).
        // So sigma acts trivially on Aut(C)!
        //
        // For D -> C, the deck involution iota is canonical (doesn't depend on w).
        // So sigma also fixes iota.
        //
        // The full sigma-action on Aut(D): since the projection
        // Aut(D) -> Aut(C)_eta is compatible with sigma, and sigma acts
        // trivially on both the kernel Z/2Z and the quotient Aut(C)_eta,
        // the sigma-action on Aut(D) is trivial by ... well, not necessarily.
        // It could be a non-trivial inner automorphism.

        // Let me just compute it by matching automorphisms.
        // For each generator of G, compute its action on the function field of D.
        // Then do the same with w -> -w for sigma(D).
        // Then use f_iso to conjugate back to D.

        printf "Computing sigma-action on Aut(D) generators...\n";
        ngens := Ngens(A);
        printf "Number of generators of A: %o\n", ngens;

        // For each generator, compute action on FC-coordinates
        for i in [1..ngens] do
            aut := mp(A.i);
            img_t := aut(FD!t);
            img_u := aut(FD!uu);
            img_v := aut(vv);
            printf "Gen %o:\n", i;
            printf "  t -> %o\n", img_t;
            printf "  u -> %o\n", img_u;
            // v image is in FD, express as a + b*vv where a,b in FC
            v_coeffs := Eltseq(img_v);
            printf "  v -> (%o) + (%o)*v\n", v_coeffs[1], v_coeffs[2];
        end for;

    else
        printf "RR space is 0-dimensional. Trying other divisor...\n";
        V, rr := RiemannRochSpace(half_sq1 - half_q1);
        printf "dim L(half_sq1 - half_q1) = %o\n", Dimension(V);
        if Dimension(V) gt 0 then
            f_iso := rr(V.1);
            printf "f = %o\n\n", f_iso;
        end if;
    end if;
else
    printf "Half-divisors don't exist, trying alternative...\n";
end if;

quit;
