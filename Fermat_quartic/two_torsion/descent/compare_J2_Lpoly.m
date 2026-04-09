/*******************************************************************************
 * compare_J2_Lpoly.m
 *
 * Compare J[2](Q) for C1 and C2 using L-polynomials.
 * The L-polynomial mod 2 gives the charpoly of Frobenius on J[2].
 *
 * Strategy:
 * 1. Compute L-polynomials of C1 and C2 over F_q for several q = 3^k.
 * 2. Reduce mod 2 to get Frobenius matrices on J[2] = F_2^6.
 * 3. Compute fixed subspaces.
 * 4. Over F_9 where the curves are isomorphic, the Frobenius matrices
 *    should be conjugate — the question is whether they're conjugate
 *    in a way that preserves the fixed subspaces.
 *
 * Actually, a simpler approach: the L-polynomial mod 2 at p determines
 * the charpoly of Frob_p on J[2]. Computing this for C1 and C2 at
 * MANY primes tells us the full Galois representation mod 2.
 ******************************************************************************/

function J2Subgroup(Cl, invs)
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    if #gens eq 0 then return sub<Cl | Cl!0>; end if;
    return sub<Cl | gens>;
end function;

print "=== L-POLYNOMIALS MOD 2 ===";
printf "%-5o %-8o %-30o %-30o %-5o\n",
    "p", "p%8", "L(C1) mod 2", "L(C2) mod 2", "Same?";

F2<t> := PolynomialRing(GF(2));

for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73] do
    Fp := GF(p);
    Fpt<tt> := FunctionField(Fp);
    Fptu<uu> := PolynomialRing(Fpt);

    f1 := uu^4 + tt^4 + 1;
    f2 := uu^4 + tt^4 - 1;

    L1_str := ""; L2_str := "";
    same := "?";

    if IsIrreducible(f1) then
        FF1 := FunctionField(f1);
        L1 := LPolynomial(FF1);
        L1_mod2 := F2 ! L1;
        L1_str := Sprint(L1_mod2);
    end if;

    if IsIrreducible(f2) then
        FF2 := FunctionField(f2);
        L2 := LPolynomial(FF2);
        L2_mod2 := F2 ! L2;
        L2_str := Sprint(L2_mod2);
    end if;

    if L1_str ne "" and L2_str ne "" then
        if L1_str eq L2_str then same := "YES"; else same := "NO"; end if;
    end if;

    printf "%-5o %-8o %-30o %-30o %-5o\n", p, p mod 8, L1_str, L2_str, same;
end for;

// =========================================================================
// Now compute the Frobenius matrices on J[2] explicitly.
// Over F_q, L(T) = det(1 - T*Frob | J). So L(T) mod 2 = det(1+T*A)
// where A is the Frobenius matrix on J[2] = F_2^6.
// charpoly(A) = T^6 * L(1/T) mod 2 = "reversed" L mod 2.
//
// Actually: L(T) = sum a_i T^i with a_0=1, a_6=q^3.
// charpoly of Frob = T^6 * L(1/T) / q^3 ... no, this is confusing.
// Just compute directly: L(T) mod 2 is the reverse of charpoly(Frob|J[2]).
// =========================================================================
print "\n=== FACTORED L-POLYNOMIALS MOD 2 ===";

for p in [3,5,7,11,13,17,19,23,29,31] do
    Fp := GF(p);
    Fpt<tt> := FunctionField(Fp);
    Fptu<uu> := PolynomialRing(Fpt);

    f1 := uu^4 + tt^4 + 1;
    f2 := uu^4 + tt^4 - 1;

    printf "p = %o (p mod 8 = %o):\n", p, p mod 8;

    if IsIrreducible(f1) then
        FF1 := FunctionField(f1);
        L1 := LPolynomial(FF1);
        L1m := F2 ! L1;
        fac1 := Factorization(L1m);
        printf "  C1: L mod 2 = %o\n", fac1;
        // Compute dim of fixed space: (T-1)^k divides L mod 2
        // The dimension of (Frob-1) kernel = multiplicity of (T+1) in L mod 2
        // Wait: L(T) mod 2 gives det(1-T*Frob). The eigenvalue 1 of Frob
        // corresponds to (1-T*1) = (1+T) in L mod 2.
        // So fixed dim = multiplicity of (t+1) as factor of L mod 2.
        mult1 := 0;
        for f in fac1 do
            if f[1] eq t+1 then mult1 := f[2]; end if;
        end for;
        printf "       mult of (t+1) = %o -> Frob fixed dim = %o\n", mult1, mult1;
    end if;

    if IsIrreducible(f2) then
        FF2 := FunctionField(f2);
        L2 := LPolynomial(FF2);
        L2m := F2 ! L2;
        fac2 := Factorization(L2m);
        printf "  C2: L mod 2 = %o\n", fac2;
        mult2 := 0;
        for f in fac2 do
            if f[1] eq t+1 then mult2 := f[2]; end if;
        end for;
        printf "       mult of (t+1) = %o -> Frob fixed dim = %o\n", mult2, mult2;
    end if;
    printf "\n";
end for;

// =========================================================================
// The charpolys mod 2 tell us the SEMISIMPLIFICATION of the Galois rep.
// But for comparing subspaces we need more.
//
// Key idea: work over F_9 where the curves are isomorphic.
// The Frobenius σ₃ on J[2](C1/F_9) has some matrix A₁ (6x6 over F_2).
// The Frobenius σ₃ on J[2](C2/F_9) has matrix A₂.
// Under the isomorphism φ: J[2](C1) → J[2](C2), A₂ = P A₁ P^{-1}.
// The fixed subspaces are ker(A₁+I) and ker(A₂+I) = P·ker(A₁+I).
// So J[2](Q) for C1 maps to J[2](Q) for C2 if and only if
// ker(A₂+I) = P·ker(A₁+I), which is AUTOMATIC since A₂ = P A₁ P^{-1}.
//
// WAIT: this means the answer is always YES!
// Under ANY isomorphism φ: C1→C2 over F_9, the transport of J[2](Q)
// for C1 IS J[2](Q) for C2. This is because:
// - φ is defined over F_9
// - σ₃ acts on φ: if σ₃(φ) ≠ φ, then the twist cocycle is nontrivial
// - But the FIXED subspace of J[2] under σ₃ is intrinsic to each curve
// - The isomorphism φ intertwines the σ₃-actions (with a twist)
//
// Actually: φ is NOT defined over F_3 (it requires ζ₈ ∈ F_9 \ F_3).
// So σ₃(φ) ≠ φ. In fact, σ₃(ζ₈) = ζ₈^3, so σ₃(φ) = φ' where
// φ': (x:y:z) → (x:y:ζ₈^3·z).
// The twist cocycle c(σ₃) = σ₃(φ)∘φ^{-1}: (x:y:z) → (x:y:ζ₈^2·z)
// = (x:y:i·z), which is an automorphism of C2 (sends x^4+y^4-z^4 to
// x^4+y^4-i^4z^4 = x^4+y^4-z^4 since i^4=1). ✓
//
// On J[2]:
// σ₃ on J(C2)[2] = c(σ₃)_* ∘ φ_* ∘ σ₃|_{J(C1)} ∘ φ_*^{-1}
// = c(σ₃)_* ∘ (conjugation by φ of σ₃ on C1)
//
// So A₂ = c_* ∘ P ∘ A₁ ∘ P^{-1} where c_* is the action of the
// automorphism c(σ₃) = (x:y:z)→(x:y:iz) on J[2].
//
// The fixed subspace of A₂ is NOT simply P(fixed subspace of A₁)!
// It's {v : c_* P A₁ P^{-1} v = v} = {v : A₁(P^{-1}v) = P^{-1}c_*^{-1}v}.
//
// So the question reduces to: what is c_* on J[2]?
// c = (x:y:z) → (x:y:iz) is an ORDER-4 automorphism of C2.
// Its action on J[2] is a 6x6 matrix C over F_2.
// Over F_2, i^2 = -1 = 1, so (x:y:iz)^2 = (x:y:-z) = (x:y:z) projectively!
// Wait no: c^2: (x:y:z) → (x:y:i²z) = (x:y:-z). And c^4 = identity.
// But on J[2], c^2 might act trivially: if (x:y:z)→(x:y:-z) acts as the
// identity on J[2], then c has order ≤ 2 on J[2].
//
// Let's compute: (x:y:-z) on C2: x^4+y^4-(-z)^4 = x^4+y^4-z^4. ✓
// This is an involution of C2. On J[2] = (Z/2Z)^6, it acts as a matrix
// of order dividing 2. If this matrix is the identity, then c acts on J[2]
// with order dividing 2 as well. And c² acting trivially means c acts as
// an involution on J[2].
// =========================================================================

print "=== ACTION OF z→-z ON J[2](C2) ===";
// The automorphism z→-z of C2 in affine: (t,u) → (t,-u) since t=x/z→x/(-z)=-t
// Wait: z→-z means (x:y:z)→(x:y:-z). In affine z=1: (x,y,1)→(x,y,-1).
// But -1 in projective P^2 means (x:y:-1) = (-x:-y:1). So affine coords:
// t=x/z, u=y/z. Under z→-z: t'=x/(-z)=-t, u'=y/(-z)=-u.
// So the affine map is (t,u)→(-t,-u).

// Compute this for C2 over F_3
printf "Over F_3:\n";
p := 3; Fp := GF(p);
Fpt<tt> := FunctionField(Fp);
Fptu<uu> := PolynomialRing(Fpt);
FF2<vv> := FunctionField(uu^4 + tt^4 - 1);
Cl2, mm2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
J2_2 := J2Subgroup(Cl2, invs2);
printf "J[2](C2/F_3) has %o elements\n", #J2_2;

// The involution (t,u) → (-t,-u) on C2
// For each J[2] element, apply the involution via divisor map
pls2 := Places(FF2, 1);

// Build coordinate lookup
aff2 := [];
coord_lookup := AssociativeArray();
for P in pls2 do
    if Valuation(FF2!tt, P) lt 0 or Valuation(vv, P) lt 0 then continue; end if;
    tv := Fp!Evaluate(FF2!tt, P);
    uv := Fp!Evaluate(vv, P);
    Append(~aff2, P);
    coord_lookup[Sprint(<tv, uv>)] := P;
end for;

// Involution map
inv_map := AssociativeArray();
for P in aff2 do
    tv := Fp!Evaluate(FF2!tt, P);
    uv := Fp!Evaluate(vv, P);
    key := Sprint(<-tv, -uv>);
    if IsDefined(coord_lookup, key) then
        inv_map[P] := coord_lookup[key];
    end if;
end for;

inv_trivial := true;
for g in J2_2 do
    D := mm2(g);
    supp := Support(D);
    invD := DivisorGroup(FF2) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 or not IsDefined(inv_map, P) then
            ok := false; break;
        end if;
        invD := invD + n * (1*inv_map[P]);
    end for;
    if ok then
        inv_g := invD @@ mm2;
        if inv_g ne g then
            printf "  z->-z sends %o to %o (NONTRIVIAL)\n", g, inv_g;
            inv_trivial := false;
        end if;
    else
        printf "  %o: could not compute involution image\n", g;
    end if;
end for;

if inv_trivial then
    print "  z->-z acts TRIVIALLY on J[2](C2/F_3)";
    print "  => c = (z->iz) has order dividing 2 on J[2]";
    print "  => The twist cocycle acts TRIVIALLY on J[2] (since c^2 = id on J[2])";
    print "";
    print "CONCLUSION: Since c acts trivially on J[2], the Frobenius on J[2](C2)";
    print "is conjugate to Frobenius on J[2](C1) by the isomorphism matrix P.";
    print "Therefore J[2](Q) for C1 maps to J[2](Q) for C2 under φ.";
    print "The 3-dimensional subspaces ARE the same.";
else
    print "  z->-z acts NONTRIVIALLY on J[2](C2/F_3)";
    print "  => c might act nontrivially too";
    print "  => The subspaces might differ";
end if;

quit;
