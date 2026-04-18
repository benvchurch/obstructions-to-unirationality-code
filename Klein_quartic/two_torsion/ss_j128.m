/*******************************************************************************
 * ss_j128.m
 *
 * Check: are ALL supersingular primes of j=128 congruent to 7 mod 8?
 * Extend the search to a larger bound.
 ******************************************************************************/

SetColumns(0);
BOUND := 100000;

printf "Supersingular primes for j=128 up to %o\n", BOUND;
printf "Checking congruence mod 8...\n\n";

ss := [];
for p in PrimesInInterval(5, BOUND) do
    Fp := GF(p);
    E := EllipticCurveWithjInvariant(Fp!128);
    ap := p + 1 - #E;
    if ap eq 0 then
        Append(~ss, p);
    end if;
end for;

printf "Found %o supersingular primes up to %o\n\n", #ss, BOUND;

// Check congruences
all_7_mod_8 := true;
for p in ss do
    r := p mod 8;
    if r ne 7 then
        printf "*** EXCEPTION: p=%o, p mod 8 = %o ***\n", p, r;
        all_7_mod_8 := false;
    end if;
end for;

if all_7_mod_8 then
    printf "ALL %o supersingular primes are = 7 mod 8\n", #ss;
else
    printf "Some exceptions found!\n";
end if;

// Print them
printf "\nPrimes: %o\n", ss;

// Also check mod 16, mod 24, mod 7, etc. for finer structure
printf "\n--- Residues mod 16 ---\n";
for r in [0..15] do
    ct := #[p : p in ss | p mod 16 eq r];
    if ct gt 0 then printf "  %o mod 16: %o primes\n", r, ct; end if;
end for;

printf "\n--- Residues mod 7 ---\n";
for r in [0..6] do
    ct := #[p : p in ss | p mod 7 eq r];
    if ct gt 0 then printf "  %o mod 7: %o primes\n", r, ct; end if;
end for;

printf "\n--- Residues mod 56 (= 7*8) ---\n";
for r in [0..55] do
    ct := #[p : p in ss | p mod 56 eq r];
    if ct gt 0 then printf "  %o mod 56: %o primes\n", r, ct; end if;
end for;

printf "\n--- Residues mod 3 ---\n";
for r in [0..2] do
    ct := #[p : p in ss | p mod 3 eq r];
    if ct gt 0 then printf "  %o mod 3: %o primes\n", r, ct; end if;
end for;

printf "\n--- Residues mod 24 (= 3*8) ---\n";
for r in [0..23] do
    ct := #[p : p in ss | p mod 24 eq r];
    if ct gt 0 then printf "  %o mod 24: %o primes\n", r, ct; end if;
end for;

// Density: how many primes = 7 mod 8 up to BOUND?
total_7mod8 := #[p : p in PrimesInInterval(5, BOUND) | p mod 8 eq 7];
printf "\n--- Density ---\n";
printf "Total primes 5..%o: %o\n", BOUND, #PrimesInInterval(5, BOUND);
printf "Primes = 7 mod 8: %o\n", total_7mod8;
printf "SS primes of j=128: %o\n", #ss;
printf "Ratio ss/primes_7mod8: %.4o\n", 1.0 * #ss / total_7mod8;

quit;
