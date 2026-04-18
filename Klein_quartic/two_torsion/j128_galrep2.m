/*******************************************************************************
 * j128_galrep2.m
 *
 * Compute the image of Gal -> GL_2(Z/16) for E = 3200j1 (j=128) by:
 *   1. Tabulating (a_p mod 16, p mod 16) for many primes
 *   2. Checking which (trace, det) pairs mod 16 actually occur
 *   3. In particular: for which det values can trace = 0 mod 16?
 ******************************************************************************/

SetColumns(0);
BOUND := 100000;

QQ := Rationals();
E := MinimalModel(EllipticCurveWithjInvariant(QQ!128));
N := Conductor(E);
printf "E = %o (j=128, conductor %o)\n\n", CremonaReference(E), N;

// Collect (a_p mod 16, p mod 16) pairs
pairs := {};  // set of <a_p mod 16, p mod 16>
trace_by_det := AssociativeArray();  // det mod 16 -> set of traces mod 16
for r in [0..15] do
    trace_by_det[r] := {};
end for;

count_by_pair := AssociativeArray();

for p in PrimesInInterval(5, BOUND) do
    if N mod p eq 0 then continue; end if;
    ap := TraceOfFrobenius(E, p);
    t := ap mod 16;
    if t lt 0 then t +:= 16; end if;
    d := p mod 16;
    Include(~pairs, <t, d>);
    Include(~trace_by_det[d], t);
    key := <t, d>;
    if not IsDefined(count_by_pair, key) then
        count_by_pair[key] := 0;
    end if;
    count_by_pair[key] +:= 1;
end for;

printf "Distinct (trace mod 16, det mod 16) pairs: %o\n\n", #pairs;

// Display: for each det value, which traces occur?
printf "det mod 16 -> traces mod 16 that occur:\n";
for d in [0..15] do
    if #trace_by_det[d] gt 0 then
        printf "  det = %o: traces = %o\n", d, Sort(Setseq(trace_by_det[d]));
    end if;
end for;

// Key question: for which det values does trace = 0 mod 16 occur?
printf "\n=== CRITICAL: det values with trace = 0 mod 16 ===\n";
for d in [0..15] do
    if 0 in trace_by_det[d] then
        ct := IsDefined(count_by_pair, <0, d>) select count_by_pair[<0, d>] else 0;
        printf "  det = %o mod 16: YES (%o occurrences)\n", d, ct;
    end if;
end for;

printf "\n=== det values WITHOUT trace = 0 mod 16 ===\n";
for d in [1,3,5,7,9,11,13,15] do  // only odd det (= primes)
    if not (0 in trace_by_det[d]) then
        printf "  det = %o mod 16: trace = 0 NEVER occurs\n", d;
    end if;
end for;

// Now also check: for trace = 0 exactly (not just mod 16)
// i.e., a_p = 0 (supersingular)
printf "\n=== Supersingular primes (a_p = 0) by p mod 16 ===\n";
ss_by_mod := AssociativeArray();
for r in [0..15] do ss_by_mod[r] := []; end for;
for p in PrimesInInterval(5, BOUND) do
    if N mod p eq 0 then continue; end if;
    ap := TraceOfFrobenius(E, p);
    if ap eq 0 then
        Append(~ss_by_mod[p mod 16], p);
    end if;
end for;
for r in [0..15] do
    if #ss_by_mod[r] gt 0 then
        printf "  p = %o mod 16: %o ss primes", r, #ss_by_mod[r];
        if #ss_by_mod[r] le 10 then
            printf " = %o", ss_by_mod[r];
        end if;
        printf "\n";
    end if;
end for;

// Also check a_p = ±16 (trace = 0 mod 16 but NOT supersingular)
printf "\n=== Primes with a_p = ±16 (trace = 0 mod 16 but not ss) ===\n";
for p in PrimesInInterval(5, BOUND) do
    if N mod p eq 0 then continue; end if;
    ap := TraceOfFrobenius(E, p);
    if (ap eq 16 or ap eq -16) then
        printf "  p=%o: a_p=%o, p mod 16 = %o\n", p, ap, p mod 16;
    end if;
end for;

// Also do mod 8 analysis for comparison
printf "\n=== (trace mod 8, det mod 8) analysis ===\n";
trace_by_det8 := AssociativeArray();
for r in [0..7] do trace_by_det8[r] := {}; end for;
for p in PrimesInInterval(5, BOUND) do
    if N mod p eq 0 then continue; end if;
    ap := TraceOfFrobenius(E, p);
    t := ap mod 8;
    if t lt 0 then t +:= 8; end if;
    d := p mod 8;
    Include(~trace_by_det8[d], t);
end for;
printf "det mod 8 -> traces mod 8:\n";
for d in [0..7] do
    if #trace_by_det8[d] gt 0 then
        printf "  det = %o: traces = %o\n", d, Sort(Setseq(trace_by_det8[d]));
    end if;
end for;

// Full matrix: how many (t, d) pairs for each combination
printf "\n=== Full count matrix (trace mod 16 vs det mod 16) ===\n";
printf "     ";
for d in [1,3,5,7,9,11,13,15] do
    printf "%5o", d;
end for;
printf "\n";
for t in [0..15] do
    printf "t=%2o:", t;
    for d in [1,3,5,7,9,11,13,15] do
        key := <t, d>;
        ct := IsDefined(count_by_pair, key) select count_by_pair[key] else 0;
        if ct gt 0 then
            printf "%5o", ct;
        else
            printf "    .";
        end if;
    end for;
    printf "\n";
end for;

quit;
