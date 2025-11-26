/*******************************************************************************
 * test_wilson_operators.m
 *
 * Purpose:
 *   Implement Wilson moves on spherical generators. Wilson moves are
 *   operations that transform one spherical generating set to another
 *   while preserving certain properties.
 *
 * Functions:
 *   - wilson_move(seq, j): Apply Wilson move raising generators to power j
 *   - cyclic_shift(seq, k): Rotate sequence by k positions
 *   - wilson_moves(seq, l): Iterate over cyclic shifts and Wilson moves
 *
 * Method:
 *   Given seq = [g1, g2, g3] with g1*g2*g3 = 1, the Wilson move by j gives
 *   [g1^j, g2^j, (g1^j * g2^j)^(-1)], which is valid when j is coprime to
 *   the orders of g1 and g2.
 *
 * Example:
 *   Uses the genus 17 Hurwitz curve (order 1344 automorphism group) to
 *   demonstrate Wilson moves and check for outer automorphisms.
 *
 * Dependencies:
 *   None (standalone computation)
 *
 * Mathematical background:
 *   Wilson moves correspond to automorphisms of the fundamental group of
 *   a punctured sphere. Combined with cyclic shifts, they generate the
 *   action of the mapping class group on conjugacy classes of covers.
 ******************************************************************************/

S := SymmetricGroup(14);
P := S!(1, 13, 2, 11, 4, 5, 8)(3, 10, 6, 14, 7, 9, 12);
Q := S!(1, 7, 3, 4)(2, 11, 13, 9, 6, 14, 10, 5);

G := sub<S | P,Q>;
T := P^3*Q;
U := P^2*Q;
seq := [T,U,(T*U)^(-1)];

A := AutomorphismGroup(G);

a := A.6;
print "a is an inner automorphism: ", IsInner(a);

for g in G do
    if (a(seq[1]))^g eq seq[1]^5 and (a(seq[2]))^g eq (seq[2])^5 then
        print g;
        print "FOUND";
    end if;
end for;


if false then
// Hurwitz curve of genus 14
G := SmallGroup(1092, 25);

seq := [
    G ! (1, 2)(3, 4)(5, 8)(6, 9)(7, 12)(13, 14),
    G ! (1, 11, 8)(2, 9, 3)(4, 13, 6)(10, 14, 12),
    G ! (1, 5, 8, 11, 2, 4, 9)(3, 6, 14, 10, 7, 12, 13)
];
end if;


wilson_move := function(seq, j) // must have j coprime to order of seq[1] and seq[2]
    if Gcd(j, Order(seq[1])) eq 1 and Gcd(j, Order(seq[2])) eq 1 then
        return [seq[1]^j, seq[2]^j, (seq[1]^j * seq[2]^j)^(-1)];
    else
        error "j must be coprime to order of seq[1] and seq[2]";
    end if;
end function;

cyclic_shift := function(seq, k) // rotate seq by k positions
    return seq[(k+1)..#seq] cat seq[1..k];
end function;

// rotate seq by l positions and then iterate over all wilson moves
wilson_moves := function(seq, l)
    for i in [1..l] do
        print "--------------------------------";
        seq := cyclic_shift(seq, 1);
        print seq;
        for j in [1..LCM(Order(seq[1]), Order(seq[2]))] do // check if the j is coprime to order of seq[1] and seq[2]
            if Gcd(j, Order(seq[1])) eq 1 and Gcd(j, Order(seq[2])) eq 1 then
                print i, j;
                new_seq := wilson_move(seq, j);
                print [Order(s) : s in new_seq];
                is_isomorphic := false;
                for g in G do
                    if (a(new_seq[1]))^g eq seq[1] and (a(new_seq[2]))^g eq seq[2] then
                        is_isomorphic := true;
                    end if;
                end for;
                for g in G do
                    if (new_seq[1])^g eq seq[1] and (new_seq[2])^g eq seq[2] then
                        is_isomorphic := true;
                    end if;
                end for;
                print "Is Isomorphic: ", is_isomorphic;
                print "New sequence generates: ", Order(sub< G | new_seq>) eq Order(G);
                print "New sequence satisfies spherical relation:", Order(&* new_seq) eq 1;
            end if;
        end for;
    end for;
    return 0;
end function;

wilson_moves(seq, 3);
