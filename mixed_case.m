/*******************************************************************************
 * mixed_case.m
 *
 * Purpose:
 *   Alternative implementation of BasketByAPairOfGens using double cosets.
 *   This is a more efficient version for certain group types.
 *
 * Function:
 *   - BasketByAPairOfGens(group, gen1, gen2): Compute singular point basket
 *     from a pair of generators using double coset decomposition
 *
 * Method:
 *   Uses double coset representatives H\G/K where H = <gen2> and K = <gen1>
 *   to efficiently enumerate the singular points, rather than iterating
 *   over all cosets.
 *
 * Output:
 *   Returns both the basket of singularities (as rationals) and the
 *   corresponding group elements.
 *
 * Dependencies:
 *   None (standalone function)
 *
 * Note:
 *   This is an alternative to the version in invariants.m, optimized for
 *   PC groups using Transversal instead of DoubleCosetRepresentatives.
 ******************************************************************************/

BasketByAPairOfGens:= function(group,gen1,gen2)
ord1 := Order(gen1); ord2 := Order(gen2);
basket := [ ]; els:=[];
delta := GCD(ord1, ord2);
if delta eq 1 then return {* *}; end if;
alpha2 := ord2 div delta;
H := sub<group | gen2>; K := sub<group | gen1>;
if Type(H) eq GrpPC then
RC := Transversal(group, H, K);
else RC := DoubleCosetRepresentatives(group, H, K);
end if;
for g in RC do
HgK := H^g meet K;
ord_HgK := #HgK;
if ord_HgK eq 1 then continue g; end if;
x := gen1^(ord1 div ord_HgK);
y := (gen2^(ord2 div ord_HgK))^g;
if exists(i){i:i in [1..delta] | y^i eq x} then

d2 := (i*(ord2 div ord_HgK)) div alpha2;
Append(~basket, d2/delta);
Append(~els,g);
end if;
end for;
return basket,els;
end function;