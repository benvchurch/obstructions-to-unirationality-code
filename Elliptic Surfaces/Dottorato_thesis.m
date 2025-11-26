// Input: Ksquare and p_g; we are assuming q=0.
//
// Step 1: the baskets.
//
// We start finding, for each K^2 and p_g,
// what are the possible baskets of
// singularities of X=(CxC)/G. By Lemma 5.2.5 the sum
// of the invariants B of the singularities must
// be equal to 3(8-K^2).
//
// We will represent the singular points of type
// C_{n,a} or D_{n,a} by the rational number
// a/n in two different multisets;
// a basket of singularities will be a pair of multisets
// of rational numbers.
//
// Remembering that cyclic quotient singularities C_{n,a}
// and C_{n,a’} are isomorphic if a*a’=1 mod n, we consider
// rational numbers in (0,1) modulo the equivalence
// relation a/n ~ a’/n.
//
// We see the entries of the continuous fraction of n/a
// as the sequence [b_1,...,b_r]. Note that the continuous
// fraction of n/a’ is the sequence [b_r,...,b_1].
//
// This can be seen as a bijection between rational numbers
// in (0,1) and sequences of integers strictly bigger than 1.
// We make this bijiection explicit by the following scripts.
ContFrac:=function(s)
CF:=[ ]; r:=1/s;
while not IsIntegral(r) do
Append(~CF, Ceiling(r)); r:=1/(Ceiling(r)-r);
end while;
return Append(CF, r);
end function;
Nq:=func<cf|#cf eq 1 select cf[1] else cf[1]-
1/$$(Remove(cf,1))>;

RatNum:=func<seq|1/Nq(seq)>;
// "Wgt" computes the weight of a sequence.
// It bounds strictly from below B of the corresponding
// singular point of type C_{n,a}; and 2*B-12 for D_{n,a}.
Wgt:=function(seq)
w:=0; for i in seq do w+:=i; end for; return w;
end function;
// The next script computes all rational number whose
// continuous fraction has small weight.
RatNumsWithSmallWgt:=function(maxW)
S:={ }; T:={}; setnums:={RationalField()| };
for i in [2..maxW] do Include(~S, [i]); end for;
for i in [1..Floor(maxW/2)-1] do
for seq in S do
if #seq eq i then
if maxW-Wgt(seq) ge 2 then
for k in [2..maxW-Wgt(seq)] do
Include(~S,Append(seq, k));
end for; end if; end if;
end for; end for;
for seq in S do
if Reverse(seq) notin T then Include(~T,seq);
end if; end for;
for seq in T do Include(~setnums, RatNum(seq)); end for;
return setnums;
end function;
// The next 4 scripts compute the invariants B and e
// of singular points of type C and D respectively (r=a/n).
InvBC:=func<r|Wgt(ContFrac(r))+r+RatNum(Reverse(ContFrac(r)))>;
InveC:=func<r|#ContFrac(r)+1-1/Denominator(RationalField()!r)>;
InvBD:=func<r|InvBC(r)/2 +6>;
InveD:=func<r|InveC(r)/2 +3>;
// The next two scripts compute the invariants B and e of

// a pair of multisets of rational numbers
// (corresponding to a basket of singular points).
InvBSet:= function(basketC, basketD)
B:=0; for r in basketC do B+:=InvBC(r); end for;
for r in basketD do B+:=InvBD(r); end for;
return B;
end function;
InveSet:= function(basketC, basketD)
e:=0; for r in basketC do e+:=InveC(r); end for;
for r in basketD do e+:=InveD(r); end for;
return e;
end function;
// Here is the invariant k of the basket:
InvkSet:=func<r,s|InvBSet(r,s)-2*InveSet(r,s)>;
// The next script computes all rational numbers with
// weight bounded from above by maxW, as computed by
// RatNumsWithSmallWgt, and returns them in a sequence
// ordered by the value of their invariant B,
// starting from the one with biggest B.
OrderedRatNums:=function(maxW)
seq:=[RationalField()| ]; seqB:=[RationalField()| ];
set:=RatNumsWithSmallWgt(Floor(maxW));
for r in set do i:=1;
for s in seqB do
if s gt InvBC(r) then i+:=1;
else break s;
end if; end for;
Insert(~seq, i, r); Insert(~seqB, i, InvBC(r));
end for;
return seq;
end function;
// The next one, CutSeqByB, takes a sequence "seq" and
// recursively removes the first element if its invariant B
// is at least maxB.
CutSeqByB:=function(seq,maxB)
Seq:=seq;

while #Seq ge 1 and InvBC(Seq[1]) gt maxB do
Remove(~Seq,1); end while;
return Seq;
end function;
// Now we have a way to compute the set of rationals with
// B bounded by the integer maxB, ordered by B:
// CutSeqByB(OrderedRatNums(maxB-1),maxB)
//
// The next script takes a sequence of rational numbers
// ordered by B and computes the baskets with invariant
// exactly B that use only these rationals.
// The function is as follows:
// - first it removes the elements with B too big to be
// in a basket;
// - then it takes the first element, say r, if B(r)=B,
// it stores {* r *};
// - else it attaches it to each basket with invariant
// B-B(r) (computed recalling the function with the
// same sequence) and store the result;
// - now we have all baskets containing r: remove r
// from the sequence and repeat the procedure until
// the sequence is empty.
BasketsWithSeqAndB:=function(seq,B)
ratnums:=CutSeqByB(seq,B); baskets:={ };
while #ratnums gt 0 do
bigguy:=ratnums[1];
if InvBC(bigguy) eq B then
Include(~baskets,{* bigguy *});
else for basket in $$(ratnums, B-InvBC(bigguy)) do
Include(~baskets, Include(basket, bigguy));
end for; end if;
Remove(~ratnums,1);
end while;
return baskets;
end function;
// Now we can compute all the "C-parts" (of baskets) with
// a given B:
PartsOfTypeC:=func<B|BasketsWithSeqAndB(OrderedRatNums(B),B)>;
// Next script computes all the possible "D-parts"

// with a given B and p_g:
PartsOfTypeD:=function(B,pg)
singD:={ }; basketD:={ };
D:=RatNumsWithSmallWgt(2*B-27);
for r in D do
if InvBD(r)le B then
if IsIntegral(Denominator(RationalField()!r)/2) then
if ContFrac(r) eq Reverse(ContFrac(r)) then
if IsIntegral((#ContFrac(r)+1)/2) then
if IsIntegral(ContFrac(r)[IntegerRing()!((#ContFrac(r)+1)/2)]/2) then
Include(~singD,r);
end if;end if;end if;end if;end if;
end for;
for d in { 2*x: x in { 0..(2*pg+1) }} do
for s in Multisets({ x: x in singD},d) do
if InvBSet({* *},s) le B then
Include(~basketD,s);
end if;
end for; end for;
return basketD;
end function;
// We do not need all these baskets, since most of them
// violate Corollary 5.1.14 or Lemma 5.2.16.
// The next scripts take care of this:
// "BasketOfY" computes the basket of the surface Y starting
// from the basket of X.
// "TestBasket" checks if a basket violates Corollary 5.1.14;
// "TestDen" checks if a basket respects Lemma 5.2.16;
//
// "Basket" constructs all the basket with given B and
// removes all the baskets which violate the conditions.
BasketOfY:=function(basketX)
basketY:={**};
for r in basketX[1] do
Include(~basketY, r);
Include(~basketY, RatNum(Reverse(ContFrac(r))));
end for;
for r in basketX[2] do Include(~basketY, r); end for;
return basketY;
end function;

TestBasket:=function(basketC, basketD)
S:=0; test:=false;
for r in BasketOfY([basketC, basketD]) do
S+:= r; end for;
if IsIntegral(S) then test:=true;
end if;
return test;
end function;
TestDen:=function(chi, BC,BD)
test:=true; xi:= 4*chi+(InvkSet(BC,BD)-InveSet(BC,BD))/3;
for r in Set(BC join BD) do
if Denominator(RationalField()!r) ge 12*(2*xi+1) then
test:=false; break r;
end if; end for;
return test;
end function;
Baskets:=function(Ksquare,pg)
baskets:=[**]; chi:=1+pg;
B:=3*(8*chi-Ksquare);
for partD in PartsOfTypeD(B,pg) do
if (InvBSet({**},partD) eq B) and TestBasket({* *}, partD)
then Append(~baskets, [{* *}, partD]); end if;
for partC in PartsOfTypeC(B-InvBSet({* *},partD)) do
if TestBasket(partC, partD) then
if TestDen(chi,partC,partD) then
Append(~baskets, [partC, partD]); end if; end if;
end for; end for;
return baskets;
end function;
// Step 2: the signatures
//
// Now we have found, for each K^2, a finite number of
// possible baskets. Proposition 5.2.13 says that once
// we fix K^2, p_g and a basket of singularities,
// there are finitely many possible signatures satisfying
// all the condition of the proposition.
//
// The next step is to compute, for each basket, the
// signatures. We will represent a signature as
// a multiset of natural numbers {* m_i *}.
//

// We first define the index of a basket of singularities
// as the lowest common multiple of the indexes of the
// singularities of type C_{n,a} in BasketOfY.
GI:=func<r|Denominator(r)/GCD(Numerator(r)+1,Denominator(r))>;
GorInd:= function(bas)
I:=1;
for r in bas do I:=LCM(IntegerRing()!I,IntegerRing()!GI(r));
end for; return I;
end function;
// We define the invariants Theta and Beta:
Theta:=function(sig)
a:=-2;
for m in sig do a+:=(1-1/m); end for;
return a;
end function;
Beta:=func<K, B, T | (K+InvkSet(B[1],B[2]))/(2*T)>;
// These two scripts transform a multiset, resp. a tuple
// into a sequence.
MsetToSeq:=function(mset)
seq:=[ ];
while #mset ne 0 do Append(~seq, Minimum(mset));
Exclude(~mset, Minimum(mset)); end while;
return seq;
end function;
TupleToSeq:=function(tuple)
seq:=[];
for el in Tuplist(tuple) do
Append(~seq,el);
end for;
return seq;
end function;
// Next script computes all the divisor (different from 1)
// of a natural number:
Divisors:=function(n)

set:={};
for i in { 2.. n} do
if n/i in IntegerRing() then
Include(~set, i);
end if; end for;
return set;
end function;
// The input of the next script are 5 numbers: CardBasket,
// Length, SBound, HBound (SBound<=HBound) and n,
// and its output are all signatures with
// #signature=Length such that (let M:=max(1/6,(Length-3)/2)
// 1) each m_i is smaller than HBound/M;
// 2) most m_i are smaller than SBound/M, the number of
// exceptions is bounded from above by half of CardBasket.
//
// For sparing time, the script first checks if the length
// is smaller than the number of possible exceptions,
// in which case only the inequality 1 is to consider.
// Moreover, to spare time, since m_i divides n=2*Beta*I,
// the script looks for the m_i’s only among the divisors of n.
CandTypes:=function(CardBasketY,Length,S,H,n)
D:=Divisors(n);
Exc:=Floor(CardBasketY/2);
if Length le Exc then
Types:=Multisets({x: x in D | x in { 2..H}},Length);
else Types:=Multisets({x: x in D | x in { 2..S}},Length);
for k in [1..Exc] do
for TypeBegin in Multisets({x: x in D | x in { 2..S}},Length-k) do
for TypeEnd in Multisets({x: x in D | x in {S+1..H}},k) do
Include(~Types, TypeBegin join TypeEnd);
end for; end for; end for;
end if;
return Types;
end function;
// The function ListTypes calculates all the types that
// fulfill the conditions imposed by Proposition 5.2.13:
ListTypes:=function(Ksquare,pg, basketX)
list:=[]; chi:=1+pg;
BC:=basketX[1]; BD:=basketX[2];
BY:=BasketOfY(basketX);

den:={};
for r in BY do
Include(~den,Denominator(RationalField()!r)); end for;
xi:= 4*chi+(InvkSet(BC,BD)-InveSet(BC,BD))/3;
I:=GorInd(BY); k:=InvkSet(BC,BD);
Rmin:=3; Tmin:=1/42;
Rmax:=Floor((Ksquare + k) +4);
BetaMax:=Floor(Beta(Ksquare,basketX,Tmin));
for R in [Rmin..Rmax] do
if R eq 3 then
top:=Floor(12*(2*xi+1));
else top:=Floor(6+(8*xi+2)/(R-3));
end if;
M:=Max(1/6,(R-3)/2);
SB:=Min(top, Floor((1/M)*(1+(Ksquare+k)/2)));
HB:=Min(top, Floor((1/M)*(1+I*(Ksquare+k))));
for b in { 1..BetaMax} do n:=2*b*I;
for cand in CandTypes(#BY,R,SB,HB,n) do ;
if forall{n : n in den |
exists{m: m in cand| m/n in IntegerRing()}} then
T:=Theta(cand);
if (T le (Ksquare+k)/2) and (T gt 0) then
beta:=Beta(Ksquare,basketX,T);
if IsIntegral(beta) and beta eq b then
if IsIntegral((Ksquare+k)/(T^2)) then
if IsIntegral((4*beta^2)/(Ksquare+k)) then bads:=0;
for n in cand do
if not IsIntegral(beta/n) then bads +:=1;
if bads gt #BY/2 then break cand; end if;
end if; end for;
Append(~list,cand);
end if;end if;end if;end if;end if;
end for;
end for;
end for;
return list;
end function;
// ListOfTypes returns, for given K^2 and p_g, all possible
// baskets (using Baskets) and for each basket all the
// possible types (using ListTypes).
ListOfTypes:=function(Ksquare,pg)
list:=[**]; chi:=1+pg;

B:=3*(8*chi-Ksquare);
for basket in Baskets(Ksquare,pg) do
L:=ListTypes(Ksquare,pg, basket);
if not IsEmpty(L) then
Append(~list,[* basket, L*]);
end if;
end for;
return list;
end function;
// Step 3: calculating the groups.
//
// Fixed K^2, p_g, the basket and the signature,
// using Proposition 5.2.13 we can compute the order
// of the group G^0.
// We search among the group of this order which groups
// have a prescribed set of spherical generators.
ElsOfOrd:=func<group, order | {g: g in group| Order(g) eq order}>;
// TuplesOfGivenOrder creates a sequence of the same length
// as the input sequence seq, whose entries are subsets
// of the group in the input, and precisely the subsets
// of elements of order the corresponding entry of seq.
TuplesOfGivenOrders:=function(group,seq)
SEQ:=[];
for i in [1..#seq] do
if IsEmpty(ElsOfOrd(group,seq[i])) then SEQ:=[]; break i;
else Append(~SEQ,ElsOfOrd(group,seq[i]));
end if; end for;
return SEQ;
end function;
// This script says if a group has a set
// of spherical generators of the given type:
ExSphGens:=function(group,type)
test:=false;
SetCands:=TuplesOfGivenOrders(group,Prune(type));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if Order(&*cands) eq type[#type] then
if #sub<group|TupleToSeq(cands)> eq #group then

test:=true; break cands;
end if; end if; end for; end if;
return test;
end function;
// Polygonal builds the polygonal group of the type given by seq
Polygonal:=function(seq)
F:=FreeGroup(#seq); Rel:={F![1..#seq]};
for i in [1..#seq] do Include(~Rel,F.i^(seq[i])); end for;
return quo<F|Rel>;
end function;
// Test and TestBAD search among all the groups of
// the order in input which groups have a spherical
// system of generators of the type in input.
// These function work in two steps (see Remark 6.2.1):
// i) they check which groups have abelianization
// isomorphic to a quotient of the abelianization
// of the polygonal group given by the type;
// ii) if a group passes the first test the scripts
// check if it has a spherical system of generators
// of the type in input.
// These two scripts make exactly the same controls, and
// we use Test in general, but in some cases there are too
// much isomorphism classes of groups of the given order
// and we use TestBAD because, SmallGroupProcess is slower
// than SmallGroups but it uses less memory.
Test:=function(type, order)
group:=AbelianQuotient(Polygonal(type));
checked:={}; quo:={}; set:={};
for g in Subgroups(group) do
Include(~quo, group/(g`subgroup)); end for;
for h in quo do Include(~set,#h); end for;
i:=1;
for H in SmallGroups(order: Warning:=false) do
if #AbelianQuotient(H) in set then
for p in quo do
if IsIsomorphic(p, AbelianQuotient(H)) then
if ExSphGens(H,type) then
Include(~checked,i); end if;
break p;end if; end for; end if;
i+:=1; end for;

return checked;
end function;
TestBAD:=function(type, order)
group:=AbelianQuotient(Polygonal(type));
checked:={}; quo:={}; set:={};
for g in Subgroups(group) do
Include(~quo, group/(g`subgroup)); end for;
for h in quo do Include(~set,#h); end for;
i:=1; P:= SmallGroupProcess(order);
repeat
H := Current(P);
if #AbelianQuotient(H) in set then
for p in quo do
if IsIsomorphic(p, AbelianQuotient(H)) then
if ExSphGens(H,type) then
Include(~checked,i); end if;
break p;end if; end for; end if;
i+:=1; Advance(~P);
until IsEmpty(P);
return checked;
end function;
// The next script takes a sequence of elements of a group
// and a further element g and conjugates each element
// of the sequence with g.
Conjug:=function(seq,el)
output:=[];
for h in seq do Append(~output,h^el); end for;
return output;
end function;
// SphGenUpToConj computes all possible sets of spherical
// generators of a group of a prescribed type and return
// (to spare memory) only one of these sets for each
// conjugacy class.
SphGenUpToConj:=function(group,seq)
Set:={ }; Rep:={ };
SetCands:=TuplesOfGivenOrders(group,Prune(seq));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if Order(&*cands) eq seq[#seq] then

if Append(TupleToSeq(cands),(&*cands)^-1) notin Set
then if sub<group|TupleToSeq(cands)> eq group then
Include(~Rep, Append(TupleToSeq(cands),(&*cands)^-1));
for g in group do
Include(~Set, Conjug(Append(TupleToSeq(cands),(&*cands)^-1),g));
end for; end if; end if; end if; end for; end if;
return Rep;
end function;
// If a group has a set of spherical generators of the
// right type before to look for an unsplit extension,
// we check if the group has a pair of sets of
// spherical generators that give the right singularities.
// If this is not the case surely a set of spherical
// generators and its conjugation by tau’ in G cannot give
// the right singularities.
//
// Given two sets of spherical generators,
// next script computes the singular points
// coming from a fixed pair (g1,g2), where
// - g_1 is a generator of the first set;
// - g_2 is a generator of the second set;
// and 1<=n_1<=ord(g_1); 1<=n_2<=ord(g_2);
// Moreover, it returns the element g such that
// g_1^n_1= (g_2^n_2)^g.
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
// CheckSingsH checks if a pair of set of spherical
// generators of groupH gives a surface Y=(CxC)/G^0
// with the expected singularities.
//
// It only checks if, given two sets of spherical
// generators and a "candidate" basket, the resulting
// surface has the prescribed basket. The advantage is that
// in the wrong cases, the script stops when it finds a
// "forbidden" singularity, without losing time computing
// all the other singular points.
CheckSingsH:=function(basket,gens1,gens2,group)
test:=true; bas:=basket;
for i in [1..#gens1] do gen1:=gens1[i];
for j in [1..#gens2] do gen2:=gens2[j];
pb:=BasketByAPairOfGens(group,gen1,gen2);
for r in pb do r1:=RatNum(Reverse(ContFrac(r)));
if r in bas then Exclude(~bas,r);
elif r1 in bas then Exclude(~bas,r1);
else test:=false; break i;
end if; end for;
end for; end for;
return test and IsEmpty(bas);
end function;
// These function checks if a group has a pair of sets
// of spherical generators that give the expected
// singularities
SingularitiesY:=function(basketX,groupH,type)
BY:=BasketOfY(basketX);
s:=SetToSequence(SphGenUpToConj(groupH,type));
c:=1; test:= false;
for i in [1..#s] do gens1:=s[i];
for j in [c..#s] do gens2:=s[j];
if CheckSingsH(BY,gens1,gens2, groupH) then

test:=true; break i;
end if; end for; c+:=1; end for;
return test;
end function;
// Now we check if a given group G has a set of
// spherical generators for a group isomorphic to G^0
// in the group G of prescribed type.
ExistSphGens:=function(groupG, idH, type)
test:=false;
SetCands:=TuplesOfGivenOrders(groupG,Prune(type));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if Order(&*cands) eq type[#type] then
if IdentifyGroup(sub<groupG|TupleToSeq(cands)>)
eq idH then test:=true; break cands;
end if; end if; end for; end if;
return test;
end function;
// GroupExtension checks if the given group "groupH"=G^0
// has some unsplit extension of degree 2, and returns
// all the groups G which are unsplit extension of groupH.
//
// If the order of the group is "bad", it uses
// SmallGroupProcess instead of SmallGroups.
GroupExtension:=function(groupH,type, badorders)
ordG:= 2*Order(groupH); ext:=[* *];
idH:=IdentifyGroup(groupH);
card:=#{x: x in groupH | Order(x) eq 2};
if ordG notin badorders then
for G in SmallGroups(ordG: Warning := false) do
if #{x: x in G | Order(x) eq 2} eq card then
if ExistSphGens(G, idH, type) then
Append(~ext, IdentifyGroup(G));
end if; end if;
end for;
else
P:= SmallGroupProcess(ordG);
repeat
G := Current(P);

if #{x: x in G | Order(x) eq 2} eq card then
if ExistSphGens(G, idH,type) then
Append(~ext, IdentifyGroup(G));
end if;end if;
Advance(~P); until IsEmpty(P);
end if;
return ext;
end function;
// ListGroups lists in checked all possible fourtuples
// (basket, type, subgroup G^0, {groups G}).
// It lists in limbo the triples
// basket, type, group G^0, where G^0 has
// a pair of sets of spherical generators of groupH
// gives a surface Y=(CxC)/G^0 with the expected
// singularities, but we cannot check the extensions,
// since the order of the group is too big.
// It lists in tocheck the triples basket, type, order G^0,
// if order G^0 is bigger than 2000 or it is 1024.
ListGroups:=function(Ksquare, pg:
badorders1:={ 256, 384, 512, 576, 768},
badorders2:={ 1152,1280,1536,1920})
checked:=[* *]; tocheck:=[* *]; limbo:=[* *];
for pair in ListOfTypes(Ksquare, pg) do
basket:=pair[1]; setoftypes:=pair[2];
for type in setoftypes do
ordH:=IntegerRing()!((Ksquare+InvkSet(basket[1],basket[2]))/
((Theta(type))^2));
if {*2,3,7*} eq type and
NumberOfGroups(PerfectGroupDatabase(),ordH) eq 0 then ;
elif (ordH gt 2000) or (ordH eq 1024) then
Append(~tocheck, [* basket, type, ordH *]);
elif ordH in { 1001..2000} and
(ordH in Include(badorders2)) then
type1:=MsetToSeq(type);
for p in TestBAD(type1, ordH) do
H:=SmallGroup(ordH,p);
if SingularitiesY(basket,H,type1) then
Append(~limbo, [* basket, type, <ordH, p>*]); end if;
end for;
elif ordH in { 1001..2000} and
(ordH notin Include(badorders2)) then
type1:=MsetToSeq(type);

for p in Test(type1, ordH) do
H:=SmallGroup(ordH,p);
if SingularitiesY(basket,H,type1) then
Append(~limbo, [*basket, type, <ordH, p>*]); end if;
end for;
elif ordH in Include(badorders1,512) then
type1:=MsetToSeq(type);
for p in TestBAD(type1, ordH) do
H:=SmallGroup(ordH,p);
if SingularitiesY(basket,H,type1) then
extensions:=GroupExtension(H,type1, badorders1 join badorders2);
if not IsEmpty(extensions) then
Append(~checked, [* basket, type, IdentifyGroup(H), extensions *]);
end if;end if; end for;
else type1:=MsetToSeq(type);
for p in Test(type1, ordH) do
H:=SmallGroup(ordH,p);
if SingularitiesY(basket,H,type1) then
extensions:=GroupExtension(H,type1, badorders1 join badorders2);
if not IsEmpty(extensions) then
Append(~checked, [* basket, type, IdentifyGroup(H), extensions *]);
end if; end if; end for;
end if; end for; end for;
return checked, limbo, tocheck;
end function;
// Step 4: existence of surfaces
//
// First we create all the sets of spherical generators
// of a prescribed type that generate a
// group isomorphic to G^0 in the group G.
SphGens:=function(groupG, idH, type)
Gens:={ };
SetCands:=TuplesOfGivenOrders(groupG,Prune(type));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if Order(&*cands) eq type[#type] then
if IdentifyGroup(sub<groupG|TupleToSeq(cands)>) eq idH then
Include(~Gens, Append(TupleToSeq(cands),(&*cands)^-1));
end if; end if; end for; end if;
return Gens;
end function;

// CheckSingsG checks if a set of elements of groupG that
// is a system of spherical generators of groupH gives
// a surface X=(CxC)/G with the expected singularities.
//
// First it checks if the singularities of Y=(CxC)/G^0
// are the expected ones.
// If this is the case it checks if the ramification
// points are right.
CheckSingsG:=function(basket, gens, groupG)
groupH:= sub<groupG|gens>;
tp:=[g: g in groupG | g notin groupH][1];
gens2:=[]; BY:=BasketOfY(basket); BD:=basket[2];
for i in [1..#gens] do Append(~gens2, gens[i]^tp);
end for;
test:=CheckSingsH(BY,gens,gens2,groupH);
if test then
for k in [1..#gens] do gen:=gens[k]; gen2:=gen^tp;
sing,els:=BasketByAPairOfGens(groupH,gen,gen2);
S:=sub<groupH|gen>;
for j in [1..#sing] do
r:=sing[j]; g:=tp*(els[j]^(-1))*tp^(-1);
if exists{h: h in groupH | ((tp*h)^2 in S)
and ((tp*h*tp^-1)*g in S) } then
if r in BD then Exclude(~BD,r);
else test:= false; break k;
end if; end if;
end for; end for; end if;
if not IsEmpty(BD) then test:=false; end if;
return test;
end function;
// ExistingSurfaces returns all the fourtuples
// (basket, type, G^0, G) that give at least
// a surface with the correct singularities.
ExistingSurfaces:=function(Ksquare, pg)
M:=[* *];
list,limbo,tocheck:=ListGroups(Ksquare, pg);
for quadruple in list do
basket:=quadruple[1]; type:=quadruple[2];
idH:=quadruple[3]; listOfG:=quadruple[4];
for idgroupG in listOfG do test:=false;

// CheckSingsG checks if a set of elements of groupG that
// is a system of spherical generators of groupH gives
// a surface X=(CxC)/G with the expected singularities.
//
// First it checks if the singularities of Y=(CxC)/G^0
// are the expected ones.
// If this is the case it checks if the ramification
// points are right.
CheckSingsG:=function(basket, gens, groupG)
groupH:= sub<groupG|gens>;
tp:=[g: g in groupG | g notin groupH][1];
gens2:=[]; BY:=BasketOfY(basket); BD:=basket[2];
for i in [1..#gens] do Append(~gens2, gens[i]^tp);
end for;
test:=CheckSingsH(BY,gens,gens2,groupH);
if test then
for k in [1..#gens] do gen:=gens[k]; gen2:=gen^tp;
sing,els:=BasketByAPairOfGens(groupH,gen,gen2);
S:=sub<groupH|gen>;
for j in [1..#sing] do
r:=sing[j]; g:=tp*(els[j]^(-1))*tp^(-1);
if exists{h: h in groupH | ((tp*h)^2 in S)
and ((tp*h*tp^-1)*g in S) } then
if r in BD then Exclude(~BD,r);
else test:= false; break k;
end if; end if;
end for; end for; end if;
if not IsEmpty(BD) then test:=false; end if;
return test;
end function;
// ExistingSurfaces returns all the fourtuples
// (basket, type, G^0, G) that give at least
// a surface with the correct singularities.
ExistingSurfaces:=function(Ksquare, pg)
M:=[* *];
list,limbo,tocheck:=ListGroups(Ksquare, pg);
for quadruple in list do
basket:=quadruple[1]; type:=quadruple[2];
idH:=quadruple[3]; listOfG:=quadruple[4];
for idgroupG in listOfG do test:=false;

idx+1,seq[idx]^seq[idx+1])>;
// This one, starting from a sequence of elements of a group,
// creates all sequences of elements which are equivalent to
// the given one for the equivalence relation generated by
// the Hurwitz moves, and return (to spare memory) only
// the ones whose entries have never decreasing order.
HurwitzOrbit:=function(seq)
orb:={ }; shortorb:={ }; Trash:={ seq };
repeat
ExtractRep(~Trash,~gens); Include(~orb, gens);
for k in [1..#seq-1] do newgens:=HurwitzMove(gens,k);
if newgens notin orb then Include(~Trash, newgens);
end if; end for;
until IsEmpty(Trash);
for gens in orb do test:=true;
for k in [1..#seq-1] do
if Order(gens[k]) gt Order(gens[k+1]) then
test:=false; break k;
end if; end for;
if test then Include(~shortorb, gens); end if;
end for;
return shortorb;
end function;
// Finally we can find all surfaces. The next program
// finds all surfaces with a given groups, type and basket.
FindSurfaces:=function(K, basket, type,idH, idG)
Good:=[* *]; Surfaces:={ }; All:={ };
G:=SmallGroup(idG[1], idG[2]);
AutG:=AutGr(G);
NumberOfCands:=#SphGens(G,idH,MsetToSeq(type));
printf "To Find= %o\n", NumberOfCands;
for gens in SphGens(G,idH,MsetToSeq(type)) do
if gens notin All then
printf "A new one! ";
Include(~Surfaces, gens); H:=sub<G|gens>;
if CheckSingsG(basket, gens, G) then
S:=[* basket, type, gens, idH, idG*];
printf " and right singularities!\n";
printf "A REALLY NEW SURFACE!!!\n";
Append(~Good, S);

else printf " but wrong singularities!\n";
end if;
orb:=HurwitzOrbit(gens);
for g1 in orb do
if g1 notin All then
for phi in AutG do Include(~All, phi(g1));
if #All eq NumberOfCands then
printf "#Surfs= %o\n", #Surfaces; break gens;
end if; end for; end if; end for;
printf "#Surfs= %o, To Find= %o\n", #Surfaces, NumberOfCands-#All;
end if; end for;
return Good;
end function;
// Next script calls the previous scripts
// and stores the data of the surfaces in
// a text file.
Output:=function(Ksquare,pg)
t:=Realtime();
New:=[* *];
M, limbo, tocheck:=ExistingSurfaces(Ksquare,pg);
for m in M do
basket:=m[1]; type:=m[2]; idH:=m[3]; idgroup:=m[4];
printf "\n Checking news %o \n", m[4];
Surf:=FindSurfaces(Ksquare, basket, type, idH, idgroup);
for surf in Surf do Append(~New, surf);
end for; end for;
F:= Open("OUTPUT_WITH_Ks" cat IntegerToString(Ksquare)
cat "_pg" cat IntegerToString(pg) cat ".txt","w");
fprintf F, "K^2=%o\n\n\n", Ksquare;
if #New ne 0 then
fprintf F, "NEW SURFACES: %o\n", #New;
fprintf F, "basket, type, gens, Id(H), Id(G)\n\n";
for new in New do fprintf F, "%o\n\n", new; end for;
fprintf F, "\n\n";
end if;
if #limbo ne 0 then
fprintf F, "PARTIALLY TO CHECK CASES: %o\n", #limbo;
for L in limbo do fprintf F, "%o\n\n", L; end for;
fprintf F, "\n\n";
end if;
if #tocheck ne 0 then
fprintf F, " TO CHECK CASES: %o\n", #tocheck;

for T in tocheck do fprintf F, "%o\n\n", T; end for;
end if;
printf "Time: %o\n", Realtime(t);
return "K^2=",Ksquare,", #New surf=",#New;
end function;
// Step 6: the fundamental group
//
// Next scripts allow us to calculate the topological
// fundamental group of the surfaces we constructed.
// We use the description of the fundamental
// given in Theorem 7.1.2 and Proposition 7.1.8.
// Poly constructs the polygonal group and the
// appropriate orbifold homomorphism.
Poly:=function(seq, gr)
F:=FreeGroup(#seq); Rel:={F![1..#seq]};
for i in [1..#seq] do
Include(~Rel,F.i^Order(seq[i])); end for;
P:=quo<F|Rel>;
return P, hom<P->gr|seq>;
end function;
// DirProd(A,B) returns the direct product between
// the groups A and B, and the corresponding injections
// and projections.
DirProd:=function(G1,G2)
G1xG2:=DirectProduct(G1,G2); vars:=[];
n:=[NumberOfGenerators(G1),NumberOfGenerators(G2)];
for i in [1..(n[1]+n[2])] do
Append(~vars,G1xG2.i); end for;
SplittedVars:=Partition(vars,n);
injs:=[hom< G1->G1xG2 | SplittedVars[1]>,
hom< G2->G1xG2 | SplittedVars[2]>];
vars1:=[]; vars2:=[];
for i in [1..n[1]] do
Append(~vars1,G1.i); Append(~vars2,G2!1); end for;
for i in [1..n[2]] do
Append(~vars1,G1!1); Append(~vars2,G2.i); end for;
projs:=[hom< G1xG2->G1 | vars1>,hom< G1xG2->G2 | vars2>];
return G1xG2, injs, projs;
end function;

// MapProd computes given two maps f,g:A->B the map product
// induced by the product on B
MapProd:=function(map1,map2)
seq:=[];
A:=Domain(map1); B:=Codomain(map1);
if Category(A) eq GrpPC then n:=NPCgens(A);
else n:=NumberOfGenerators(A); end if;
for i in [1..n] do
Append(~seq, map1(A.i)*map2(A.i)); end for;
return hom<A->B|seq>;
end function;
// Pi1 uses a sequence of spherical generators for G^0
// inside G to construct the corresponding polygonal group
// and the group HH that acts on the universal cover of CxC.
// Then it constructs the degree 2 extension GG.
// Finally it takes the quotient by Tors(GG).
Pi1:=function(seq, G)
H:=sub<G|seq>; REL:=[]; TorsG:=[]; Sing:=;
el:=random{g: g in G | g notin H};
phi1:=hom<H->H| x:-> x^el>;
T,f1:=Poly(seq,H); t:=(el^2)@@f1;
TxT,inT,proT:=DirProd(T,T);
HxH,inH:=DirectProduct(H,H);
Diag:=MapProd(inH[1],inH[2])(H);
f:=MapProd(proT[1]*f1*inH[1],proT[2]*f1*phi1*inH[2]);
bigH:=Rewrite(TxT,Diag@@f); tt:=inT[1](t)*inT[2](t);
PHI:=hom<bigH->bigH| x:-> inT[1](proT[2](x))*inT[2](t*proT[1](x)*(t^-1))>;
genH:=SetToSequence(Generators(bigH)); relH:=Relations(bigH);
F:=FreeProduct(bigH,FreeGroup(1)); im:=[];
for i in [1..#genH] do Append(~im,F.i); end for;
map:=hom<bigH->F|im>; tau:=map(tt);
ul:=F.(#Generators(F)); Append(~REL, ul^2*(tau^-1));
for i in [1..#genH] do
Append(~REL, map(PHI(genH[i]))* ul * map(genH[i]^-1 )*(ul^-1));
end for;
bigG,pr:=quo<F|REL>;
for i in [1..#seq] do gen1:=seq[i];
for j in [1..#seq] do gen2:=seq[j];
for o1 in [1..Order(gen1)-1] do
for o2 in [1..Order(gen2)-1] do

test,v:=IsConjugate(H,gen1^o1, phi1(gen2^o2));
if test then Include(~Sing, [i,j]);
for d in Centralizer(H, gen1^o1) do
Append(~TorsG, pr(map(TxT.i^o1 *
((TxT.(j+#seq)^o2)^(inT[2]((el *d^-1*v*el^-1)@@f1)^-1)))));
end for; end if; end for; end for; end for; end for;
for i in [1..#seq] do gen:=seq[i];
if [i,i] in Sing then
for o in [1..Order(gen)-1] do
for h in H do
test, v:= IsConjugate(H, (el*h)^2, gen^o);
if test then
for d in Centralizer(H, gen^o) do
w:=(v*d)@@f1; h1:=h@@f1; h2:= (el*h*(el^-1))@@f1; s:=h2*t*h1;
k:=(s^-1)*((T.i^o)^(w^-1));
Append(~TorsG, pr(ul*(map(inT[1](h1)*inT[2](k*h2)))));
end for;
end if; end for; end for;end if; end for;
return Simplify(quo<bigG|TorsG>);
end function;
// Next function is an additional function
// that we used to exclude some skipped cases.
// It returns a representative of each conjugacy class
// of elements of the given order.
ConjugCl:=function(group, order)
Set:={}; Rep:=[];
list:=[x: x in group | Order(x) eq order];
for el in list do
if el notin Set then
for a in group do
Include(~Set, el^a);
end for; Append(~Rep, el);
end if; end for;
return Rep;
end function;