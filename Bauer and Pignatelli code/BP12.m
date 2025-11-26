// Code for paper "THE CLASSIFICATION OF MINIMAL PRODUCT-QUOTIENT SURFACES WITH pg = 0."

// We first need to find, for each K^2, what are the possible baskets of
// singularities. By Lemma 1.8 the sum of the invariants B of the
// singularities must equal 3(8-K^2).
//
// We will represent a singular point 1/n(1,a) by the rational number
// a/n; hence a basket of singularities will be a multiset of rational
// numbers. Remember that cyclic quotient singularities 1/n(1,a) and
// 1/n(1,a’) are isomorphic if a*a’=1 mod n, so we must consider rational
// numbers in (0,1) modulo the equivalence relation a/n~a’/n.
//
// The invariant B of a singularity 1/n(1,a) equals (a+a’)/n+sum(b_i),
// where b_i are the entries of the continuous fraction of n/a: we see
// them as the sequence [b_1,...,b_r]. Note that the continuous
// fraction of n/a’ is the "reversed" sequence [b_r,...,b_1].
//
// This can be seen as a bijection between rational numbers in (0,1)
// and sequences of integers strictly bigger than 1.
// We make this bijiection explicit by the following scripts.
ContFrac:=function(s)
CF:=[ ]; r:=1/s;
while not IsIntegral(r) do
Append(~CF, Ceiling(r)); r:=1/(Ceiling(r)-r);
end while;
return Append(CF, r);
end function;
Nq:=func<cf|#cf eq 1 select cf[1] else cf[1]-1/$$(Remove(cf,1))>;
RatNum:=func<seq|1/Nq(seq)>;
// "Wgt" computes the weight of a sequence, i.e., the sum of its
// entries. It bounds strictly from below B of the corresponding
// singular point.
Wgt:=function(seq)
w:=0; for i in seq do w+:=i; end for; return w;
end function;
// The next script computes all rational number whose continuous
// fraction has small weight, by listing all sequences (modulo
// "reverse") and storing the corresponding rational number.
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
// The next two scripts compute the invariants B and e of a rational
// number (i.e., of the corresponding singular point).
InvB:=func<r|Wgt(ContFrac(r))+r+RatNum(Reverse(ContFrac(r)))>;
Inve:=func<r|#ContFrac(r)+1-1/Denominator(RationalField()!r)>;
// The next two scripts compute the invariants B and e of a multiset
// of rational numbers (corresponding to a basket of singular points).
InvBSet:= function(basket)
B:=0; for r in basket do B+:=InvB(r); end for; return B;
end function;
InveSet:= function(basket)
e:=0; for r in basket do e+:=Inve(r); end for; return e;
end function;
// Here is the invariant k of the basket:SURFACES WITH pg = q = 0
Invk:=func<r|InvBSet(r)-2*InveSet(r)>;
// The next script computes all rational numbers with weight bounded
// from above by maxW, as computed by RatNumsWithSmallWgt, and returns
// them in a sequence ordered by the value of their invariant B,
// starting from the one with biggest B.
OrderedRatNums:=function(maxW)
seq:=[RationalField()| ]; seqB:=[RationalField()| ];
set:=RatNumsWithSmallWgt(Floor(maxW));
for r in set do i:=1;
for s in seqB do
if s gt InvB(r) then i+:=1;
else break s;
end if; end for;
Insert(~seq, i, r); Insert(~seqB, i, InvB(r));
end for;
return seq;
end function;
// The next one, CutSeqByB, takes a sequence "seq" and recursively
// removes the first element if its invariant B is at least maxB.
CutSeqByB:=function(seq,maxB)
Seq:=seq;
while #Seq ge 1 and InvB(Seq[1]) gt maxB do Remove(~Seq,1); end while;
return Seq;
end function;
// Now we have a way to compute the set of rationals with B bounded by
// the integer maxB, ordered by B:
// CutSeqByB(OrderedRatNums(maxB-1),maxB)
//
// The next script takes a sequence of rationals ordered by B
// and computes the baskets with invariant exactly B that use only these
// rationals.
// The function is as follows:
// -- first remove the elements with B too big to be in a basket
// -- then take the first element, say r, if B(r)=B, store {* r *}
// -- else attach it to each basket with invariant B-B(r)
// (computed recalling the function with the same sequence)
// and store the result
// -- now we have all baskets containing r: remove r from the sequence
// and repeat the procedure until the sequence is empty
BasketsWithSeqAndB:=function(seq,B)
ratnums:=CutSeqByB(seq,B); baskets:={ };
while #ratnums gt 0 do
bigguy:=ratnums[1];
if InvB(bigguy) eq B then Include(~baskets,{* bigguy *}); else
for basket in $$(ratnums, B-InvB(bigguy)) do
Include(~baskets, Include(basket, bigguy));
end for; end if;
Remove(~ratnums,1);
end while;
return baskets;
end function;
// Now we can compute all Baskets with a given B:
BasketsWithSmallB:=func<B|
BasketsWithSeqAndB(OrderedRatNums(Ceiling(B)-1),B)>;
// We do not need all these baskets, since most of them violate the Lemma 1.7.
// The next two scripts take care of this: "TestBasket" will check if a basket
// violates Lemma 1.7; "Basket" will take the output of BasketsWithSmallB and
// removes all the baskets which violate the condition.
TestBasket:=function(basket)
firstseq:=[];
for r in basket do Append(~firstseq,r); end for;
setofseqs:={ firstseq };
for i in [1..#firstseq] do newseqs:={};
for seq in setofseqs do
Include(~newseqs,
Insert(Remove(seq,i),i,RatNum(Reverse(ContFrac(seq[i])))));
end for;
setofseqs:=setofseqs join newseqs;
end for;
test:=false;
for seq in setofseqs do
if IsIntegral(Wgt(seq)) then test:=true;
end if;
end for;
return test;
end function;
Baskets:=function(B)
baskets:={ };
for basket in BasketsWithSmallB(B) do
if TestBasket(basket) then Include(~baskets, basket);SURFACES WITH pg = q = 0
end if;
end for;
return baskets;
end function;
// Now we have found, for each K^2, a finite and rather small number of
// possible baskets. The next step is to restrict, for each basket, to finitely
// many signatures. We will represent a signature as the multiset of naturals
// {* m_i *}.
//
// We first define the index of a basket of singularities as the lowest
// common multiple of the indices of the singularities
GI:=func<r|Denominator(r)/GCD(Numerator(r)+1,Denominator(r))>;
GorInd:= function(bas)
I:=1;
for r in bas do I:=LCM(IntegerRing()!I,IntegerRing()!GI(r)); end for;
return I;
end function;
// We need moreover the invariant Theta of a signature
Theta:=function(type)
t:=-2; for n in type do t+:=1-1/n; end for;
return t;
end function;
// The input of the next program are 4 numbers, CardBasket, Length, SBound and
// HBound (SBound<=HBound), and its output are all signatures with
// #signature=Length such that (for C:=max(1/6,(Length-3)/2)
// 1) each m_i is smaller than HBound/C;
// 2) most m_i are smaller than SBound/C, the number of exceptions
//
being bounded from above by half of CardBasket.
// For sparing time, the script first checks if the length is smaller
// than the number of possible exceptions to 2, in which case only the
// inequality 1 is to consider.
CandTypes:=function(CardBasket,Length,SBound,HBound)
C:=Maximum(1/6,(Length-3)/2); S:=Floor(SBound/C); H:=Floor(HBound/C);
Exc:=Floor(CardBasket/2);
if Length le Exc then Types:=Multisets({x: x in [2..H]},Length);
else Types:=Multisets({x: x in [2..S]},Length);
for k in [1..Exc] do
for TypeBegin in Multisets({x: x in [2..S]},Length-k) do
for TypeEnd in Multisets({x: x in [S+1..H]},k) do
Include(~Types, TypeBegin join TypeEnd);
end for; end for; end for;
end if;
return Types;
end function;
// The next script, ListOfTypesBas, finds all signatures compatible with the
// basket in the input (i.e., which respect Proposition 1.11).
// We use
// 1) Theta<= maxTh:=(K^2+k)/4 (follows from 1.11.a),
// 2) #signature<= 2*Theta+4 (follows from the definition of Theta).
ListOfTypesBas:=function(basket)
S:={ }; B:=InvBSet(basket); k:=Invk(basket); I:=GorInd(basket);
Ksquare:=8-B/3; maxTh:=(Ksquare+k)/4;
for h in [3..Floor(2*maxTh+4)] do
for cand in CandTypes(#basket,h,maxTh+1,2*I*maxTh+1) do
T:=Theta(cand);
if T le maxTh then
if T gt 0 then Alpha:=maxTh/T;
if Alpha in IntegerRing() then
if forall{n : n in cand | 2*Alpha*I/n in IntegerRing()} then bads:=0;
for n in cand do
if Alpha/n notin IntegerRing() then bads +:=1;
end if; end for;
if bads le #basket/2 then Include(~S,cand);
end if; end if; end if; end if; end if; end for; end for;
return S;
end function;
// Finally, we can conlude the second step, by writing a script which
// lists, for given K^2, all possible baskets (by using Baskets) and for
// each basket all possible signatures (by using ListOfTypesBas)
ListOfTypes:=function(Ksquare)
S:=[* *];
for basket in Baskets(3*(8-Ksquare)) do L:=ListOfTypesBas(basket);
if not IsEmpty(L) then Append(~S,[* basket, L *]);
end if; end for;
return S;
end function;
// Now we are left with the last step: for each basket we need to
// consider all pairs of possible signatures and look for groups of the
// correct order which have two sets of spherical generators of these
// signatures which give a surface with the prescribed basket ofSURFACES WITH pg = q = 0
// singularities. First we need to write some command which is not
// implemented in MAGMA.
// This extracts from a finite group the set of elements of a certain
// order.
ElsOfOrd:=function(group,order)
Els:={ };
for g in group do if Order(g) eq order then Include(~Els, g);
end if; end for;
return Els;
end function;
// TuplesOfGivenOrder creates a sequence of the same length as the input
// sequence seq, whose entries are subsets of the group in the input,
// and precisely the subsets of elements of order the corresponding
// entry of seq
TuplesOfGivenOrders:=function(group,seq)
SEQ:=[];
for i in [1..#seq] do
if IsEmpty(ElsOfOrd(group,seq[i])) then SEQ:=[]; break i;
else Append(~SEQ,ElsOfOrd(group,seq[i]));
end if;
end for;
return SEQ;
end function;
// This two transform a multiset, resp. a tuple, into a sequence.
TypeToSeq:=function(type)
seq:=[ ]; t:=type;
while #t ne 0 do Append(~seq, Maximum(t));
Exclude(~t, Maximum(t));
end while;
return seq;
end function;
TupleToSeq:=function(tuple)
seq:=[];
for elt in Tuplist(tuple) do
Append(~seq,elt);
end for;
return seq;
end function;
// This script checks if a group has a set of spherical generators of
// the prescribed signature.
ExSphGens:=function(group,type)
test:=false; seq:=TypeToSeq(type);
SetCands:=TuplesOfGivenOrders(group,Prune(seq));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if Order(&*cands) eq seq[#seq] then
if sub<group|TupleToSeq(cands)> eq group then
test:=true; break cands;
end if; end if;
end for; end if;
return test;
end function;
// The next script runs a systematic search on all finite groups and
// produces the list of all triples (basket, pair of signatures, group)
// such that
// 1) the basket is compatible with the input K^2;
// 2) the signatures are compatible with the basket;
// 3) the group has order (K^2+k)/(2*Theta_1*Theta_2) (see 1.11.b)
//
and sets of spherical generators of both signatures.
// If one of the signatures is {*2,3,7*} the group must be perfect, so
// in this case the program first checks if there are perfect groups of
// the right order: if the answer is negative it jumps directly to the
// next case.
// The program skips to check the groups of order bigger than 2000, 1024
// (since there is no complete list avalaible) or of orders in the set
// "badorders" which can be chosen by the user.
// These skipped cases are listed in the second output, and must be
// considered separately.
ListGroups:=function(Ksquare: badorders:={256,512,768,1152,1280,
1536,1728,1792,1920})
checked:=[* *]; tocheck:=[* *];
for pair in ListOfTypes(Ksquare) do
basket:=pair[1]; types:=pair[2]; k:=Invk(basket);
for pairoftypes in Multisets(types,2) do ord:=(Ksquare+k)/2;
for T in pairoftypes do ord:=ord/Theta(T);
end for;
if IsIntegral(ord) then
if {*2,3,7*} in pairoftypes and
NumberOfGroups(PerfectGroupDatabase(),IntegerRing()!ord) eq 0
then ;
elif ord gt 2000 or ord in Include(badorders,1024) thenSURFACES WITH pg = q = 0
Append(~tocheck, [* basket, pairoftypes, ord *]);
else for G in SmallGroups(IntegerRing()!ord: Warning := false) do
test:=true;
for T in pairoftypes do
if not ExSphGens(G,T) then test:=false; break T;
end if;
end for;
if test then Append(~checked, [* basket, pairoftypes, G *]);
end if; end for;
end if; end if; end for; end for;
return checked, tocheck;
end function;
// Each case in the first output of ListGroups(K^2) gives at least a
// surface, but we are interested only in those surfaces having the
// prescribed basket of singularities. The next goal then is to compute
// these singularities.
//
// The next script takes a sequence of elements of a group and a further
// element g and conjugates each element of the sequence with g.
Conjug:=function(seq,elt)
output:=[];
for h in seq do Append(~output,h^elt);
end for;
return output;
end function;
// The next program computes all possible sets of spherical generators
// of a group of a prescribed signature and returns (to spare memory) only
// one of these sets for each conjugacy class.
SphGenUpToConj:=function(group,type)
Set:={ }; Rep:={ }; seq:=TypeToSeq(type);
SetCands:=TuplesOfGivenOrders(group,Prune(seq));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if TupleToSeq(cands) notin Set then
if Order(&*cands) eq seq[#seq] then
if sub<group|TupleToSeq(cands)> eq group then
Include(~Rep, Append(TupleToSeq(cands),(&*cands)^-1));
for g in group do Include(~Set, Conjug(TupleToSeq(cands),g));
end for;
end if; end if; end if;
end for; end if;
return Rep;
end function;
// Given two sets of spherical generators, the singular points of the
// resulting surface are the image of points in the product of curves
// C_1xC_2 having nontrivial stabilizer. These correspond to pairs
// (g_1,n_1,g_2,n_2) where
// - g_1 is a generator of the first set;
// - g_2 is a generator of the second set;
// 1<=n_1<=ord(g_1); 1<=n_2<=ord(g_2); g_1^n_1=g_2^n_2
// First we write a program which computes the singular points
// coming from a fixed pair (g1,g2).
BasketByAPairOfGens:=function(group,gen1,gen2)
basket:={* *}; RC:={ }; delta:=GCD(Order(gen1),Order(gen2));
alpha1:=IntegerRing()!(Order(gen1)/delta);
alpha2:=IntegerRing()!(Order(gen2)/delta);
RC2,f2:=RightTransversal(group,sub<group | gen2 >);
for g2 in RC2 do test:=true;
for g in sub<group| gen1 > do
if f2(g2*g) in RC then test:=false; break g;
end if; end for;
if test then Include(~RC, g2);
end if; end for;
for g in RC do
for d1 in [1..delta-1] do
for d2 in [1..delta-1] do
if (gen1^(d1*alpha1)) eq (gen2^(d2*alpha2))^g then
Include(~basket,d2/delta); break d1;
end if; end for; end for; end for;
return basket;
end function;
// We could use it to compute the basket of singularities of every
// constructed surface, but this is too expensive for our purposes.
// The next program only checks if, given two sets of spherical
// generators and a "candidate" basket, the resulting surface has the
// prescribed basket. The advantage is that in the wrong cases, the
// script stops when it finds a "forbidden" singularities, without
// losing time computing all the other singular points.
CheckSings:=function(basket,gens1,gens2,group)
test:=true; bas:=basket;
for gen1 in gens1 do
for gen2 in gens2 do pb:=BasketByAPairOfGens(group,gen1,gen2);
for r in pb do r1:=RatNum(Reverse(ContFrac(r)));SURFACES WITH pg = q = 0
if r in bas then Exclude(~bas,r);
elif r1 in bas then Exclude(~bas,r1);
else test:=false; break gen1;
end if; end for;
end for; end for;
return test and IsEmpty(bas);
end function;
// The next script computes all product-quotient surfaces
// with p_g=0, chi=1 and given K^2. It has the same input as ListGroups,
// K^2 and the bad orders (BO), so it does not treat the cases not
// treated by ListGroups, which must be treated separately.
ExistingSurfaces:=function(Ksquare: BO:={256,512,768,1152,1280,
1536,1728,1792,1920})
M:=[* *];
for triple in ListGroups(Ksquare: badorders:=BO) do
basket:=triple[1]; pairsoftypes:=triple[2];
group:=triple[3]; Types:=[];
for type in pairsoftypes do Include(~Types,type); end for;
SetGens1:=SphGenUpToConj(group,Types[1]);
if #Types eq 1 then SetGens2:=SetGens1;
else SetGens2:=SphGenUpToConj(group,Types[2]);
end if;
test:=false;
for gens1 in SetGens1 do
for gens2 in SetGens2 do
if CheckSings(basket,gens1,gens2,group) then test:=true;
break gens1;
end if;
end for; end for;
if test then
Append(~M, [* basket,pairsoftypes,IdentifyGroup(group)*]);
end if;
end for;
return M;
end function;
// We still have not found all possible surfaces. In fact the output of
// ExistingSurfaces(n) gives all possible triples
// (basket,pair of signatures, group) which give AT LEAST a surface with
// p_g=0 and K^2=n, but there could be more than one. In fact, there are
// more than one surface for each pair of spherical generators of the
// prescribed types which pass the singularity test, but they are often
// isomorphic. More precisely, they are isomorphic if the pair of
// spherical generators are equivalent for the equivalence relation
// generated by Hurwitz moves (on each set of generators separately)
// and the automorhisms of the group (on both sets simultaneously).
// We need to construct orbits for this equivalence relation.
// The next scripts creates the Automorphism Group of a group as an
// explicit set.
AutGr:=
function(gr)
Aut:=AutomorphismGroup(gr); A:={ Aut!1 };
repeat
for g1 in Generators(Aut) do
for g2 in A do
Include (~A,g1*g2);
end for; end for;
until #A eq #Aut;
return A;
end function;
// The next script creates the Hurwitz move.
HurwitzMove:=
function(seq,idx)
return Insert(Remove(seq,idx),idx+1,seq[idx]^seq[idx+1]);
end function;
// This script, starting from a sequence of elements of a group,
// creates all sequences of elements which are equivalent to the given
// one for the equivalence relation generated by Hurwitz moves,
// and returns (to spare memory) only the ones whose entries have never
// increasing order.
HurwitzOrbit:=
function(seq)
orb:={ }; shortorb:={ }; Trash:={ seq };
repeat
ExtractRep(~Trash,~gens); Include(~orb, gens);
for k in [1..#seq-1] do newgens:=HurwitzMove(gens,k);
if newgens notin orb then Include(~Trash, newgens);
end if; end for;
until IsEmpty(Trash);
for gens in orb do test:=true;
for k in [1..#seq-1] do
if Order(gens[k]) lt Order(gens[k+1]) then test:=false; break k;
end if;
end for;
if test then Include(~shortorb, gens);SURFACES WITH pg = q = 0
end if;
end for;
return shortorb;
end function;
// Now we create all sets of spherical generators of a group of a
// prescribed signature.
SphGens:=function(group,seq)
Gens:={ }; SetCands:=TuplesOfGivenOrders(group,Prune(seq));
if not IsEmpty(SetCands) then
for cands in CartesianProduct(SetCands) do
if Order(&*cands) eq seq[#seq] then
if sub<group|TupleToSeq(cands)> eq group then
Include(~Gens, cands);
end if; end if;
end for; end if;
return Gens;
end function;
// Finally, we can find all surfaces. The next program finds all
// surfaces with a given group, pair of signatures and basket (must be run
// on the outputs of ExistingSurfaces).
FindSurfaces:=function(basket, pairoftypes, gr)
Good:={@ @}; Surfaces:={ }; All:={ }; Aut:=AutGr(gr); Types:=[];
for type in pairoftypes do Append(~Types, type);
end for;
seq1:=TypeToSeq(Types[1]); seq2:=TypeToSeq(Types[2]);
NumberOfCands:=#SphGens(gr,seq1)*#SphGens(gr,seq2);
for gens1 in SphGens(gr,seq1) do genseq1:=TupleToSeq(gens1);
for gens2 in SphGens(gr,seq2) do genseq2:=TupleToSeq(gens2);
if genseq1 cat genseq2 notin All then
Include(~Surfaces, [Append(genseq1,(&*gens1)^-1),
Append(genseq2,(&*gens2)^-1)]);
orb1:=HurwitzOrbit(Append(genseq1,(&*gens1)^-1));
orb2:=HurwitzOrbit(Append(genseq2,(&*gens2)^-1));
for g1 in orb1 do gg1:=Prune(g1);
for g2 in orb2 do gg2:=Prune(g2);
if gg1 cat gg2 notin All then
for phi in Aut do Include(~All, phi(gg1 cat gg2));
end for;
end if;
if #All eq NumberOfCands then break gens1;
end if;
end for; end for;
end if;
end for; end for;
for gens in Surfaces do
if CheckSings(basket,gens[1],gens[2],gr) then
Include(~Good, gens);
end if; end for;
return Good;
end function;
// The next script, FindCurves, uses the same argument of FindSurfaces to find
// all curves with a given signature and group, modulo Hurwitz moves and inner
// automorphisms of the group.
FindCurves:=function(type, gr)
Curves:={ }; All:={ }; seq:=TypeToSeq(type);
NumberOfCands:=#SphGens(gr,seq);
for gens in SphGens(gr,seq) do genseq:=TupleToSeq(gens);
if genseq notin All then
Include(~Curves, Append(genseq,(&*gens)^-1));
orb:=HurwitzOrbit(Append(genseq,(&*gens)^-1));
for g in orb do gg:=Prune(g);
if gg notin All then
for h in gr do Include(~All, Conjug(gg,h));
end for;
end if;
if #All eq NumberOfCands then break gens;
end if;
end for;
end if;
end for;
return Curves;
end function;
PolyGroup:=function(seq,gr)
F:=FreeGroup(#seq); R:={F![1..#seq]};
for i in [1..#seq] do
Include(~R,F.i^Order(seq[i]));
end for;
P:=quo<F|R>;
return P, hom<P->gr|seq>;
end function;
DirProd:=function(G1,G2)
G1xG2:=DirectProduct(G1,G2); vars:=[];
n:=[NumberOfGenerators(G1),NumberOfGenerators(G2)];
for i in [1..Wgt(n)] do Append(~vars,G1xG2.i); end for;SURFACES WITH pg = q = 0
SplittedVars:=Partition(vars,n);
injs:=[hom< G1->G1xG2 | SplittedVars[1]>,
hom< G2->G1xG2 | SplittedVars[2]>];
vars1:=[]; vars2:=[];
for i in [1..n[1]] do
Append(~vars1,G1.i); Append(~vars2,G2!1);
end for;
for i in [1..n[2]] do
Append(~vars1,G1!1); Append(~vars2,G2.i);
end for;
projs:=[hom< G1xG2->G1 | vars1>,hom< G1xG2->G2 | vars2>];
return G1xG2, injs, projs;
end function;
// The next script computes, given two maps A->B (careful, they MUST be
// between the same groups) the map product induced by the product on B
MapProd:=function(map1,map2)
seq:=[]; G:=Domain(map1); H:=Codomain(map1);
if Category(G) eq GrpPC then n:=NPCgens(G);
else n:=NumberOfGenerators(G); end if;
for i in [1..n] do Append(~seq,map1(G.i)*map2(G.i)); end for;
return hom<G->H|seq>;
end function;
// Finally, this program computes the fundamental group of a product-quotient
// surface.
Pi1:=function(pairsofseqs,gr)
T1,f1:=PolyGroup(pairsofseqs[1],gr);
T2,f2:=PolyGroup(pairsofseqs[2],gr);
T1xT2,inT,proT:=DirProd(T1,T2);
grxgr,inG:=DirectProduct(gr,gr);
Diag:=MapProd(inG[1],inG[2])(gr);
f:=MapProd(proT[1]*f1*inG[1],proT[2]*f2*inG[2]);
H:=Rewrite(T1xT2,Diag@@f); rels:=[];
for i in [1..#pairsofseqs[1]] do g1:=pairsofseqs[1][i];
for j in [1..#pairsofseqs[2]] do g2:=pairsofseqs[2][j];
for d1 in [1..Order(g1)-1] do
for d2 in [1..Order(g2)-1] do
test,h:=IsConjugate(gr,g1^d1,g2^d2);
if test then for c in Centralizer(gr,g1^d1) do
Append(~rels, T1xT2.i^d1 *
((T1xT2.(j+#pairsofseqs[1])^d2)^(inT[2]((h^-1*c) @@ f2))));
end for; end if;
end for; end for; end for; end for;
return Simplify(quo<H|rels>);
end function;