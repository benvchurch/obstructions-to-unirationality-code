// Code for the paper "QUOTIENTS OF PRODUCTS OF CURVES, NEW SURFACES WITH pg = 0 AND THEIR FUNDAMENTAL GROUPS."

/* The first script, ListOfTypes, produces, for each value of K^2=8-t,
a list containing all signatures fulfilling the conditions i), ii) and iii)
in subsection 5.2. We represent the signatures by sequences of 7
positive integers [m1,..,m7], adding some "1" if the length of the
sequence is shorter. E.g., the signature (2,3,7) is represented by the
sequence [1,1,1,1,2,3,7]. Note that by lemma 5.9 the length of the
signatures is bounden by 7.
The script takes all nondecreasing sequences of 7 positive integers
between 1 and 3(K^2+2) (cf. lemma 5.9) and discards those
which do not fulfill all three conditions.
The script uses two auxiliary functions Theta and Alpha computing the
respective numbers (see (17) in subsection 5.2). */

Theta:=function(sig)
a:=5;
for m in sig do a:=a-1/m; end for;
return a;
end function;
Alpha:=func<sig,Ksquare | Ksquare/(4*Theta(sig))>;
ListOfTypes:=function(Ksquare: MaximalCoefficient:=3*(Ksquare+2))
list:=[* *];
for m1 in [ 1..3*(Ksquare+2)] do
for m2 in [m1..3*(Ksquare+2)] do
for m3 in [m2..3*(Ksquare+2)] do
for m4 in [m3..3*(Ksquare+2)] do
for m5 in [m4..3*(Ksquare+2)] do
for m6 in [m5..3*(Ksquare+2)] do
for m7 in [m6..3*(Ksquare+2)] do
sig:=[Integers() | m1,m2,m3,m4,m5,m6,m7 ];
if Theta(sig) ne 0 then A:=Alpha(sig,Ksquare);
if A in IntegerRing() and A ge 1 then
if forall{m : m in sig | 2*A/m in IntegerRing()} then bads:=0;
for m in sig do
if A/m notin IntegerRing() then bads +:=1;
end if; end for;
if bads le 4-Ksquare/2 then Append(~list,sig);
end if; end if; end if; end if;
end for; end for; end for; end for; end for; end for; end for;
return list;
end function;


/* The second important script is ListGroups, which returns for each
K^2, the list of all triples [G,T1,T2] where T1 and T2 are two
signatures in ListOfTypes(K^2) and G is a group of the prescribed
order 8*Alpha(T1)*Alpha(T2)/K^2 having sets of spherical generators of
both signatures. Note that the script skips the cases: |G| = 1024,
1152, or bigger than 2000, cases which we have excluded by hand (cf.
subsection(5.3)).
It uses two subscripts:
ElsOfOrd which returns the set of elements of a group of a given
order,
ExistSphericalGenerators, a boolean function which answers if a
group has a system of generators of a prescribed signature */

ElsOfOrd:=function(G,order)
Els:={ };
for g in G do if Order(g) eq order then Include(~Els, g);
end if; end for;
return Els; end function;

ExistSphericalGenerators:=function(G,sig)
test:=false;
for x1 in ElsOfOrd(G,sig[1]) do
for x2 in ElsOfOrd(G,sig[2]) do
for x3 in ElsOfOrd(G,sig[3]) do
for x4 in ElsOfOrd(G,sig[4]) do
for x5 in ElsOfOrd(G,sig[5]) do
for x6 in ElsOfOrd(G,sig[6]) do
if Order(x1*x2*x3*x4*x5*x6) eq sig[7]
and #sub<G|x1,x2,x3,x4,x5,x6> eq #G
then test:=true; break x1;
end if;
end for; end for; end for; end for; end for; end for;
return test;
end function;
ListGroups:=function(Ksquare)
list:=[* *]; L:=ListOfTypes(Ksquare); L1:=L;
for T1 in L do
for T2 in L1 do
ord:=8*Alpha(T1,Ksquare)*Alpha(T2,Ksquare)/Ksquare;
if ord in IntegerRing() and ord le 200 and ord notin {1024, 1152} then
for G in SmallGroups(IntegerRing()!ord: Warning := false) do
if ExistSphericalGenerators(G,T1) then
if ExistSphericalGenerators(G,T2) then
Append(~list,[* G,T1,T2 *]);
end if; end if; end for; end if; end for;
L1:=Reverse(Prune(Reverse(L1)));
end for;
return list;
end function;

/* Each triple [G,T1,T2] corresponds to many surfaces, one for each
pair of spherical generators of G of the prescribed signatures, but
still these surfaces can be too singular.
The script ExistingNodalSurfaces returns all triples in the output of
ListGroups such that at least one of the surfaces has exactly the
prescribed number 8-K^2 of nodes as singularities.
It uses three more scripts.
FSGUpToConjugation returns a list of spherical generators of the group
of given type, and more precisely, one for each conjugacy
class. It divides the set of spherical generators into two sets,
Heaven and Hell, according to the rule "if a conjugate of the set I’m
considering is in Heaven, go to Hell, else to Heaven", and returns Heaven.
CheckSingsEl is a Boolean function answering if the surface S given by
two sets of generators of G has the right number of nodes and no other
singularities.
It uses the following: given a pair of spherical generators, the singular
points of the resulting surface S come from pairs g,h of elements, one
for each set, such that there are n,m with g^n nontrivial and
conjugated to h^m. If the order of g^n is 2 then S has some nodes,
else S has worse singularities, a contradiction.
Checksings is a Boolean function answering if there is apair of spherical
generators of G of signatures sig1 and sig2 giving a surface with the
right number of nodes.
To save time it checks only one set of spherical generators for each
conjugacy class, using FSGUpToConjugation. In fact, the isomorphism
class of the surface obtained by a pair of spherical generators does
not change if we act on one of them by an inner automorphism. */

FSGUpToConjugation:=function(G,sig)
Heaven:={@ @}; Hell:={@ @};
for x1 in ElsOfOrd(G,sig[1]) do
for x2 in ElsOfOrd(G,sig[2]) do
for x3 in ElsOfOrd(G,sig[3]) do
for x4 in ElsOfOrd(G,sig[4]) do
for x5 in ElsOfOrd(G,sig[5]) do
for x6 in ElsOfOrd(G,sig[6]) do x7:=x1*x2*x3*x4*x5*x6;
if Order(x7) eq sig[7] then
if #sub<G|x1,x2,x3,x4,x5,x6> eq #G then
if [x1,x2,x3,x4,x5,x6,x7^-1] notin Hell then
Include(~Heaven,[x1,x2,x3,x4,x5,x6,x7^-1]);
for g in G do
Include(~Hell, [x1^g,x2^g,x3^g,x4^g,x5^g,x6^g,(x7^-1)^g]);
end for;
end if; end if; end if;
end for; end for; end for; end for; end for; end for;
return Heaven;
end function;

CheckSingsEl:=function(G,seq1,seq2,Ksquare)
Answer:=true; Nodes:=0;
for g1 in seq1 do
for g2 in seq2 do
for d1 in [1..Order(g1)-1] do
for d2 in [1..Order(g2)-1] do
if IsConjugate(G,g1^d1,g2^d2) then
if Order(g1^d1) ge 3 then Answer:=false; break g1;
elif Order(g1^d1) eq 2 then
Nodes +:=Order(G)/(2*d1*d2*#Conjugates(G,g1^d1));
if Nodes gt 8-Ksquare then Answer:=false; break g1;
end if; end if; end if; end for; end for; end for; end for;
return Answer and Nodes eq 8-Ksquare;
end function;

CheckSings:=function(G,sig1,sig2,Ksquare)
test:=false;
for gens1 in FSGUpToConjugation(G,sig1) do
for gens2 in FSGUpToConjugation(G,sig2) do
if CheckSingsEl(G,gens1,gens2,Ksquare) then test:=true; break gens1;
end if; end for; end for; return test;
end function;

ExistingNodalSurfaces:=function(Ksquare)
M:=[* *];
for triple in ListGroups(Ksquare) do
G:=triple[1]; T1:=triple[2]; T2:=triple[3];
if CheckSings(G,T1,T2,Ksquare) then Append(~M, triple);
end if; end for; return M; end function;

/* ExistingNodalSurfaces produces a list of triples [G,T1,T2] more
precisely 7 for K^2=2, 11 for K^2=4 and 6 for K^2=6, one for each row
of table 2. To each of these triples correspond at least a surface
with p_g=q=0.
We need a script which finds all surfaces, modulo isomorphisms. Recall
that two of these surfaces are isomorphic if and only if the two pairs
of spherical generators are equivalent for the equivalence
relation generated by Hurwitz moves on each set and by the
automorphism group of G (acting simultaneously on the pair). This is
done by FindAllComponents, which needs 4 new scripts.
AutGr describes the automorphism group of G as set.
HurwitzMove runs an Hurwitz move on a sequence of elements of a
group.
HurwitzOrbit computes the orbit of a sequence of elements of
the group under Hurwitz moves, and then returns (to save memory)
the subset of the sequences such that the corresponding sequence of integers,
given by the orders of the group elements, is non
decreasing.
SphGens gives all sets of spherical generators of a group of
prescribed signature of length 5. Note that we have reduced the
length of the signature from 7 to 5, because the output of
ListOfTypes (see table 3) shows that the bound of r in lemma 5.9 can
be sharpened to 5.
Finally FindAllComponents produces (fixing the group and the
signatures) one pair of spherical generators for each isomorphism
class.
Running FindAllComponents on all 7+11+6 triples obtained by
ExixtingNodalSurfaces (remembering that we have to shorten the
signatures removing the first two 1) we always find one surface
except in three cases, giving two surfaces.
*/

AutGr:=function(G)
Aut:=AutomorphismGroup(G); A:={ Aut!1 };
repeat
for g1 in Generators(Aut) do
for g2 in A do
Include (~A,g1*g2);
end for; end for;
until #A eq #Aut; return A; end function;
HurwitzMove:=function(seq,idx)
return Insert(Remove(seq,idx),idx+1,seq[idx]^seq[idx+1]);
end function;
HurwitzOrbit:=function(seq)
orb:={ }; Purgatory:={ seq };
repeat
ExtractRep(~Purgatory,~gens); Include(~orb, gens);
for k in [1..#seq-1] do hurgens:=HurwitzMove(gens,k);
if hurgens notin orb then Include(~Purgatory, hurgens);
end if; end for;
until IsEmpty(Purgatory);
orbcut:={ };
for gens in orb do test:=true;
for k in [1..#seq-1] do
if Order(gens[k]) gt Order(gens[k+1]) then test:=false; break k;
end if;
end for;
if test then Include(~orbcut, gens);
end if;
end for; return orbcut; end function;
SphGens:=function(G,sig)
Gens:={ };
for x1 in ElsOfOrd(G,sig[1]) do
for x2 in ElsOfOrd(G,sig[2]) do
for x3 in ElsOfOrd(G,sig[3]) do
for x4 in ElsOfOrd(G,sig[4]) do
if Order(x1*x2*x3*x4) eq sig[5] then
if sub<G|x1,x2,x3,x4> eq G then
Include(~Gens, [x1,x2,x3,x4,(x1*x2*x3*x4)^-1]);
end if; end if; end for; end for; end for; end for;
return Gens; end function;
FindAllComponents:=function(G,sig1,sig2,Ksquare)
Comps:={@ @}; Heaven:={ }; Hell:={ }; Aut:=AutGr(G);
NumberOfCands:=#SphGens(G,sig1)*#SphGens(G,sig2);
for gen1 in SphGens(G,sig1) do
for gen2 in SphGens(G,sig2) do
if gen1 cat gen2 notin Hell then
Include(~Heaven, [gen1,gen2]);
orb1:=HurwitzOrbit(gen1); orb2:=HurwitzOrbit(gen2);
for g1 in orb1 do for g2 in orb2 do for phi in Aut do
Include(~Hell, phi(g1 cat g2));
if #Hell eq NumberOfCands then break gen1;
end if;
end for; end for; end for;
end if;
end for; end for;
for gens in Heaven do
if CheckSingsEl(G,gens[1],gens[2],Ksquare) then
Include(~Comps, gens);
end if; end for; return Comps; end function;

/* Finally we have to compute the fundamental group of the resulting
surfaces, which is done by the script Pi1. It uses the script
Polygroup which, given a sequence of 5 spherical generators of a group
5, produces the corresponding Polygonal Group P and the surjective
morphism P->G.
Pi1 uses the two sequences seq1, seq2 of 5 spherical generators of G
to construct the surjection f from the product of the respective
polygonal groups T1 x T2 to G x G, defines the subgroup H (=preimage
of the diagonal in GxG), and takes the quotient by by a sequence of
generators of Tors(H), which are obtained as follows: consider each pair
of elements (g1,g2), where gi is an element of seqi, such that g1^a is
nontrivial and conjugate to g2^b. Note that they give rise to a node, so
they both have order 2). Let h be a fixed element of G such that
g1^a*h=h*g2^b.
We let c vary between the elements in G commuting with g1^a.
Let t1,t2 be the natural preimages of g1,g2 in the
respective polygonal groups T1 and T2, t a preimage of h^-1*c in T2.
Then t1^a*t^-1*t2^b*t has order 2 and belongs to H.
These elements generate Tors(H) (see prop. 4.3). */

/* forms the free group generated by e1, ..., e5 subject to the relations e1 * ... * e5 = id and e_i^(seq_i) = id */

PolyGroup:=function(seq)
F:=FreeGroup(#seq);
P:=quo<F | F.1^Order(seq[1]), F.2^Order(seq[2]), F.3^Order(seq[3]),
F.4^Order(seq[4]), F.5^Order(seq[5]), F.1*F.2*F.3*F.4*F.5>;
return P, hom<P->Parent(seq[1])|seq>;
end function;

Pi1:=function(seq1,seq2)
T1:=PolyGroup(seq1); T2,f2:=PolyGroup(seq2); G:=Parent(seq1[1]);
T1xT2:=DirectProduct(T1,T2);
inT2:=hom< T2->T1xT2 | [T1xT2.6, T1xT2.7, T1xT2.8, T1xT2.9, T1xT2.10]>;
GxG,inG:=DirectProduct(G,G); m:=NumberOfGenerators(G); L:=[ ];
for i in [1..m] do Append(~L,GxG.i*GxG.(i+m)); end for;
Diag:=hom<G->GxG|L>(G);
f:=hom<T1xT2->GxG|
inG[1](seq1[1]),inG[1](seq1[2]),inG[1](seq1[3]),
inG[1](seq1[4]),inG[1](seq1[5]),
inG[2](seq2[1]),inG[2](seq2[2]),inG[2](seq2[3]),
inG[2](seq2[4]),inG[2](seq2[5])>;
H:=Rewrite(T1xT2,Diag@@f); TorsH:=[ ];
for i in [1..5] do if IsEven(Order(seq1[i])) then
for j in [1..5] do if IsEven(Order(seq2[j])) then
a:=IntegerRing()!(Order(seq1[i])/2); b:=IntegerRing()!(Order(seq2[j])/2);
test,h:= IsConjugate(G,seq1[i]^a,seq2[j]^b);
if test then for c in Centralizer(G,seq1[i]^a) do
Append(~TorsH, T1xT2.i^a * ((T1xT2.(j+5)^b)^(inT2((h^-1*c) @@ f2))));
end for; end if;
end if; end for; end if; end for;
return Simplify(quo<H | TorsH>);
end function;

/* This following script does the same computation as the previous one,
but instead of returning the fundamental group as astract group it
returns T1xT2, H as subgroup of T1xT2 and a list of generators of
Tors(H) */

Pi1Detailed:=function(seq1,seq2)
T1:=PolyGroup(seq1); T2,f2:=PolyGroup(seq2); G:=Parent(seq1[1]);
T1xT2:=DirectProduct(T1,T2);
inT2:=hom< T2->T1xT2 | [T1xT2.6, T1xT2.7, T1xT2.8, T1xT2.9, T1xT2.10]>;
GxG,inG:=DirectProduct(G,G); m:=NumberOfGenerators(G); L:=[ ];
for i in [1..m] do Append(~L,GxG.i*GxG.(i+m)); end for;
Diag:=hom<G->GxG|L>(G);
f:=hom<T1xT2->GxG|
inG[1](seq1[1]),inG[1](seq1[2]),inG[1](seq1[3]),
inG[1](seq1[4]),inG[1](seq1[5]),
inG[2](seq2[1]),inG[2](seq2[2]),inG[2](seq2[3]),
inG[2](seq2[4]),inG[2](seq2[5])>;
H:=Rewrite(T1xT2,Diag@@f); TorsH:=[ ];
for i in [1..5] do if IsEven(Order(seq1[i])) then
for j in [1..5] do if IsEven(Order(seq2[j])) then
a:=IntegerRing()!(Order(seq1[i])/2); b:=IntegerRing()!(Order(seq2[j])/2);
test,h:= IsConjugate(G,seq1[i]^a,seq2[j]^b);
if test then for c in Centralizer(G,seq1[i]^a) do
Append(~TorsH, T1xT2.i^a * ((T1xT2.(j+5)^b)^(inT2((h^-1*c) @@ f2))));
end for; end if;
end if; end for; end if; end for;
return T1xT2,H, TorsH;
end function;
