// Code for paper "PRODUCT-QUOTIENT SURFACES: NEW INVARIANTS AND ALGORITHMS"

// We are looking for regular product-quotient surfaces.

// Three main inputs: pg, gamma and M. 
// pg is the genus of the surface we want to construct.
// gamma+pg equals half of the codimension of the space we 
// know in H^{1,1}.
// M is the maximal multiplicity of a singular point.
// Baskets(pg,gamma,M) will compute all baskets which fulfill 
// all the numerical inequalities we know for a basket of
// singularities of a product-quotient surface with the given 
// value of those three numbers

// First we define mu of the basket. Since it only depends on 
// the denominators we make it as a function on a multiset of 
// positive integers: we will run it in the denominators 
// of the basket.

mu:=function(multisetofint)
   w:=0; for i in multisetofint do w+:=(1-1/i); end for; return w;
end function;

// The next program which produces all multisets of integers
// with minimal integer 2, maximal integer M (second input) and
// mu<=Sm. 

MultisetsByMuandMprel:=function(Sm,M)
     output:={ {* *} };
     if M gt 1 and Sm ge 1-1/M then output:={}; NSm:=Sm-1+1/M; 
       if NSm lt 1 then NM:=Min(M,Floor(1/(1-NSm)));
       else NM:=M;
       end if;
       for k in [1..NM] do
         for lil in $$(NSm,k) do
          Include(~output,Include(lil,M));           
     end for; end for; end if;
return output;
end function;

// Moreover we require that M itself divides the Lcm of all
// other entries (else there is no basket with these 
// multiplicities passing the test "TestBasket" below).

MultisetsByMuandM:=function(Sm,M)
  output:={ };
  for mults in MultisetsByMuandMprel(Sm,M) do 
    if #mults ge 2 then test:=true;
      for a in MultisetToSet(mults) do
        if not IsIntegral(Lcm(Exclude(mults,a))/a) then 
          test:= false; break a;     
      end if; end for;
      if test then Include(~output,mults);     
  end if; end if; end for;      
return output;
end function;

// Now we produce all multiplicities with xi>=1/2, equivalently
// mu<= 4pg+2gamma+7/2 

Mults:=function(pg,gamma,M)
  if M eq 1 then return { {* *} };
  else return MultisetsByMuandM(4*pg+2*gamma+7/2, M);
  end if;
end function;

// The multiplicities determine mu. We know that, fixed xi
// and a multiplicity, there are finitely many compatible
// signatures (m_1,..,m_r). We look for this list.


// First we set the divisibility test: each multiplicity 
// divides at least an m_i

Test:=function(mult,type)
bool:=true;   
   for n in mult do booln:=false;
     for m in type do
         if m/n in IntegerRing() then booln:=true; break m;
     end if; end for; 
   if not booln then bool:=false; break n; 
   end if; end for;
return bool;
end function;

// Now we find the list, by using all conditions we know.
// Some of them involve the index of the basket, which do not 
// depend only on the multiplicities. Anyway, fixed the 
// multiplicities, the biggest possible index is reached by
// the basket with all numerators equal to 1, and the indices
// of the other baskets is a divisor of it.
// We call I the index of this basket.
// The conditions we know are then:
// a) r<=xi+4;
// b) Theta>0 ==> r>=3
// c) m_i<12(xi+1)
//   if I=1 (e.g. if all the multiplicities are two<9, then 
//          (since f=1/6) m_i<=6(xi+1)
//   if r>3, m_i< 6+2(2xi+1)/(r-3)
//   if r>3, m_i<= 2(xi*I+1)/(r-3)
// d) out of |B|/2 indices the bounds of b) can be improved as
//    for r=3, m_i<= 6+3*xi
//    for r>3, m_i<=(xi+2)/(r-3)
// e) xi/2 Theta, I*xi/m_i*Theta are positive integers
// f) out of |B|/2 indices xi/(2*Theta*m_i) is integral
// g) each multiplicity divides at least an m_i 
// h) mi <= 2(xi/Theta +3)
// TypesByMults first compute those of length 3, then those of 
// bigger length.

TypesByMults:=function(mults,xi)
    output:={ }; 
    Exc:=Floor(#mults/2);
    I:=Lcm(Exclude(Set(Include(mults,2)),2)); 
    MaxM3:=Floor(Min(6*(1+I*xi), Ceiling(12*xi+11)));  
    MaxM3i:=Floor(3*(2+xi));
  if Exc ge 3 then T:=Multisets({x: x in [2..MaxM3]}, 3);
  else T:={};
    for k in [0..Exc] do
    for Txr3B in Multisets({x: x in [2..MaxM3i]},3-k) do
    for Txr3E in Multisets({x: x in [1+MaxM3i..MaxM3]},k) do
          Include(~T, Txr3B join Txr3E);
  end for; end for; end for; end if;
   MaxM4:=Floor(Min(2*(1+I*xi), Ceiling(4*xi+7)));  
   MaxM4i:=Floor(2+xi);
  for r in [4..Floor(4+xi)] do
    if Exc ge r then T:=T join Multisets({x: x in [2..MaxM4]}, r);
    else 
      for k in [0..Exc] do
      for TxrB in Multisets({x: x in [2..MaxM4i]},r-k) do
      for TxrE in Multisets({x: x in [1+MaxM4i..MaxM4]},k) do
          Include(~T, TxrB join TxrE);
  end for; end for; end for; end if; end for;
  for cand in T do Theta:=-2+mu(cand);
    if Theta gt 0 and
       Max(cand) le 2*(3+xi/Theta) and 
       xi/(2*Theta) in IntegerRing() and 
       Test(mults,cand) and
       forall{n : n in cand | xi*I/(Theta*n) in IntegerRing()} 
        then b:=0;
        for n in cand do
          if xi/(2*Theta*n) notin IntegerRing() then b +:=1;
        end if; end for;
        if b le Exc then Include(~output,cand);           
        end if; 
   end if; end for; 
return output;
end function;

// Now we need a script for computing all baskets related to a 
// certain multiplicity. First we need to compute the 
// continued fraction of a rational  number and viceversa the 
// rational number of a continued fraction: these are 
// respectively the programs 
// ContFrac: for 0<s<1, the continued fraction of 1/s, 
// RatNum: computes 1/s from the continued fraction.

ContFrac:=function(s)
  CF:=[ ]; r:=1/s;
  while not IsIntegral(r) do
    Append(~CF, Ceiling(r)); r:=1/(Ceiling(r)-r);
  end while;
  return Append(CF, r);
end function;

Nq:=func<cf|#cf eq 1 select cf[1] else cf[1]-1/$$(Remove(cf,1))>;

RatNum:=func<seq|1/Nq(seq)>;

// We produce a representative for every quotient singularity 
// of multiplicity n, up to "duality", where the dual of q/n
// which we define immediately after, is q'/n with qq'-1 
// multiple of n. Then we produce all baskets of singularities 
// with prescribed multiplicities

QuotSings:=function(n)
  sings:={};
  for q in [1..n-1] do
    if Gcd(q,n) eq 1 and Modinv(q,n) ge q then
      Include(~sings,q/n);
  end if; end for;
return sings;
end function;

BasketsWM:=function(multiplicities)
  set:={ {* *} };
  for n in multiplicities do temp:={};
    for basket in set do
      for rat in QuotSings(n) do
	  Include(~temp,Include(basket,rat));
    end for; end for;
  set:=temp;
  end for;
return set;
end function;

// We compute Gamma of a rational and then (GammaBas) of a 
// basket

Dual:=func<r|Modinv(Numerator(r),Denominator(r))/Denominator(r)>;

Gamma:=func<r|(&+(ContFrac(r))-3*#(ContFrac(r))+r+Dual(r))/6>;

GammaBas:=function(bas)
   g:=0; for rat in bas do g+:=Gamma(rat); end for; return g;
end function;

// Not all basket are ok for us; we know that the trace must 
// be integral up to duality (Lemma 1.7 of [BP]); we need a
// script testing it. By choosing the fibration, we can 
// "block" one singularity, using the duality only on the 
// other singularities.
    
TestBasket:=function(basket)
  if #basket eq 0 then test:=true; 
  else test:=false; basseq:=[];
    for r in basket do Append(~basseq,r); end for;
    setofseqs:={ basseq };
    for i in [2..#basseq] do newseqs:={};
      for seq in setofseqs do
        Include(~newseqs,
             Insert(Remove(seq,i),i,Dual(seq[i])));
      end for;
      setofseqs:=setofseqs join newseqs;
    end for;
    for seq in setofseqs do
      if IsIntegral(&+(seq)) then test:=true; break;
      end if;
    end for;
  end if;
  return test;
end function;

// Here we produce all baskets with prescribed multiplicities 
// and gamma passing the test
 
Baskets:=function(multiplicities,gamma)
    set:={};
  for basket in BasketsWM(multiplicities) do 
    if GammaBas(basket) eq gamma and TestBasket(basket) then
      Include(~set, basket);
  end if; end for;
return set;
end function;

// ListOfTypes computes, for all multiplicities mults in 
// Mults(pg,gamma,M), 
// 1) TypesByMults(mults,xi=4+4pg+2gamma-mu)
// 2) Baskets(mults,gamma)
// returning the outputs only when both are non empty in a 
// list 

ListOfTypes:=function(pg,gamma,M)
  S:=[* *]; mults:=Mults(pg,gamma,M); 
  for mult in mults do 
    mue:=mu(mult);
    T:=TypesByMults(mult,4+4*pg+2*gamma-mue);
    if not #T eq 0 then 
      B:=Baskets(mult,gamma);
      if not #B eq 0 then
        Append(~S,[* B, T *]);
  end if; end if; end for;
 return S;
end function;

// Now it is time to work on finite groups.
// We need some useful tools. ElsOfOrd extract from the finite 
// group "group" all elements of order "order".

ElsOfOrd:=function(group,order)
  Els:={ };
  for g in group do if Order(g) eq order then Include(~Els, g);
  end if; end for;
  return Els;
end function;

// TuplesOfGivenOrder creates a sequence of the same length as 
// the input sequence seq, whose entries are subsets of the 
// group in the input, and precisely the subsets of elements 
// of order the corresponding entry of seq

TuplesOfGivenOrders:=function(group,seq)
  SEQ:=[];
  for i in [1..#seq] do
    if IsEmpty(ElsOfOrd(group,seq[i])) then SEQ:=[]; break i;
    else Append(~SEQ,ElsOfOrd(group,seq[i]));
    end if;
  end for;
  return SEQ;
end function;

// These two transform a multiset, resp. a tuple, into a 
// sequence.

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

// This script checks if a group has a set of spherical 
// generators of the prescribed signature.

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

// The next script runs a systematic search on all finite 
// groups and produces the list of all triples 
// (basket, pair of signatures, group)
// such that
// 1) Basket and signature are in ListOfTypes(pg,gamma,M);
//    so one singularity of multiplicity M, no singularity 
//    of higher multiplicity and all conditions discussed 
//    up to now
// 2) the group has order xi/(Theta_1*Theta_2) and has
//    sets of spherical generators of both signatures.
// If one of the signatures is {*2,3,7*} the group must be 
// perfect, so in this case the program first checks if there 
// are perfect groups of the right order: if the answer is 
// negative it jumps directly to the next case.
// The program skips to check the groups of order bigger than 
// maxordG (a parameter which can be set by the user, by default 
// 2000), 1024 (since there is no complete list avalaible) or 
// of orders in the set "badorders" which can be chosen by the 
// user. These skipped cases are listed in the second output, 
// and must be considered separately.

ListGroups:=function(pg,gamma,M: 
      badorders:={256,512,768,1152,1280,1536,1728,1792,1920}, maxordG:=2000)
  checked:=[* *]; tocheck:=[* *];
  for pair in ListOfTypes(pg,gamma,M) do
    types:=pair[2]; 
    for basket in pair[1] do  
      den:={* *}; 
      for s in basket do 
        Include(~den,Denominator(s)); 
      end for;
      mue:=mu(den); 
      xi:=4*pg+2*gamma+4-mue;    
      for pairoftypes in Multisets(types,2) do 
        ord:=xi;
        for T in pairoftypes do 
          ord:=ord/(mu(T)-2);
        end for;
        if IsIntegral(ord) then
          if {*2,3,7*} in pairoftypes and
             NumberOfGroups(PerfectGroupDatabase(),IntegerRing()!ord) eq 0
       then ;
          elif ord gt maxordG or ord in Include(badorders,1024) 
            then Append(~tocheck, [* basket, pairoftypes, ord *]);
          else 
            for G in SmallGroups(IntegerRing()!ord: Warning := false) do
              test:=true;
              for T in pairoftypes do
                if not ExSphGens(G,T) then test:=false; break T;
              end if; end for;
              if test then Append(~checked, [* basket, pairoftypes, G *]);
     end if; end for; end if; end if; end for; end for; end for;
 return checked, tocheck;
end function;

Conjug:=function(seq,elt)
  output:=[];
   for h in seq do Append(~output,h^elt);
   end for;
  return output;
end function;

// The next program computes all possible sets of spherical 
// generators of a group of a prescribed signature and returns 
// (to spare memory) only one of these sets for each conjugacy 
// class.

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

// Given two sets of spherical generators, the singular points 
// of the resulting surface are the image of points in the 
// product of curves C_1xC_2 having nontrivial stabilizer. These 
// correspond to 4-tuple (g_1,n_1,g_2,n_2) where
// - g_1 is a generator of the first set;
// - 1<=n_1<ord(g_1); 
// - g_2 is a generator of the second set;
// - 1<=n_2<ord(g_2); 
// - g_1^n_1=g_2^n_2
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

// We could use it to compute the basket of singularities of 
// every constructed surface, but this is too expensive for our 
// purposes. The next program only checks if, given two sets of 
// spherical generators and a "candidate" basket, the resulting 
// surface has the prescribed basket. The advantage is that in 
// the wrong cases, the script stops when it finds a "forbidden" 
// singularities, without losing time computing all the other 
// singular points.

CheckSings:=function(basket,gens1,gens2,group)
  test:=true; bas:=basket;
    for gen1 in gens1 do
    for gen2 in gens2 do pb:=BasketByAPairOfGens(group,gen1,gen2);
      for r in pb do r1:=RatNum(Reverse(ContFrac(r)));
      if r in bas then Exclude(~bas,r);
         elif r1 in bas then Exclude(~bas,r1);
         else test:=false; break gen1;
      end if; end for;
    end for; end for;
  return test and IsEmpty(bas);
end function;

// The next script computes all regular product-quotient 
// surfaces with given p_g, gamma and M. It uses the first 
// output of ListGroups, so it does not consider the cases 
// in its second output

ExistingSurfaces:=function(pg,gamma,M: 
    BO:={256,512,768,1152,1280,1536,1728,1792,1920}, moG:=2000)
  N:=[* *]; 
  L,T:=ListGroups(pg,gamma,M: badorders:=BO, maxordG:=moG);
  for triple in L do
    basket:=triple[1]; 
    pairsoftypes:=triple[2]; 
    group:=triple[3]; 
    Types:=[]; 
    for type in pairsoftypes do Include(~Types,type); 
    end for;
    SetGens1:=SphGenUpToConj(group,Types[1]);
    if #Types eq 1 
      then SetGens2:=SetGens1;
    else SetGens2:=SphGenUpToConj(group,Types[2]);
    end if;
    test:=false;
      for gens1 in SetGens1 do
        for gens2 in SetGens2 do
          if CheckSings(basket,gens1,gens2,group) then test:=true; 
              break gens1;
           end if;
      end for; end for;
      if test then l:=0;
	   for q in basket do l+:=#ContFrac(q); 
        end for;
        Append(~N, [* basket, 8*pg+8-2*gamma-l, pairsoftypes, IdentifyGroup(group)*]);
  end if;  end for;
return N, T;
end function;

// The remaining part of the script is a essentially a 
// cut-and-paste from our previous script "Orbifold.magma", 
// to compute all surfaces corresponding to each entry of the 
// output of ExistingSurfaces, and compute their fundamental 
// group.

// The next scripts creates the Automorphism Group of a group as 
// an explicit set.

AutGr:=
  function(gr)
    Aut:=AutomorphismGroup(gr); A:={ Aut!1 };
    repeat
      for g1 in Generators(Aut) do
      for g2 in A do
      Include (~A,g1*g2);
      end for; end for;
    until  #A eq #Aut;
  return A;
end function;

// The next script creates the Hurwitz move.

HurwitzMove:=
  function(seq,idx)
  return Insert(Remove(seq,idx),idx+1,seq[idx]^seq[idx+1]);
end function;

// This script, starting from a sequence of elements of a group,
// creates all sequences of elements which are equivalent to the 
// given one for the equivalence relation generated by Hurwitz 
// moves, and returns (to spare memory) only the ones whose 
// entries have never increasing  order.

HurwitzOrbit:=
  function(seq)
  orb:={ }; shortorb:={  }; Trash:={ seq };
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
      if test then Include(~shortorb, gens);
      end if;
    end for;
  return shortorb;
end function;

// Now we create all sets of spherical generators of a group of 
// a prescribed signature.

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

// The next program finds all
// surfaces with a given group, pair of signatures and basket 
// (must be run on the outputs of ExistingSurfaces).

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

// The next script, FindCurves, uses the same argument of 
// FindSurfaces to find all curves with a given signature and 
// group, modulo Hurwitz moves and inner automorphisms of the 
// group.

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
   for i in [1..n[1]+n[2]] do Append(~vars,G1xG2.i); end for;
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

// The next script computes, given two maps A->B (careful, they 
// MUST have same source and same target) the map product 
// induced by the product on B

MapProd:=function(map1,map2)
  seq:=[]; G:=Domain(map1); H:=Codomain(map1);
  if Category(G) eq GrpPC then n:=NPCgens(G); 
  else n:=NumberOfGenerators(G); end if;
  for i in [1..n] do Append(~seq,map1(G.i)*map2(G.i)); end for;
  return hom<G->H|seq>;
end function;

// Finally, this program computes the fundamental group of a 
// product-quotient surface.

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



