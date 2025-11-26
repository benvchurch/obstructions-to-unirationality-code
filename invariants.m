/*******************************************************************************
 * invariants.m
 *
 * Purpose:
 *   Core library for computing invariants of product-quotient surfaces.
 *   Provides functions for singularity baskets, continued fractions, and
 *   numerical invariants (K^2, Segre number, diagonal form number, etc.)
 *
 * Main functions:
 *   - ContFrac(s): Compute continued fraction expansion of 1/s for 0 < s < 1
 *   - RatNum(seq): Reconstruct rational from continued fraction
 *   - QuotSings(n): Representatives for quotient singularities of multiplicity n
 *   - BasketsWM(mults): Generate baskets of singularities with given multiplicities
 *   - BasketByAPairOfGens(G, g1, g2): Compute singular points from generator pair
 *   - Gamma(r), GammaBas(bas): Gamma function for singularities
 *   - k(r), l(r), e(r): Numerical invariants of quotient singularities
 *   - K2, SegreNumber, DiagonalFormNumber: Surface invariant computations
 *   - Pi1, MyPi1: Fundamental group computations for product-quotient surfaces
 *   - HodgeDiamond: Display Hodge diamond of a surface
 *
 * Dependencies:
 *   None (standalone library)
 *
 * Usage:
 *   load "invariants.m";
 *   // or
 *   import "invariants.m": k, ContFrac, l, K2, SegreNumber;
 *
 * Mathematical background:
 *   Product-quotient surfaces are (C1 x C2)/G where C1, C2 are curves and G
 *   is a finite group acting freely on the product outside finitely many points.
 *   The singularities are cyclic quotient singularities classified by rationals.
 ******************************************************************************/

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


/* compute the numerical invariants of a quotient singularity (1, a)/n represented as the rational number a/n */

l := function(r)
    return #(ContFrac(r));
end function;

e := function(r)
    return l(r) + 1 - 1/Denominator(r);
end function;

k := function(r)
    return -2 + 2/Denominator(r) + r + Dual(r) + &+(ContFrac(r)) - 2 * l(r);
end function;

// returns a baset of singularities as well as the numerical invairants

ComputeBasket:=function(gens1,gens2,group)
    lTot := 0;
    eTot := 0;
    kTot := 0;
    totalBasket := [];
    for gen1 in gens1 do
    for gen2 in gens2 do pb:=BasketByAPairOfGens(group,gen1,gen2);
      for r in pb
        do 
        lTot := lTot + l(r);
        eTot := eTot + e(r);
        kTot := kTot + k(r);
        totalBasket := Append(totalBasket, r);
       end for;
    end for;
    end for;
    return totalBasket, lTot, eTot, kTot;
end function;

ComputeS:=function(gens1,gens2,group)
    S := 0;
    totalBasket := [];
    for gen1 in gens1 do
    for gen2 in gens2 do pb:=BasketByAPairOfGens(group,gen1,gen2);
      for r in pb
        do 
        S := S + e(r) + k(r);
        totalBasket := Append(totalBasket, r);
       end for;
    end for;
    end for;
    return S;
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
  if Category(G1) eq GrpPC then n:=[NPCgens(G1),NPCgens(G2)];
  else n:=[NumberOfGenerators(G1),NumberOfGenerators(G2)]; end if;
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

/* use pair of sequences of group elements to compute Pi as before */

Checks := function(pairsofseqs, gr)
  if #pairsofseqs ne 2 then
    error "error: pairsofseqs must be a list of two sequences of group elements";
  end if;
  if &* pairsofseqs[1] ne Id(gr) then
    error "error: pairsofseqs[1] must be a list of spherical elements";
  end if;
  if &* pairsofseqs[2] ne Id(gr) then
    error "error: pairsofseqs[2] must be a list of spherical elements";
  end if;
  if not sub<gr | pairsofseqs[1]> eq gr then
    error "error: pairsofseqs[1] does not generate gr";
  end if;
  if not sub<gr | pairsofseqs[2]> eq gr then
    error "error: pairsofseqs[2] does not generate gr";
  end if;
  return true;
end function;

// only takes sequences of length 3 as input

Pi1:=function(seq1,seq2, G) /* the arguments are sequences of elements of the monodromy group G */
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

Pi1_v2:=function(pairsofseqs,gr)
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
            (((T1xT2.(j+#pairsofseqs[1]))^d2)^(inT[2]((h^-1*c) @@ f2))));
    end for; end if;
  end for; end for; end for; end for;
  return Simplify(quo<H|rels>);
end function;

MyPi1:=function(pairsofseqs,gr)
  Checks(pairsofseqs, gr);
  T1,f1:=PolyGroup(pairsofseqs[1],gr); 
  T2,f2:=PolyGroup(pairsofseqs[2],gr);
  T1xT2,inT,proT:=DirProd(T1,T2); 
  grxgr,inG:=DirectProduct(gr,gr);
  Diag:=MapProd(inG[1],inG[2])(gr);
  f:=MapProd(proT[1]*f1*inG[1],proT[2]*f2*inG[2]);
  
  // Get the preimage of the diagonal
  H, rewrite_map := Rewrite(T1xT2,Diag@@f);
  
  // Create additional relations
  torsion_rels := [];

  for i in [1..#pairsofseqs[1]] do
    g1 := pairsofseqs[1][i];
    for j in [1..#pairsofseqs[2]] do
      g2 := pairsofseqs[2][j];
      for d1 in [1..Order(g1) - 1] do
        for d2 in [1..Order(g2) - 1] do
          test, h := IsConjugate(gr, g1^d1, g2^d2);
          if test then
            for c in Centralizer(gr, g1^d1) do
              rel := T1xT2.i^d1 * ((T1xT2.(j + #pairsofseqs[1])^d2)^(inT[2]((h^-1 * c) @@ f2)));
              if not rel in Domain(rewrite_map) then
                print "issue";
              else
                Append(~torsion_rels, rewrite_map(rel));
              end if;
            end for;
          end if;
        end for;
      end for;
    end for;
  end for;
  // Return the quotient
  return Simplify(quo<H | torsion_rels>);
end function;

ChiCurve := function(mult, ordG)
    s := -2;
    for m in mult do
        s := s + (1 - 1/m);
    end for;
    return s * ordG;
end function;


ChiCurvePermutation := function(action, elements, degree)
    s := (-2) * degree;
    for g in elements do
        cycles := CycleStructure(action(g));
        for pair in cycles do 
            s := s + (pair[1] - 1) * pair[2];
        end for;
    end for;
    return s;
end function;

K2 := function(pairofseqs, G)
    ord1 := [Order(g) : g in pairofseqs[1]];
    ord2 := [Order(g) : g in pairofseqs[2]];
    totalBasket, lTot, eTot, kTot := ComputeBasket(pairofseqs[1], pairofseqs[2], G);
    return 2*ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - kTot;
end function;

SegreNumber := function(pairofseqs, G)
    ord1 := [Order(g) : g in pairofseqs[1]];
    ord2 := [Order(g) : g in pairofseqs[2]];
    totalBasket, lTot, eTot, kTot := ComputeBasket(pairofseqs[1], pairofseqs[2], G);
    return ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - eTot - kTot;
end function;

RR13Number := function(pairofseqs, G)
    ord1 := [Order(g) : g in pairofseqs[1]];
    ord2 := [Order(g) : g in pairofseqs[2]];
    totalBasket, lTot, eTot, kTot := ComputeBasket(pairofseqs[1], pairofseqs[2], G);
    return 2*(ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - eTot - kTot) + eTot + kTot;
end function;

IsCanonical := function(r)
  return (Denominator(r) * r eq Denominator(r)-1) or (Denominator(Dual(r)) * Dual(r) eq Denominator(Dual(r))-1);
end function;


BruinNumber := function(pairofseqs, G)
    ord1 := [Order(g) : g in pairofseqs[1]];
    ord2 := [Order(g) : g in pairofseqs[2]];
    totalBasket, lTot, eTot, kTot := ComputeBasket(pairofseqs[1], pairofseqs[2], G);
    S := 0;
    for r in totalBasket do
      if IsCanonical(r) then 
        n := Denominator(r) - 1;
        if n eq 1 then  
          S := S + 4/27;
        elif n eq 2 then
          S := S + 67/216;
        else
          S := S + ((n + 1)^2 - 1)/(n + 1)*1/6 - 0.1932;
        end if;
      end if;
    end for;
//    print "Genus: ", (ChiCurve(ord1, Order(G)) + 2)/2, (ChiCurve(ord2, Order(G)) + 2)/2;
    return 1/6*(ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - eTot - kTot) + S;
end function;

DiagonalFormNumber := function(pairofseqs, G)
    ord1 := [Order(g) : g in pairofseqs[1]];
    ord2 := [Order(g) : g in pairofseqs[2]];
    totalBasket, lTot, eTot, kTot := ComputeBasket(pairofseqs[1], pairofseqs[2], G);
    singConditions := 0;
    for r in totalBasket do
      if IsCanonical(r) then 
        singConditions := singConditions + 2;
      else 
        singConditions := singConditions + 3 * (&+ContFrac(r) - 2 * l(r)) + 2;
      end if;
    end for;
    
    return 2*ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - kTot - singConditions;
end function;

HodgeDiamond := function(pairofseqs, G)
    ord1 := [Order(g) : g in pairofseqs[1]];
    ord2 := [Order(g) : g in pairofseqs[2]];
    totalBasket, lTot, eTot, kTot := ComputeBasket(pairofseqs[1], pairofseqs[2], G);
    K2 := 2*ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - kTot;
    Segre := ChiCurve(ord1, Order(G))*ChiCurve(ord2, Order(G))/Order(G) - eTot - kTot;
    c2 := (K2 - Segre);
    chiO := (K2 + c2)/12; // Noether's formula
    q := 0; // iregularity zero by assumption
    h20 := chiO - 1; // use euler characteristic of O_X 
    h11 := c2 - 2 - 2 * h20; // the sum of the cohomology is the topological euler characteristic;
    print"\n";
    print " "," ","1";
    print " ","0", " ", "0";
    print h20, " ", h11, " ", h20;
    print " ","0", " ", "0";
    print " "," ","1";
    print"\n";
    return h20, h11;
end function;

runData := function(G, seq1, seq2)
    totalBasket, lTot, eTot, kTot := ComputeBasket(seq1, seq2, G);
    print "totalBasket: ", totalBasket;
    print "Number of Singularities: ", #totalBasket;
    print "K2: ", K2([seq1,seq2],G);
    print "Segre: ", SegreNumber([seq1,seq2],G);
    print "RR13: ", RR13Number([seq1, seq2], G);
    print "Bruin: ", BruinNumber([seq1, seq2], G);
    print "Diagonal: ", DiagonalFormNumber([seq1, seq2], G);
    //print "pi_1: ", Order(Pi1([seq1, seq2], G));
    return "";
end function;

findData := function(G, seq1, seq2)
    if Order(Pi1([seq1, seq2], G)) ne 1 then
        return false;
    end if;
    
    rr13 := RR13Number([seq1, seq2], G);
    bruin := BruinNumber([seq1, seq2], G);
    diagonal := DiagonalFormNumber([seq1, seq2], G);
    
    return rr13 gt 0 or bruin gt 0 or diagonal gt 0;
end function;


