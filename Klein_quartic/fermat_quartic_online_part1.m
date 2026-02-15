// Fermat quartic x^4+y^4+z^4=0: Aut action on J[2]
// Part 1: Compute the action matrices
// For the Magma online calculator

p := 89; Fp := GF(p);
iv := Sqrt(Fp!(-1));
r4 := [Fp!1, iv, Fp!(-1), -iv];

// Function field and class group
Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FF<uu> := FunctionField(u^4 + t^4 + 1);
et := FF!t; eu := uu;
Cl, m := ClassGroup(FF);
invs := Invariants(Cl);
printf "Cl invariants: %o\n", invs;

// J[2] via even invariants
eidx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
assert #eidx eq 6;
F2 := GF(2); V6 := VectorSpace(F2, 6);
function R2(c) es:=Eltseq(c); return V6![F2!es[eidx[j]]:j in [1..6]]; end function;

// Degree-1 places with nonzero coords
deg1 := Places(FF, 1);
printf "#deg1 places: %o\n", #deg1;
pd := []; // <place, a, b>
for P in deg1 do
    a:=Evaluate(et,P); b:=Evaluate(eu,P);
    if a ne 0 and b ne 0 then Append(~pd, <P,a,b>); end if;
end for;
printf "#usable places: %o\n", #pd;

// Place lookup
plk := AssociativeArray();
for d in pd do plk[<d[2],d[3]>]:=d[1]; end for;
for P in deg1 do a:=Evaluate(et,P); b:=Evaluate(eu,P); plk[<a,b>]:=P; end for;

// Basis for J/2J from [P_i - ref]
ref := pd[1];
bp := []; bv := []; sp := sub<V6|>;
for i in [2..#pd] do
    D := 1*pd[i][1] - 1*ref[1]; c := D @@ m; v := R2(c);
    if v ne V6!0 and v notin sp then
        Append(~bp, <pd[i], ref>); Append(~bv, v);
        sp := sub<V6|sp,v>;
        if Dimension(sp) eq 6 then break; end if;
    end if;
end for;
if #bv lt 6 then
    for i in [1..#pd] do for j in [i+1..#pd] do
        D:=1*pd[i][1]-1*pd[j][1]; c:=D@@m; v:=R2(c);
        if v ne V6!0 and v notin sp then
            Append(~bp,<pd[i],pd[j]>); Append(~bv,v);
            sp:=sub<V6|sp,v>;
            if Dimension(sp) eq 6 then break i; end if;
        end if;
    end for; end for;
end if;
assert #bv eq 6;
Bm := Matrix(F2,[Eltseq(v):v in bv]);
Bi := Bm^(-1);
printf "J/2J basis found\n";

// 96 automorphisms: P_sigma * diag(1,beta,gamma)
SP := [Matrix(Fp,3,3,[1,0,0,0,1,0,0,0,1]),
       Matrix(Fp,3,3,[0,1,0,1,0,0,0,0,1]),
       Matrix(Fp,3,3,[0,0,1,0,1,0,1,0,0]),
       Matrix(Fp,3,3,[1,0,0,0,0,1,0,1,0]),
       Matrix(Fp,3,3,[0,0,1,1,0,0,0,1,0]),
       Matrix(Fp,3,3,[0,1,0,0,0,1,1,0,0])];
SN := ["id","(12)","(13)","(23)","(123)","(132)"];

al := []; // <matrix, label>
for si in [1..6] do for b in r4 do for g in r4 do
    M := SP[si]*DiagonalMatrix(Fp,[1,b,g]);
    Append(~al, <M, Sprintf("%o*D(1,%o,%o)",SN[si],b,g)>);
end for; end for; end for;
assert #al eq 96;

// Compute action matrices
function AA(M,a,b)
    v:=M*Matrix(Fp,3,1,[a,b,1]);
    return v[1,1]/v[3,1], v[2,1]/v[3,1];
end function;

af := []; // F2 action matrices
for k in [1..96] do
    M := al[k][1]; iv2 := [];
    for j in [1..6] do
        Pd:=bp[j][1]; Qd:=bp[j][2];
        a1,b1:=AA(M,Pd[2],Pd[3]); a2,b2:=AA(M,Qd[2],Qd[3]);
        D:=1*plk[<a1,b1>]-1*plk[<a2,b2>]; c:=D@@m;
        Append(~iv2, R2(c));
    end for;
    Cm := Matrix(F2,[Eltseq(v):v in iv2]);
    Append(~af, Bi*Cm);
end for;

// Verify
for k in [1..96] do assert Determinant(af[k]) ne 0; end for;
assert af[1] eq IdentityMatrix(F2,6);
G := sub<GL(6,F2)|af>;
printf "|Image| = %o, type = %o\n", #G, GroupName(G);
ker := [k:k in [1..96]|af[k] eq IdentityMatrix(F2,6)];
printf "Kernel size: %o\n", #ker;
if #ker gt 1 then for k in ker do printf "  ker: %o\n",al[k][2]; end for; end if;

// Orbits and stabilizers
print "\n=== ORBITS ON J[2]\\{0} ===";
vis := {};
for vec in V6 do
    if vec eq V6!0 or vec in vis then continue; end if;
    orb := {vec}; si := [];
    for k in [1..96] do
        img := vec*af[k]; Include(~orb,img);
        if img eq vec then Append(~si,k); end if;
    end for;
    vis join:= orb;
    S := sub<GL(6,F2)|[af[k]:k in si]>;
    printf "\nOrbit size %o, |Stab| = %o, Stab = %o\n", #orb, #si, GroupName(S);
    printf "  Rep: %o\n", vec;
    printf "  Stab PGL(3) matrices:\n";
    for k in si do printf "    %o\n", Eltseq(al[k][1]); end for;
end for;

// Individual class table
print "\n=== ALL 63 CLASSES ===";
printf "%-20o  |Stab|  Type\n","Class";
for vec in V6 do
    if vec eq V6!0 then continue; end if;
    si:=[k:k in [1..96]|vec*af[k] eq vec];
    if #si gt 0 then S:=sub<GL(6,F2)|[af[k]:k in si]>; sn:=GroupName(S);
    else sn:="1"; end if;
    printf "%-20o  %-6o  %o\n", vec, #si, sn;
end for;
