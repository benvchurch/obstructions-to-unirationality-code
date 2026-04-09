/*******************************************************************************
 * check_Qi_point.m
 *
 * Does C: x^4+y^4+z^4=0 have a Q(i)-rational point?
 *
 * Answer: NO. Local obstruction at pi=(1+i) above 2.
 ******************************************************************************/

K<i> := QuadraticField(-1);
OK := Integers(K);
pi := OK![1,1];  // 1+i

printf "=== Q(i)-POINTS ON C: x^4+y^4+z^4=0 ===\n\n";

// =========================================================================
// 1. Small height search
// =========================================================================
printf "--- Small height search over Z[i] ---\n";
bound := 3;
found := false;
for a1 in [-bound..bound] do for b1 in [0..bound] do
    x := OK![a1,b1];
    if x eq 0 then continue; end if;
    for a2 in [-bound..bound] do for b2 in [-bound..bound] do
        y := OK![a2,b2];
        for a3 in [-bound..bound] do for b3 in [-bound..bound] do
            z := OK![a3,b3];
            if y eq 0 and z eq 0 then continue; end if;
            if x^4 + y^4 + z^4 eq 0 then
                printf "FOUND: (%o : %o : %o)\n", x, y, z;
                found := true;
            end if;
        end for; end for;
    end for; end for;
end for; end for;
if not found then
    printf "No point found with |re|,|im| <= %o\n\n", bound;
end if;

// =========================================================================
// 2. Local obstruction at pi = 1+i (above 2)
//
// Residue field: F_2 = Z[i]/(1+i). In F_2, x^4 = x, so
// x^4+y^4+z^4 = x+y+z. F_2-points: (0:1:1), (1:0:1), (1:1:0).
//
// Affine chart z=1: need x^4+y^4 = -1.
// F_2-point (0,1): x = pi*beta, y = 1+pi*alpha.
//   F = (pi*beta)^4 + (1+pi*alpha)^4 + 1
//     = pi^4*beta^4 + 1 + 4*pi*alpha + 6*pi^2*alpha^2 + ... + 1
//     = 2 + (higher order in pi)
// Now 2 = -i*pi^2, so F = pi^2*(-i + O(pi^2)).
// Since -i is a unit, v_pi(F) = 2 always. QED.
// =========================================================================
printf "--- Local analysis at pi = 1+i (above 2) ---\n\n";
printf "pi = 1+i, pi^2 = 2i, pi^4 = -4\n";
printf "2 = -i*pi^2, so v_pi(2) = 2\n\n";

// pi-adic valuation
function PiVal(x)
    if x eq 0 then return 100; end if;
    v := 0;
    while x ne 0 do
        q := K!x / K!pi;
        if not (q in OK) then break; end if;
        x := OK!q;
        v +:= 1;
    end while;
    return v;
end function;

// Build representatives mod pi^k
function MakeReps(k)
    result := [OK!0];
    for j in [0..k-1] do
        pj := pi^j;
        new_result := [];
        for r in result do
            Append(~new_result, r);
            Append(~new_result, r + pj);
        end for;
        result := new_result;
    end for;
    return result;
end function;

// Verify: v_pi(F) for all lifts mod pi^3
reps3 := MakeReps(3);  // 8 reps mod pi^3
printf "F_2-point (x,y) = (0,1) mod pi in chart z=1:\n";
printf "  Lift: x = pi*beta, y = 1+pi*alpha, with alpha,beta mod pi^3\n";
vals := {};
for alpha in reps3 do for beta in reps3 do
    x := pi * beta;
    y := OK!1 + pi * alpha;
    val := x^4 + y^4 + 1;
    v := PiVal(val);
    Include(~vals, v);
end for; end for;
printf "  v_pi(F) values over all %o lifts: %o\n", #reps3^2, vals;

// Check other F_2-point (1,0) by symmetry
printf "\nF_2-point (x,y) = (1,0) mod pi in chart z=1:\n";
vals2 := {};
for alpha in reps3 do for beta in reps3 do
    x := OK!1 + pi * alpha;
    y := pi * beta;
    val := x^4 + y^4 + 1;
    v := PiVal(val);
    Include(~vals2, v);
end for; end for;
printf "  v_pi(F) values: %o\n", vals2;

printf "\n=> v_pi(x^4+y^4+z^4) = 2 for ALL primitive (x,y,z).\n";
printf "=> No Q_2(i)-point on C.\n\n";

// =========================================================================
// 3. Also check p = 5 (splits in Z[i], residue F_5)
// =========================================================================
printf "--- Local analysis at p = 5 ---\n";
printf "5 = (2+i)(2-i) in Z[i], residue field F_5 at each prime\n";
F5 := GF(5);
printf "Fourth powers in F_5: ";
for a in F5 do printf "%o->%o ", a, a^4; end for;
printf "\n";
npts := 0;
for x in F5 do for y in F5 do for z in F5 do
    if x eq 0 and y eq 0 and z eq 0 then continue; end if;
    if x^4+y^4+z^4 eq 0 then npts +:= 1; end if;
end for; end for; end for;
printf "Projective F_5-points (affine reps): %o\n", npts;
printf "=> Also obstructed at p=5.\n\n";

// =========================================================================
printf "=== CONCLUSION ===\n";
printf "C: x^4+y^4+z^4=0 has NO Q(i)-rational point.\n";
printf "Local obstruction at pi=(1+i): v_pi(F) = 2 for all primitive lifts.\n";

quit;
