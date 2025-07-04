Attach("./compute_corrections.m");
Attach("./count_plane_model.m");
import "./compute_zeta_function.m": OptimisedComputeZetaFunctionNumerator;
import "./compute_lift.m": lift_curve;
R<x,y> := PolynomialRing(Integers(),2);

SetGPU(true);

function IsSupersingular(f,p)
    n := # Vertices(NewtonPolygon(f,p : Faces := "Lower"));
    n;
    return (n eq 2);
end function;


// // This example is from Tuitman's list of examples for q=p, available on Github
print "Curve", 1;
Q_1 :=y^6 - x*(x-1)^2*(x-2)^2*(x-3)^3;
p := 11;
Q_1 := ChangeRing(Q_1,  GF(p));

res, t_1, t_2, t_3, t_4, mem := OptimisedComputeZetaFunctionNumerator(Q_1);

// Curves for C1 points: 0 1 lambda mu inf

for p in [5] do 
    for rootlambda in [2 .. p-2] do
        for rootmu in [2 .. p-2] do
            if (GF(p) ! rootlambda eq GF(p) ! rootmu) or (GF(p) ! rootlambda eq GF(p) ! -rootmu) then
                continue;
            end if;
    
            lambda := rootlambda^2;
            mu := rootmu^2;

            Q_H_4 := x*y^6 - (x-1)^2*(x-mu)^2;
            Q_H_3 := y^3 - (x - rootlambda)*(x + rootlambda)^2*(x - rootmu) * (x + rootmu)^2;
            Q_H_5 := y^3 - x*(x-1)*(x+1)^2*(x-rootlambda)*(x+rootlambda)^2*(x-rootmu)^2;

            Qs := [Q_H_3, Q_H_5, Q_H_4];
            res := [];

            for Q in Qs do
                Append(~res, OptimisedComputeZetaFunctionNumerator(ChangeRing(Q, GF(p))));
            end for;

            all_cyclotomic := true;
            for r in res do
                if not IsSupersingular(r,p) then
                    all_cyclotomic := false;
                    break;
                end if;
            end for;
            if all_cyclotomic then
                print lambda,mu, "supersingular";
            end if;
        end for;
    end for;
end for;

// Curves for C2

Q_1 := y^3 - x^2 * (x - 1) * (x - lambda); // 
