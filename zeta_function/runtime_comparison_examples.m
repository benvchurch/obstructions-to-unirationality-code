Attach("compute_corrections.m");
Attach("count_plane_model.m");
import "compute_zeta_function.m": OptimisedComputeZetaFunctionNumerator;
import "compute_lift.m": lift_curve;
R<x,y> := PolynomialRing(Integers(),2);

SetGPU(true);

lambda := 2;
mu := 3;

// // This example is from Tuitman's list of examples for q=p, available on Github
print "Curve", 1;
Q_1 :=y^6 - x*(x-1)^2*(x-2)^2*(x-3)^3;
p_1 := 11;
Q_1 := ChangeRing(Q_1,  GF(p_1));

res, t_1, t_2, t_3, t_4, mem := OptimisedComputeZetaFunctionNumerator(Q_1);
print t_1, t_2, t_3, t_4, mem, "\n";
Q_1_t, lift_time := lift_curve(Q_1, p_1);
print lift_time;
res_t := ZetaFunction(Q_1_t, p_1);


Q_1 := y^3 - x^2 * (x - 1) * (x - lamba) ;

