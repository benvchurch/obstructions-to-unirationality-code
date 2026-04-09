/*******************************************************************************
 * tests.m
 *
 * Driver: runs steiner_pipeline.m's RunSteinerPipeline procedure on each
 * quartic in the list `tests` below. Each run's full Magma output is written
 * to results/<label>.log; a one-line summary is appended to results/SUMMARY.txt.
 *
 * To add a new curve: append <"label", quartic_form> to the `tests` sequence.
 ******************************************************************************/

load "steiner_pipeline.m";

QQ := Rationals();
P2Q<x,y,z> := ProjectiveSpace(QQ, 2);

// ---------------------------------------------------------------------
// The list of genus-3 quartics to run. Edit this to add/remove curves.
// ---------------------------------------------------------------------
tests := [
    <"klein_twist",
        x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
        - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z)>,
    <"fermat",
        x^4 + y^4 + z^4>,
    <"edge",
        25*(x^4 + y^4 + z^4) - 34*(x^2*y^2 + x^2*z^2 + y^2*z^2)>
];

// ---------------------------------------------------------------------
// Run each test. Per-run output goes to results/<label>.log so a crash
// in one curve does not lose data from the others.
// ---------------------------------------------------------------------
System("mkdir -p results");

SetOutputFile("results/SUMMARY.txt" : Overwrite := true);
printf "Steiner / Prym pipeline runs -- %o curves\n\n", #tests;
UnsetOutputFile();

for entry in tests do
    lbl := entry[1];
    F := entry[2];
    log_file := "results/" cat lbl cat ".log";

    printf "\n>>> Running pipeline on %o (output -> %o)\n", lbl, log_file;
    t0 := Cputime();

    SetOutputFile(log_file : Overwrite := true);
    try
        RunSteinerPipeline(lbl, F);
        ok := true;
        err_msg := "";
    catch e
        ok := false;
        err_msg := Sprintf("%o", e);
        printf "\n*** ERROR running %o ***\n%o\n", lbl, e;
    end try;
    UnsetOutputFile();

    elapsed := Cputime(t0);
    SetOutputFile("results/SUMMARY.txt");
    if ok then
        printf "[OK]   %-15o  CPU %.1os  log=%o\n", lbl, elapsed, log_file;
    else
        printf "[FAIL] %-15o  CPU %.1os  log=%o  err=%o\n",
               lbl, elapsed, log_file, err_msg;
    end if;
    UnsetOutputFile();

    printf "    %o (CPU %.1os)\n", ok select "OK" else "FAIL", elapsed;
end for;

print "\nAll runs done. See results/SUMMARY.txt and results/*.log";

quit;
