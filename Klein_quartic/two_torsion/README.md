# Klein Quartic Two-Torsion

This directory studies the `2`-torsion of Jacobians of genus-`3` plane quartics, with the Klein quartic twist as the main motivating example and the Fermat and Edge quartics as comparison cases.

The central geometric pipeline is:

`quartic -> 28 bitangents -> 63 Steiner complexes -> quartic decompositions -> genus-2 Pryms -> elliptic factors / supersingular behavior`

There are really two intertwined projects here:

1. the `Steiner/Prym` pipeline, which turns bitangent and contact-conic data into genus-`2` curves and Prym invariants;
2. the `J[2] / supersingular / Galois representation` pipeline, which studies automorphism actions, Jacobian factorization, and supersingular-prime coincidences.

## Where To Start

If you are new to this directory, read in this order:

1. [`pipeline_math.md`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/pipeline_math.md)
2. [`tests.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/tests.m)
3. [`steiner_computations.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/steiner_computations.m)
4. [`PRYM_INVARIANTS.md`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/PRYM_INVARIANTS.md)
5. [`aut_j2_modules.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/aut_j2_modules.m), [`ss_coincidences.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_coincidences.m), and [`ss_jacobian.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_jacobian.m)

## Internal Structure

### Main drivers

- [`tests.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/tests.m): batch driver for the Steiner/Prym pipeline on the Klein twist, Fermat quartic, and Edge quartic.
- [`steiner_computations.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/steiner_computations.m): core implementation of the bitangent-to-Prym pipeline.
- [`aut_j2_modules.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/aut_j2_modules.m): computes the automorphism action on bitangents and on `J[2]`.
- [`ss_coincidences.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_coincidences.m): compares supersingular-prime sets attached to Prym elliptic factors.
- [`ss_jacobian.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_jacobian.m): factors Jacobian `L`-polynomials and cross-references Jacobian supersingularity with Prym data.

### Supporting computation scripts

- [`hensel_decomp.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/hensel_decomp.m): Hensel-lift experiment for lifting decomposition data from finite fields.
- [`fermat_aut_field.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/fermat_aut_field.m): field-of-definition computations for automorphisms in the quartic examples.
- [`j128_divfield.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/j128_divfield.m): arithmetic work around the elliptic factor with `j = 128`.
- [`j128_galrep.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/j128_galrep.m), [`j128_galrep2.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/j128_galrep2.m), [`j128_galrep3.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/j128_galrep3.m), [`j128_galrep4.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/j128_galrep4.m): a sequence of experiments refining the Galois-representation analysis for the `j = 128` factor.
- [`ss_j128.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_j128.m): supersingular-prime analysis specialized to the `j = 128` curve.
- [`ss_jacobian_phase2.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_jacobian_phase2.m): later-stage or refined Jacobian supersingularity analysis.

### Subdirectories

- [`covers/`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/covers): mod-`2` cover constructions.
- [`elliptic_curve_factors_tests/`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/elliptic_curve_factors_tests): checks of elliptic factors, isogenies, and supersingular statistics.
- [`setup/`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/setup): preparatory arithmetic helpers.
- [`ss_analysis/`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/ss_analysis): focused supersingularity case studies.
- [`results/`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/results): current run outputs.
- [`results.pre_refactor/`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/results.pre_refactor): archived outputs from an earlier version of the pipeline.

## File Index

| File | Role | Math content | Status |
| --- | --- | --- | --- |
| `tests.m` | Driver | Runs the Steiner/Prym pipeline on selected quartics | source |
| `steiner_computations.m` | Core source | Bitangents, Steiner complexes, contact conics, quartic decompositions, genus-2 Pryms, Igusa and `j`-invariants | source |
| `pipeline_math.md` | Note | Exposition of theta characteristics, Steiner complexes, Pryms, and the geometry behind the pipeline | source |
| `pipeline_math.tex` | Note source | LaTeX source for the pipeline note | source |
| `pipeline_math.pdf` | Compiled note | Rendered version of the pipeline note | generated deliverable |
| `pipeline_math.aux`, `pipeline_math.log`, `pipeline_math.out` | TeX build artifacts | Auxiliary LaTeX files | generated |
| `PRYM_INVARIANTS.md` | Note | Records the invariant data tracked for Prym computations | source |
| `CLEANUP_REPORT.md` | Note | Refactoring and cleanup notes for this directory | source |
| `steiner_history.md` | Note | Historical notes on the Steiner pipeline development | source |
| `aut_j2_modules.m` | Driver/helper | Automorphism groups, bitangent permutation action, and `F_2[Aut(C)]`-module structure on `J[2]` | source |
| `hensel_decomp.m` | Experiment | Lifting decomposition data by Hensel-style methods | source |
| `fermat_aut_field.m` | Experiment | Field-of-definition questions for automorphisms in comparison quartics | source |
| `j128_divfield.m` | Experiment | Division-field and arithmetic analysis for the `j=128` elliptic factor | source |
| `j128_galrep.m` | Experiment | First pass at Galois-representation analysis for the `j=128` factor | source |
| `j128_galrep2.m` | Experiment | Refined `j=128` Galois-representation computations | source |
| `j128_galrep3.m` | Experiment | Refined `j=128` Galois-representation computations | source |
| `j128_galrep4.m` | Experiment | Refined `j=128` Galois-representation computations | source |
| `ss_coincidences.m` | Driver | Compares supersingular-prime sets for Prym elliptic factors arising from the same quartic | source |
| `ss_j128.m` | Experiment | Supersingular-prime analysis for the `j=128` factor | source |
| `ss_jacobian.m` | Driver | Jacobian `L`-polynomial factorization and comparison with Prym supersingularity | source |
| `ss_jacobian_phase2.m` | Experiment | Additional Jacobian supersingularity analysis | source |
| `setup/two_ranks.m` | Helper | Preparatory rank or `2`-rank computations | source |
| `covers/mod2_cover.m` | Helper | Builds mod-`2` covers attached to `J[2]` data | source |
| `covers/mod2_cover_part2.m` | Helper | Continuation/refinement of the mod-`2` cover construction | source |
| `covers/mod2_cover_twist.m` | Helper | Mod-`2` cover construction for the twisted Klein quartic setting | source |
| `elliptic_curve_factors_tests/check_isogeny_correct.m` | Check | Verifies candidate isogeny relations among elliptic factors | source |
| `elliptic_curve_factors_tests/check_j23_internal.m` | Check | Internal consistency checks for one of the elliptic factor computations | source |
| `elliptic_curve_factors_tests/supersingular_stats.m` | Check | Supersingular statistics for elliptic factors | source |
| `elliptic_curve_factors_tests/supersingular_stats2.m` | Check | Variant/refinement of the supersingular statistics script | source |
| `ss_analysis/ss_21orbit.m` | Case study | Supersingular analysis for the `21`-orbit in the Klein-quartic `J[2]` picture | source |
| `results/SUMMARY.txt` | Output summary | One-line status summary for current runs | generated |
| `results/*.log` | Run outputs | Per-run computation logs | generated |
| `results/run.stdout`, `results/run.stderr` | Run outputs | Captured Magma stdout/stderr | generated |
| `results/prym_table.md` | Curated output | Summary table of Prym data from runs | generated deliverable |
| `results.pre_refactor/SUMMARY.txt` | Archive output | Summary from the older pipeline version | archive |
| `results.pre_refactor/*.log` | Archive output | Logs from the pre-refactor version | archive |
| `results.pre_refactor/run.stdout`, `results.pre_refactor/run.stderr` | Archive output | Captured output from the earlier version | archive |
| `.claude/settings.local.json` | Tooling | Local editor/agent settings, not mathematical source | local config |

## Suggested Documentation Convention

When adding files here, label them mentally in one of these buckets:

- `driver`: intended to be run directly
- `helper`: callable computational routine used by a driver
- `note`: mathematical explanation or research memo
- `generated`: build artifact or run output
- `archive`: historical output kept for comparison

That distinction is more useful here than the raw filename alone.
