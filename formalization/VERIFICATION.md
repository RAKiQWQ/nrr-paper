# Verification of the Lean formalization

On 2026-11-28 the pinned Lean 4.24.0 / mathlib v4.24.0 project built successfully. The default import closure contained 303 Lean source files, including `NRR.lean`. The audit examined all 9,518 project declarations, including private helpers, and found three transitive axioms: `propext`, `Classical.choice`, and `Quot.sound`. The final theorem has the type `NRR.fullClassification : NRR.FullClassification`.

| English manuscript | Checked declaration |
| --- | --- |
| Theorem 1.1, prescribed body and measure | `NRR.prescribedCounterexamples` |
| Corollary 1.2, robustness under approximate equal mass | `NRR.prescribedRobustCounterexamples` |
| Corollary 1.3, pointwise classification | `NRR.fullClassification` |
| Theorem 1.4, one pair of rational polynomials for all dimensions | `NRR.CubeEuclideanDimensions.exists_same_polynomials_all_dimensions` |

The type of the classification quantifies over each prescribed full-dimensional compact convex body and each absolutely continuous probability measure giving it mass one. The proof supplies both the negative direction and the prime-power existence theorem. The cube theorem chooses its polynomials before quantifying over the dimension. [Definitions](NRR/Statement.lean) · [Classification proof](NRR/PrimePowerTopologyConclusion.lean) · [Cube theorem](NRR/CubeEuclideanDimensions.lean)

## Reproduce the checks

With elan, Git and Python 3 on the path, run these commands from the Lean project directory:

```sh
lake exe cache get
lake build
lake env lean ProofAudit.lean
python ../scripts/verify.py
```

The PowerShell verifier also checks that every file under `NRR/` is reachable from the default import. With the dependencies cached, run `./scripts/verify.ps1 -LeanThreads 1`. The package manifest pins mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. [Verifier](scripts/verify.ps1) · [Audit](ProofAudit.lean) · [Dependency lockfile](lake-manifest.json)

Selected output from the checks:

```text
Default import closure covers 303 project source files.
Build completed successfully (3760 jobs).
Audited 9518 project declarations. Axioms: [Quot.sound, propext, Classical.choice]
'NRR.primePowerExistence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NRR.fullClassification' depends on axioms: [propext, Classical.choice, Quot.sound]
Four cube moments and slope recovery: 324 exact interpolation nodes.
```

The exact arithmetic script also checks internal binomial gcds for `2 ≤ n ≤ 200`, winding counts for `n = 6, 10, 12, 15`, the three-dimensional spherical cap bound, and the positive weight correction on an asymmetric pyramid. [Arithmetic checks](../scripts/verify.py)
