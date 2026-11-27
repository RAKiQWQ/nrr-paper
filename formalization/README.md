# Lean formalization of the generalized Nandakumar–Ramana Rao problem

Fix a dimension `d ≥ 3`, a number of parts `n ≥ 2`, a full-dimensional compact convex body `K`, and an absolutely continuous probability measure giving `K` mass one. When `n` is a prime power, every choice of `d − 1` Hausdorff-continuous real-valued functionals on nonempty compact convex sets admits a fair convex partition of `K` into `n` pieces. For every other `n`, some choice of these functionals prevents a fair partition of the prescribed body and measure. A fair partition gives all pieces equal measure and equal values of each functional. [Definitions and quantifiers](NRR/Statement.lean) · [Paper](../paper/main.pdf)

| Result | Lean declaration |
| --- | --- |
| Counterexamples for non-prime-power sizes | [`NRR.prescribedCounterexamples`](NRR/PrescribedCounterexamples.lean) |
| Existence for prime-power sizes | [`NRR.primePowerExistence`](NRR/PrimePowerTopologyConclusion.lean) |
| Pointwise classification | [`NRR.fullClassification : NRR.FullClassification`](NRR/PrimePowerTopologyConclusion.lean) |

## Reading the proof

The counterexample uses horizontal moments to localize candidate partitions near slabs. Two adjacent interfaces then determine a continuous correction that prevents equality. The [geometric proof](../paper/notes/geometric-proof.md) and [planar construction](../paper/notes/planar-construction.md) develop these steps.

For prime-power sizes, the lowest Fuks class survives in twisted homology. A signed transfer and a local calculation detect a twisted fundamental cycle. Its nonzero Euler image forces an equivariant zero, which gives a fair equal-mass power partition. The theorem index follows these maps and lists separate proofs of robustness, the ball estimates, and the same rational polynomial pair for cubes in every dimension. [Theorem index](docs/theorem-index.md)

## Checking the project

From this directory, with elan, Git, and Python 3 installed, run the following in PowerShell.

```powershell
lake exe cache get
../scripts/verify-formalization.ps1 -LeanThreads 1
```

The default import is [NRR.lean](NRR.lean). The verifier checks import coverage, builds with Lean and mathlib 4.24.0, audits transitive axioms, and runs the arithmetic script. The verification record includes shell commands and the expected output. [Verification record](docs/verification.md) · [Axiom audit](ProofAudit.lean) · [Third-party sources and licenses](third_party/README.md)
