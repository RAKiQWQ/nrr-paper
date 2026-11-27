# Ported topology foundations

`NRR/TopologyPort/SimplicialHomotopy.lean` and
`NRR/TopologyPort/SimplicialChainHomotopy.lean` adapt the corresponding
`Mathlib/AlgebraicTopology/SimplicialObject/Homotopy.lean` and
`ChainHomotopy.lean` from mathlib revision
`9d581dfff2e41de989072ea63abf3daf69311520` (Lean `v4.36.0-rc2`).

The upstream author is Fabian Odermatt; the copyright and Apache-2.0 notices
are preserved in the files. The license is reproduced in `mathlib-LICENSE`.
The port targets this project's pinned Lean/mathlib `v4.24.0`, with older
syntax and explicit finite combinatorial proofs replacing newer tactic/API
uses. The shared mathlib source tree is not modified.

These are foundational simplicial homotopy and chain homotopy theorems.
They do not themselves assert the configuration-space obstruction, the
prime-power existence theorem, or the full NRR classification.

The project audit uses owning-module provenance as well as namespaces so
that ported declarations in upstream namespaces are included in its
transitive axiom checks.

## Relative singular chains and small chains

The `NRR/SingularHomology*.lean` modules adapt foundational material from
`Submission/Homology/` and `Hatcher/Excision/` in
`akopjan/toptverbert-nandakumar`, revision
`d98f6f87bb60b9e5b3a57370f393ade1397189bc`. Copyright and upstream file
attribution are retained in the individual adapted modules. The Apache-2.0
license is reproduced in `toptverbert-nandakumar-LICENSE`.

The local implementation uses arbitrary ring coefficients in `ModuleCat R`
and the actual singular chain functor in mathlib 4.24.0. These modules are
foundations, rather than an imported configuration-space obstruction theorem.

`NRR/TopologyPort/SphereCaps.lean` adapts the metric-sphere cap and contraction
constructions from `Submission/Model/Sphere.lean` and
`Submission/Homotopy/ContractionData.lean` at the same revision.
Its copyright notice and the repository license are included above.

`NRR/TopologyPort/Suspension.lean` adapts `Submission/Model/Suspension.lean`
from the same revision. `NRR/TopologyPort/RelativeSingularPrism.lean` also
records its upstream source in the file header. `NRR/TopologyPort/SimplexCut.lean`
retains the mathlib copyright and Apache-2.0 notice for Joël Riou's simplex
category construction.
