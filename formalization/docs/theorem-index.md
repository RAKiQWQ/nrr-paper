# Manuscript-to-Lean theorem index

The labels below follow the [published manuscript](../../paper/main.pdf). All four principal statements quantify over actual convex partitions. The body and measure are fixed before the functionals are chosen. [Definitions](../NRR/Statement.lean)

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1. A counterexample on each prescribed body and measure | [`NRR.prescribedCounterexamples`](../NRR/PrescribedCounterexamples.lean) |
| Corollary 1.2. A positive gap for approximately equal masses | [`NRR.prescribedRobustCounterexamples`](../NRR/RobustCounterexamples.lean) |
| Corollary 1.3. Universal fairness exactly at prime-power sizes | [`NRR.fullClassification` and `NRR.primePowerExistence`](../NRR/PrimePowerTopologyConclusion.lean) |
| Theorem 1.4. One pair of rational polynomials for cubes in every dimension | [`NRR.CubeEuclideanDimensions.exists_same_polynomials_all_dimensions`](../NRR/CubeEuclideanDimensions.lean) |

## Geometric counterexamples

| Step | Result and source |
| --- | --- |
| Cylinder rigidity | Vanishing horizontal first moments force each piece to be a horizontal slab. The adjacent separating planes determine the partition of the whole body. [Rigidity](../NRR/CylinderRigidity.lean) · [Extension](../NRR/CylinderExtension.lean) |
| Planar correction | `LocalModel.exists_planar_correction` gives the perturbation, and `balanced_square_rigidity` detects the zero configuration. `actualTotals_eq_coset` identifies the range of total winding numbers. For six parts the proof also gives their multiplicities. [Construction](../NRR/PlanarExistence.lean) · [Rigidity](../NRR/LocalModel.lean) · [Winding numbers](../NRR/EndWindingRange.lean) |
| Prescribed body and measure | Localization, compactness of the partition space, and continuous extension give functionals on all nonempty compact convex sets. The obstruction persists for nearly equal masses. [Counterexamples](../NRR/PrescribedCounterexamples.lean) · [Robustness](../NRR/RobustCounterexamples.lean) |
| Six parts in the three-dimensional ball | A spherical cap estimate in every direction forces positive-volume intersection with the inner cylinder. The five interior sixth-quantiles lie strictly between its ends. [Cap estimate and applications](../NRR/BallCapSix.lean) |
| Polynomial tests on the ball | Finitely many ordinary volume moments suffice. The remaining coordinate functionals can be chosen additive. [Polynomial approximation](../NRR/BallPolynomialCounterexample.lean) · [Additive moments](../NRR/BallAdditiveMomentsPolynomial.lean) |
| Four moments on the cube | `exists_rational_polynomials_for_partitions` gives a strict gap for all equal-volume convex partitions of the three-dimensional cube. In higher dimensions, Brunn–Minkowski equality forces product pieces. The volume-preserving coordinate change gives the factor `n/2^d` and the prescribed last coordinate. [Three-dimensional case](../NRR/CubePartitionLocalStacks.lean) · [Product rigidity](../NRR/CubeProductRigidity.lean) · [Euclidean moment formulas](../NRR/CubeEuclideanDimensions.lean) |
| Other measures and ambient partitions | Restricting and normalizing a finite measure, and clipping an ambient convex partition to the prescribed body, give the corresponding negative statements. [Corollaries](../NRR/PrescribedPartitionCorollaries.lean) |

The polynomial results establish existence. The proofs leave the coefficients, degree bounds, and numerical global gaps unspecified.

## Prime-power existence

| Step | Result and source |
| --- | --- |
| Fuks filtration | Finite disk attachments give the cellular basis of ordinary relative homology. The exact sequence for three levels identifies the connecting map. [Cell homology](../NRR/PrimePowerTopologyGeneralCellHomology.lean) · [Three levels](../NRR/PrimePowerTopologyFuksTriple.lean) |
| Twisted homology | Singular chains have free label orbits. Equivariant fillings give surjectivity of the bottom-degree projection and vanishing below the next cell dimension. [Bottom-degree comparison](../NRR/PrimePowerTopologyTwistedBottomComparison.lean) |
| Persistence at prime powers | The orientation character cancels the shuffle incidence signs. Divisibility of the interior binomial coefficients makes the first twisted differential zero, and the lowest class survives in the full configuration space. [Persistence theorem](../NRR/PrimePowerTopologyPrimePowerPersistence.lean) |
| Suspension and the Euler target | A neighborhood deformation and collapse give the suspension isomorphism, natural for proper maps. Iterating it and accounting for the fiber relabeling action by `sign^d` identifies a nonzero class in the twisted target. [Suspension](../NRR/SingularHomologyBMSuspensionGeometry.lean) · [Iteration](../NRR/PrimePowerTopologyBMSuspensionGeometricIteration.lean) · [Euler target](../NRR/PrimePowerTopologyAssociatedBMTargetNonzero.lean) |
| Twisted fundamental cycle | Take one staircase simplex from each label orbit. Signed transfer expands this chain into the oriented sum of all staircase simplices. Chain-level injectivity proves the cycle condition in prime characteristic. [Cycle and transfer](../NRR/PrimePowerTopologyTwistedFundamentalCycle.lean) |
| Local nonvanishing | Only the identity staircase simplex contains the selected point. Its chart induces a local homology isomorphism, and a coloring cocycle takes value one there. [Local chart](../NRR/PrimePowerTopologyStaircaseLocalChart.lean) · [Simplex detection](../NRR/SingularHomologySimplexLocalDetection.lean) · [Staircase class](../NRR/PrimePowerTopologyStaircaseLocalHomology.lean) |
| Euler obstruction | The ambient collapse and transfer naturality detect the normal image. The closed inclusion of the rank-one normal group is an isomorphism in the critical degree, so the Euler image is nonzero. [Ambient collapse](../NRR/PrimePowerTopologyStaircaseAmbient.lean) · [Source class](../NRR/PrimePowerTopologyStaircaseEulerSource.lean) · [Normal inclusion](../NRR/PrimePowerTopologyEulerThomPrimePower.lean) |
| Fair partitions | `configuration_equivariant_has_zero` applies in ambient dimension at least two. `universalFairness_of_configuration_zero` uses equal-mass power diagrams and a limit removing the positive background measure to prove the positive `BodyPartition` statement. [Configuration zero theorem](../NRR/PrimePowerTopologyConclusion.lean) · [Analytic implication](../NRR/PrimePowerExistencePowerConclusion.lean) |

The direct projection of the ordered fundamental class has zero Euler image. The orbit-representative cycle above is detected by transfer, which works even when the characteristic divides the order of the label group. [Ordered projection](../NRR/PrimePowerTopologyAssociatedBMFundamental.lean)

The [audit](../ProofAudit.lean) checks the types of the three principal Lean proof terms and the transitive axioms of all project declarations. [Verification record and reproduction instructions](verification.md)
