import NRR
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit the transitive axioms of every project declaration, including private
helpers. The typed checks below also verify the proof terms for the three
principal propositions in NRR.Statement.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name _ =>
    let text := name.toString
    let ownedModule := (env.getModuleIdxFor? name).any fun index =>
      let moduleName := env.header.moduleNames[index.toNat]!.toString
      moduleName == "NRR" || moduleName.startsWith "NRR."
    if ownedModule || text.startsWith "NRR." || text.startsWith "_private.NRR." ||
        text.startsWith "MathlibExt.Topology.Homotopy.BorsukUlamWanted." then
      names.push name
    else names
  let audit : Lean.CollectAxioms.M Unit := do
    for name in names do
      Lean.CollectAxioms.collect name
  let (_, result) := (audit.run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in result.axioms do
    unless allowed.contains axiomName do
      throwError "Project depends on a nonstandard axiom: {axiomName}"
  logInfo m!"Audited {names.size} project declarations. Axioms: {result.axioms}"

#check NRR.classification_iff
#check (NRR.primePowerExistence : NRR.PrimePowerExistence)
#check (NRR.fullClassification : NRR.FullClassification)
#check NRR.PrimePowerTopology.configuration_equivariant_has_zero
#print axioms NRR.primePowerExistence
#print axioms NRR.fullClassification
#check NRR.PrimePowerTopology.configurationTwistedFundamentalChain_transfer
#check NRR.PrimePowerTopology.configurationTwistedFundamentalChain_cycle
#check NRR.PrimePowerTopology.configurationGenuineTwistedFundamentalClass_normal_ne_zero
#check NRR.PrimePowerTopology.configurationOrdinaryStaircaseClass_ne_zero
#check NRR.SingularHomology.SimplexFundamental.identityClass_local_ne_zero
#check NRR.PrimePowerTopology.nontrivial_associatedBMTwistedTarget_primePower
#check NRR.PrimePowerTopology.bm_twistedMinimalClass_primePower_ne_zero
#check NRR.BallCapSix.six_partition_positive_volume
#check NRR.LocalModel.planar_correction_of_winding_realization
#check NRR.AngularMap.realize_coordinates
#check NRR.AngularMap.realize_degreeProfile
#check NRR.LocalModel.exists_planar_correction
#check NRR.Cylinder.partition_is_slabs
#check NRR.Cylinder.separated_by_adjacent_horizontal_slabs
#check NRR.universalFairness_two
#check (NRR.prescribedCounterexamples : NRR.PrescribedCounterexamples)
#check NRR.prescribedCounterexample_six
#check NRR.universalFairness_implies_primePow
#check NRR.primePowerExistence_of_configuration_zero
#check NRR.PrimePowerTopology.isQuotientMap_minimalWedgeProjection
#check NRR.TopologyPort.singularSSetHomotopy
#check NRR.TopologyPort.singularChainHomotopy
#check NRR.TopologyPort.singularChainHomotopy_pair_naturality
#check NRR.prescribedRobustCounterexamples
#check (NRR.not_bodyGeneralizedNRR : ¬ NRR.BodyGeneralizedNRR)
#check (NRR.not_generalizedNRR : ¬ NRR.GeneralizedNRR)
#check NRR.PrimePowerTopology.twistedFuksTriple_shortExact
#check NRR.PrimePowerTopology.twistedFuksDifferential_eq_tripleδ
#check NRR.PrimePowerTopology.mono_twistedFuksRelativeInclusion_iff
#check NRR.PrimePowerTopology.sphereZeroReducedHomologyIso
#check NRR.SingularHomology.simplexι_singularChainSubdivision_eq_sum
#check NRR.CubeFourMomentReadout.horizontal_neighborhood_readout
#check NRR.RationalMomentApproximation.exists_two_rational_four_moment_polynomials
#check NRR.CubeChartBounds.exists_bounded_cube_graph_chart
#check NRR.CubeInternalMargins.exists_internal_margin
#check NRR.CubePartitionSpace.local_stacks
#check NRR.CubePartitionSpace.exists_rational_polynomials
#check NRR.CubeFourMomentReadout.exists_rational_polynomials_for_stacks
#check NRR.CubeFourMomentReadout.exists_rational_polynomials_for_product_stacks
#check NRR.CubePartitionSpace.exists_rational_polynomials_for_partitions
#check NRR.BrunnMinkowskiRigidity.eq_translate_of_volume_midpoint_eq
#check NRR.CubeProductRigidity.eq_prod_of_equal_passive_moments_of_partition
#check NRR.CubeAllDimensions.exists_polynomials_for_all_actual_partitions
#check NRR.CubeEuclideanDimensions.exists_same_polynomials_all_dimensions
#check NRR.CubeEuclideanDimensions.polynomialFormula
#check NRR.CubeEuclideanDimensions.passiveFormula
#check NRR.SingularHomology.quasiIso_mvSmallIncl
#check NRR.SingularHomology.mvExcisionHrelIso
#check NRR.SingularHomology.mvDelta_naturality
#check NRR.PrimePowerTopology.sphereTopHomologyIso
#check NRR.PrimePowerTopology.isZero_Habs_sphere_off_top
#check NRR.PrimePowerTopology.diskTopHomologyIso
#check NRR.PrimePowerTopology.isZero_diskRelative_off_top
#check NRR.PrimePowerTopology.diskFirstReflectionRelativeMap_top
#check NRR.PrimePowerTopology.pointRelativePositiveIso
#check NRR.PrimePowerTopology.vectorInfinityFundamentalClass_existsUnique
#check NRR.PrimePowerTopology.minimalRelativeFundamentalClass_ne_zero
#check NRR.PrimePowerTopology.coherentMinimalRelativeClass_relabel
#check NRR.PrimePowerTopology.linearIndependent_coherentMinimalRelativeClass
#check NRR.PrimePowerTopology.mem_nextFuks_diff_vertical_iff_splitSize
#check NRR.PrimePowerTopology.card_actualColumnShuffles
#check NRR.PrimePowerTopology.transfer_actualColumnShuffles
#check NRR.PrimePowerTopology.twoColumnCellTopHomologyIso
#check NRR.PrimePowerTopology.isOpenEmbedding_twoColumnIntoLevel
#check NRR.PrimePowerTopology.minimalFundamentalClass_sum_coeff
#check NRR.PrimePowerTopology.minimalRelativeFundamentalBasis
#check NRR.PrimePowerTopology.isZero_minimalFuksRelative_off_top
#check NRR.PrimePowerTopology.coherentTwistedMinimalMap_coefficient
#check NRR.PrimePowerTopology.coherentTwistedMinimalClass_ne_zero
#check NRR.PrimePowerTopology.fuksTripleδ_transfer
#check NRR.PrimePowerTopology.twistedFuksDifferential_minimalCoefficient
#check NRR.PolynomialMomentSeparation.convex_eq_of_ordinaryMoments
#check NRR.PolynomialMomentSeparation.prescribed_finite_momentPolynomial_counterexamples
#check NRR.PolynomialMomentSeparation.unitBall_finite_momentPolynomial_counterexamples
#check NRR.ClosedPolyhedralCone.interior_carrier
#check NRR.ClosedPolyhedralCone.exists_onePointHomeomorphClosedBall_pair
#check NRR.PrimePowerTopology.orderedTwoColumnCharacteristic_mem_lower_iff
#check NRR.PrimePowerTopology.isQuotientMap_twoColumnCharacteristicPresentation
#check NRR.PrimePowerTopology.exists_twoColumnDiskHomeomorph_pair
#check NRR.PrimePowerTopology.orderedTwoColumnDiskCharacteristic_interior_unique
#check NRR.PrimePowerTopology.orderedTwoColumnDiskCharacteristic_cover
#check NRR.SingularHomology.ClosedCollapse.isIso_relativeMap
#check NRR.PrimePowerTopology.associatedBMTwistedEulerMap_eq_zero_of_nonzero
#check NRR.SingularHomology.FiniteCellAttachment.relativeTopCoordinates
#check NRR.SingularHomology.FiniteCellAttachment.isZero_relative_off_dimension
#check NRR.PrimePowerTopology.generalFuksFiniteAttachment
#check NRR.PrimePowerTopology.generalFuksRelativeTopEquiv
#check NRR.PrimePowerTopology.isZero_generalFuksRelative_off_dimension
#check NRR.PrimePowerTopology.isIso_generalFuksRelative_step
#check NRR.PrimePowerTopology.twoColumnFuksBasis_eq_disk_image
#check NRR.PrimePowerTopology.fuksDifferential_twoColumnFuksBasis
#check NRR.PrimePowerTopology.isUnit_twoColumnShuffleLocalDegree
#check NRR.PrimePowerTopology.HabsMap_twoColumnDiskAttachingSphereMinimalPinch_eq_zero
#check NRR.PrimePowerTopology.twoColumnMinimalRelativeCoefficient_fuksDifferential_modTwo
#check NRR.PrimePowerTopology.sum_twoColumnMinimalRelativeCoefficient_fuksDifferential_modTwo
#check NRR.PrimePowerTopology.fuksDifferential_projection
#check NRR.PrimePowerTopology.twoColumnFuksBasis_relabel
#check NRR.PrimePowerTopology.twistedFuksDifferential_modTwo_projected_basis
#check NRR.PrimePowerTopology.projection_comp_twistedFuksDifferential_two_pow
#check NRR.PrimePowerTopology.minimalTwistedProjection_eq_zero_iff
#check NRR.PrimePowerTopology.associatedBMTwistedEulerClass_localizes
#check NRR.PrimePowerTopology.canonicalBMTwistedNormalDiskRelative_eq_standardFiber
#check NRR.PrimePowerTopology.associatedBMProjection_comp_twistedEulerMap_eq_zero
#check NRR.PrimePowerTopology.associatedBMTwistedEulerClass_eq_zero
#check NRR.PrimePowerTopology.associatedBMEulerOnCokernel_ne_zero_iff
#check NRR.PrimePowerTopology.fuksRelativeOrbitBasis_relabel
#check NRR.PrimePowerTopology.exists_equivariantBoundarySection_of_basis
#check NRR.PrimePowerTopology.existsUnique_twistedHomology_desc_of_free_orbits
#check NRR.PrimePowerTopology.epi_twistedFuksRelativeProj_through_cell_degree
#check NRR.PrimePowerTopology.isZero_twistedFuksRelative_below_cell_degree
#check NRR.PrimePowerTopology.twistedFuksDifferential_two_pow
#check NRR.PrimePowerTopology.twistedMinimalClass_two_pow_survives
#check NRR.PrimePowerTopology.bm_twistedMinimalClass_two_pow_ne_zero
#check NRR.EndWindingRange.actualTotals_eq_coset
#check NRR.EndWindingRange.six_actual_multiplicities
#check NRR.Binomial.halfGcd_prime_pow
#check NRR.prescribedCounterexamples_finiteMeasure_and_ambient
#check NRR.BallAdditiveMoments.unitBall_mixedPolynomial_counterexamples
