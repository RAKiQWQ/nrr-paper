import NRR.BallPolynomialCounterexample
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The additive coordinates retained by the planar construction, and
rational polynomial approximation of their actual volume densities. -/

noncomputable section
open Set Topology MeasureTheory Metric TopologicalSpace Filter
open NRR.Coordinates NRR.MomentCoordinates NRR.InterfaceChart NRR.GlobalAssembly

namespace NRR.BallAdditiveMoments

local instance productVolumeHaar {d : ℕ} :
    Measure.IsAddHaarMeasure (volume : Measure (Space d × ℝ)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure (Space d)).prod (volume : Measure ℝ))
  infer_instance

/-- The complete geometric construction, exposing its unchanged additive tail. -/
theorem counterexample_with_tail {q r : ℕ} (hn : ¬ IsPrimePow (r+2))
    (K : ConvexBody (Space (q+2) × ℝ)) (μ : Measure (Space (q+2) × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (A : Localization.MomentCylinder K μ (r+2))
    (data : Localization.UniformLayerData K μ A) :
    ∃ (δ : ℝ) (G : C(ConvexLimits.ConvexCompact (Space (q+2) × ℝ),ℂ × Space q)),
      (∀ C, (G C).2 = remainingMoment (A.moment δ) C) ∧
      ∀ S ∈ equalMassPartitions (n := r+2) K μ, ∃ i j,
        G (bodyToConvexCompact (S i)) ≠ G (bodyToConvexCompact (S j)) := by
  obtain ⟨δ₀,hδ₀,loc⟩ := A.localizes hμ hK data.U data.openU data.slabsInU
  let δ := δ₀/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD : (0 : Space (q+2)) ∈ interior (closedBall (0 : Space (q+2)) A.a) :=
    ball_subset_interior_closedBall (mem_ball_self A.radius_pos)
  have inner : closedBall (0 : Space (q+2)) A.a ×ˢ Icc (-A.h) A.h ⊆ bodyPoints K :=
    A.inner.trans interior_subset
  let chart := layerChart K.val.isCompact K.property.1 data.ε data.a data.b data.t
    data.ordered data.axis data.between hD inner data.bounds (A.capProfile δ)
  have models : ∀ S ∈ equalMassPartitions (n := r+2) K μ, convexConfigurations S ∈ data.U →
      chart.Models Localization.productPartitionCell (complexMoment (A.moment δ)) S := by
    intro S hS hSU
    obtain ⟨σ,members,p,hp,special,lower,upper⟩ := data.configurations S hS hSU
    have part := HorizontalExtension.convexPartition_reindex (convexPartition_of_partition hS.1) σ
    have readings := A.capProfile_readings hδ.le
      (fun i => bodyToConvexCompact (S (σ i))) part p.val.1 p.val.2 lower upper
    exact layerChart_models K.val.isCompact K.property.1 data.ε data.a data.b data.t
      data.ordered data.axis data.between hD inner data.bounds (A.capProfile δ)
      Localization.productPartitionCell (complexMoment (A.moment δ)) S σ members p hp special
      readings.1 readings.2
      (balanced_complex (A.moment δ) (fun i => bodyToConvexCompact (S i)) (A.balanced δ S hS.1))
  obtain ⟨G,tail,reject⟩ := Localization.counterexample_of_moment_chart_with_tail hn K μ hμ hK
    A δ data.U data.openU (loc δ hδ (by dsimp [δ]; linarith)) chart models
  exact ⟨δ,G,tail,reject⟩

/-- Pulling an absolutely continuous integral through affine coordinates
produces an actual integrable density for ordinary Euclidean volume. -/
theorem exists_volume_density_pullback {d m : ℕ}
    (e : Space d ≃ᴬ[ℝ] Space m × ℝ) (ρ : Measure (Space m × ℝ))
    [IsFiniteMeasure ρ] (hac : ρ ≪ volume) (f : Space m × ℝ → ℝ) (hf : Integrable f ρ) :
    ∃ g : Space d → ℝ, Integrable g volume ∧
      ∀ s : Set (Space d), MeasurableSet s →
        (∫ x in s, g x ∂volume) = ∫ y in e '' s, f y ∂ρ := by
  let ν := ρ.map e.symm
  have hν : ν ≪ volume := Coordinates.Affine.map_absolutelyContinuous_haar
    e.symm ρ volume volume hac
  have hi : Integrable (fun x => f (e x)) ν := by
    apply e.symm.toHomeomorph.measurableEmbedding.integrable_map_iff.mpr
    change Integrable (fun y => f (e (e.symm y))) ρ
    simpa only [e.apply_symm_apply] using hf
  refine ⟨fun x => (ν.rnDeriv volume x).toReal • f (e x),
    (integrable_rnDeriv_smul_iff hν).mpr hi, ?_⟩
  intro s hs
  rw [setIntegral_rnDeriv_smul hν hs]
  change (∫ x in s, f (e x) ∂(ρ.map e.symm)) = _
  have hmap := e.symm.toHomeomorph.measurableEmbedding.setIntegral_map
    (μ := ρ) (fun x => f (e x)) s
  change (∫ x in s, f (e x) ∂(ρ.map e.symm)) =
    ∫ y in e.symm ⁻¹' s, f (e (e.symm y)) ∂ρ at hmap
  rw [hmap]
  have he : e.symm ⁻¹' s = e '' s := by
    ext y
    exact ⟨fun hy => ⟨e.symm y,hy,e.apply_symm_apply y⟩,
      by rintro ⟨x,hx,rfl⟩; simpa using hx⟩
  simp only [he, e.apply_symm_apply]

/-- Rational polynomials approximate any integrable density in all cell
integrals simultaneously. The estimate holds for every measurable subset
of the fixed compact body. -/
theorem exists_polynomial_near_integrals {d : ℕ} (K : Body d)
    (f : Space d → ℝ) (hf : Integrable f volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin d) ℚ, ∀ s : Set (Space d), MeasurableSet s → s ⊆ K.points →
      |PolynomialMomentSeparation.polynomialMoment p s - ∫ x in s, f x ∂volume| < ε := by
  obtain ⟨g,_,hg,hgc,hgi⟩ := hf.exists_hasCompactSupport_integral_sub_le
    (show 0 < ε/4 by positivity)
  let coordinates : Fin d → C(K.points,ℝ) := fun i =>
    ⟨fun x => x.val i,(EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩
  letI : CompactSpace K.points := isCompact_iff_compactSpace.mp K.val.isCompact
  have separate : ∀ x y : K.points, x ≠ y → ∃ i, coordinates i x ≠ coordinates i y := by
    intro x y hxy
    by_contra! he
    exact hxy (Subtype.ext (PiLp.ext he))
  let η := ε / (4 * (volume.real K.points + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨p,hp⟩ := RationalMomentApproximation.exists_rational_polynomial_near_coordinates
    coordinates separate ⟨fun x => g x.val,hgc.comp continuous_subtype_val⟩ hη
  refine ⟨p,fun s hs hsub => ?_⟩
  have hsi : IntegrableOn g s volume := hgi.integrableOn
  have polyK : IntegrableOn (PolynomialMomentSeparation.polynomialEvaluation p) K.points volume :=
    (PolynomialMomentSeparation.polynomialEvaluation p).continuous.continuousOn.integrableOn_compact
      K.val.isCompact
  have polyS := polyK.mono_set hsub
  have near : |PolynomialMomentSeparation.polynomialMoment p s - ∫ x in s, g x ∂volume| ≤
      η * volume.real s := by
    rw [PolynomialMomentSeparation.polynomialMoment, ← integral_sub polyS hsi, ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const
      ((measure_mono hsub).trans_lt (K.val.isCompact.measure_lt_top (μ := volume)))
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact (hp ⟨x,hsub hx⟩).le)
  have l1 : |(∫ x in s, g x ∂volume) - ∫ x in s, f x ∂volume| ≤ ε/4 := by
    rw [← integral_sub hsi hf.integrableOn, ← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply (setIntegral_le_integral (hgi.sub hf).norm (Eventually.of_forall (fun _ => norm_nonneg _))).trans
    simpa only [Real.norm_eq_abs, Pi.sub_apply, abs_sub_comm] using hg
  have mass : volume.real s ≤ volume.real K.points :=
    ENNReal.toReal_mono K.val.isCompact.measure_lt_top.ne (measure_mono hsub)
  have hηmass : η * volume.real K.points < ε/4 := by
    have hden : 0 < 4 * (volume.real K.points+1) := by positivity
    dsimp [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [measureReal_nonneg (μ := volume) (s := K.points)]
  have triangle := abs_add_le
    (PolynomialMomentSeparation.polynomialMoment p s - ∫ x in s, g x ∂volume)
    ((∫ x in s, g x ∂volume) - ∫ x in s, f x ∂volume)
  have upper := mul_le_mul_of_nonneg_left mass hη.le
  rw [sub_add_sub_cancel] at triangle
  linarith

/-- Each retained coordinate has one fixed ordinary-volume density, also
after transporting the full construction to the prescribed coordinates. -/
theorem moment_tail_density {d q n : ℕ}
    (e : Space d ≃ᴬ[ℝ] Space (q+2) × ℝ)
    {K : ConvexBody (Space (q+2) × ℝ)} {μ : Measure (Space (q+2) × ℝ)}
    (A : Localization.MomentCylinder K μ n) (δ : ℝ) (k : Fin q) :
    ∃ g : Space d → ℝ, Integrable g volume ∧
      ∀ C : CompactConvex d,
        remainingMoment (A.moment δ) (Coordinates.Affine.convexCompactsHomeomorph e C) k =
          ∫ x in (C.val : Set (Space d)), g x ∂volume := by
  letI := A.finite
  let L : Space (q+2) →L[ℝ] ℝ := (EuclideanSpace.proj k).comp (remainingProjection q)
  let f : Space (q+2) × ℝ → ℝ := fun y => L y.1
  have hf : Integrable f A.ρ :=
    (L.comp (ContinuousLinearMap.fst ℝ (Space (q+2)) ℝ)).integrable_comp A.first
  let B := Localization.solidCylinder (d := q+2) A.a A.h
  have hB : IsCompact B := Localization.isCompact_solidCylinder A.a A.h
  letI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  have hfB : Integrable f (volume.restrict B) :=
    (L.continuous.comp continuous_fst).continuousOn.integrableOn_compact hB
  obtain ⟨g₀,hg₀,eq₀⟩ := exists_volume_density_pullback e (volume.restrict B)
    Measure.absolutelyContinuous_restrict f hfB
  obtain ⟨g₁,hg₁,eq₁⟩ := exists_volume_density_pullback e A.ρ A.ac f hf
  refine ⟨fun x => g₀ x + δ * g₁ x,hg₀.add (hg₁.const_mul δ),fun C => ?_⟩
  let D := Coordinates.Affine.convexCompactsHomeomorph e C
  have hD : MeasurableSet (ConvexLimits.points D) := D.val.isCompact.isClosed.measurableSet
  have hi₀ : IntegrableOn (fun y : Space (q+2) × ℝ => y.1)
      (ConvexLimits.points D ∩ B) volume :=
    continuous_fst.continuousOn.integrableOn_compact (D.val.isCompact.inter hB)
  have hi₁ : IntegrableOn (fun y : Space (q+2) × ℝ => y.1) (ConvexLimits.points D) A.ρ :=
    ((ContinuousLinearMap.fst ℝ (Space (q+2)) ℝ).integrable_comp A.first).integrableOn
  change L ((∫ y in ConvexLimits.points D ∩ B, y.1 ∂volume) +
    δ • (∫ y in ConvexLimits.points D, y.1 ∂A.ρ)) = _
  rw [map_add,map_smul,← L.integral_comp_comm hi₀,← L.integral_comp_comm hi₁]
  rw [integral_add hg₀.integrableOn (hg₁.const_mul δ).integrableOn,integral_const_mul]
  rw [eq₀ _ C.val.isCompact.isClosed.measurableSet,eq₁ _ C.val.isCompact.isClosed.measurableSet]
  change (∫ y in ConvexLimits.points D ∩ B, f y ∂volume) +
    δ * (∫ y in ConvexLimits.points D, f y ∂A.ρ) =
    (∫ y in ConvexLimits.points D, f y ∂(volume.restrict B)) +
    δ * (∫ y in ConvexLimits.points D, f y ∂A.ρ)
  rw [Measure.restrict_restrict hD,inter_comm]

/-- Before approximation, exactly two arbitrary continuous characteristics
and `q = d-3` integrals exclude every actual prescribed equal-mass partition. -/
theorem prescribed_integrable_counterexample (q r : ℕ) (hn : ¬ IsPrimePow (r+2))
    (K : Body (q+3)) (μ : Measure (Space (q+3)))
    (hpr : IsProbabilityMeasure μ) (hac : μ ≪ volume) (hs : μ K.points = 1) :
    ∃ (φ : Fin (q+2) → C(CompactConvex (q+3),ℝ)) (f : Fin q → Space (q+3) → ℝ),
      (∀ k, Integrable (f k) volume) ∧
      (∀ k C, φ k.succ.succ C = ∫ x in (C.val : Set (Space (q+3))), f k x ∂volume) ∧
      ∀ S : Fin (r+2) → Body (q+3), BodyPartition K S → EqualMass μ S →
        ∃ a i j, φ a (S i).toCompactConvex ≠ φ a (S j).toCompactConvex := by
  letI : IsProbabilityMeasure μ := hpr
  have hr : 0 < r := by
    by_contra h
    have he : r = 0 := by omega
    subst r
    exact hn Nat.prime_two.isPrimePow
  obtain ⟨e,strip₀,axis₀⟩ := BodyNormalization.exists_normalized_coordinates K
  let K' := Coordinates.Affine.bodiesHomeomorph e K
  let μ' := μ.map e
  letI : IsProbabilityMeasure μ' := Coordinates.Affine.map_isProbabilityMeasure e μ
  have hac' : μ' ≪ volume :=
    Coordinates.Affine.map_absolutelyContinuous_haar e μ volume volume hac
  have hs' : μ' (bodyPoints K') = 1 := by
    change (μ.map e) (bodyPoints (Coordinates.Affine.bodiesHomeomorph e K)) = 1
    rwa [Coordinates.Affine.map_body_mass]
  have mass : 0 < μ' (bodyPoints K') := by rw [hs']; exact zero_lt_one
  have strip : bodyPoints K' ⊆ univ ×ˢ Icc (-1 : ℝ) 1 :=
    fun x hx => ⟨mem_univ _,abs_le.mp (strip₀ x hx)⟩
  have axis : ∀ z : ℝ, |z| < 1 → ((0 : Space (q+2)),z) ∈ interior (bodyPoints K') :=
    fun z hz => axis₀ z (abs_lt.mp hz).1 (abs_lt.mp hz).2
  obtain ⟨A,⟨data⟩⟩ := Localization.exists_momentCylinder_uniformLayerData hr K' μ' hac' mass strip axis
  obtain ⟨δ,G,tail,reject⟩ := counterexample_with_tail hn K' μ' hac' mass A data
  choose f hfi hfe using fun k : Fin q => moment_tail_density e A δ k
  refine ⟨fun a => Coordinates.Affine.pullCharacteristic e (realCoordinates G a), f,hfi,?_,?_⟩
  · intro k C
    change (G (Coordinates.Affine.convexCompactsHomeomorph e C)).2 k = _
    rw [tail]
    exact hfe k C
  · intro S hp hm
    have hp' := Coordinates.Affine.partition_map ((bodyPartition_iff_partition K S).mp hp) e
    have hm' := (Coordinates.Affine.equalMass_map_iff e μ S).mpr hm
    obtain ⟨i,j,hij⟩ := reject (fun i => Coordinates.Affine.bodiesHomeomorph e (S i)) ⟨hp',hm'⟩
    obtain ⟨a,ha⟩ := realCoordinates_separates G hij
    exact ⟨a,i,j,ha⟩

end NRR.BallAdditiveMoments
