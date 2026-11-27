import NRR.CylinderPartitionLimits
import NRR.CenteredBackground

/-! Genuine additive moment identities for convex partitions, including
the globally continuous weighted horizontal moment used for localization. -/

noncomputable section
open Set Filter Topology MeasureTheory Metric

namespace NRR.ConvexLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem aedisjoint_of_disjoint_interiors (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (μ : Measure E) (hμ : μ ≪ ν) {A B : Set E}
    (ca : Convex ℝ A) (cb : Convex ℝ B)
    (disj : Disjoint (interior A) (interior B)) : AEDisjoint μ A B := by
  apply measure_mono_null _ (measure_union_null
    (hμ (ca.addHaar_frontier ν)) (hμ (cb.addHaar_frontier ν)))
  intro x hx
  by_cases hi : x ∈ interior A
  · exact Or.inr ⟨subset_closure hx.2,fun hj => Set.disjoint_left.mp disj hi hj⟩
  · exact Or.inl ⟨subset_closure hx.1,hi⟩

/-- Boundaries may be shared: Haar-null convex frontiers are enough for
the exact vector-valued sum, without replacing closed cells by open cells. -/
theorem integral_partition (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (μ : Measure E) (hμ : μ ≪ ν) {ι : Type*} [Fintype ι]
    (C : ι → Set E) (closed : ∀ i, IsClosed (C i)) (convex : ∀ i, Convex ℝ (C i))
    (disjoint : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {K : Set E} (cover : (⋃ i, C i) = K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : IntegrableOn f K μ) :
    (∫ x in K, f x ∂μ) = ∑ i, ∫ x in C i, f x ∂μ := by
  rw [← cover] at hf ⊢
  rw [integral_iUnion_ae (fun i => (closed i).measurableSet.nullMeasurableSet)
    (fun i j hij => aedisjoint_of_disjoint_interiors ν μ hμ (convex i) (convex j)
      (disjoint hij)) hf, tsum_fintype]

theorem integral_id_zero_of_neg_invariant (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    {S : Set E} (meas : MeasurableSet S) (symmetric : Neg.neg ⁻¹' S = S) :
    (∫ x in S, x ∂ν) = 0 := by
  have mp := (Measure.measurePreserving_neg ν).restrict_preimage meas
  rw [symmetric] at mp
  have H := mp.integral_comp (MeasurableEquiv.neg E).measurableEmbedding id
  change (∫ x in S, -x ∂ν) = (∫ x in S, x ∂ν) at H
  rw [integral_neg] at H
  have he : (∫ x in S, x ∂ν) + (∫ x in S, x ∂ν) = 0 := by
    calc
      _ = -(∫ x in S, x ∂ν) + (∫ x in S, x ∂ν) :=
        congrArg (fun v : E => v + (∫ x in S, x ∂ν)) H.symm
      _ = 0 := neg_add_cancel _
  have hz : (2 : ℝ) • (∫ x in S, x ∂ν) = 0 := by simpa only [two_smul] using he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end NRR.ConvexLimits

namespace NRR.Localization

variable {d : ℕ}

theorem integral_fst_cylinder_zero (a h : ℝ) :
    (∫ q in solidCylinder (d := d) a h, q.1 ∂volume) = 0 := by
  have hi : IntegrableOn id (solidCylinder (d := d) a h) volume :=
    continuous_id.continuousOn.integrableOn_compact (isCompact_solidCylinder a h)
  have symm : Neg.neg ⁻¹' solidCylinder (d := d) a h = solidCylinder a h := by
    ext q
    simp only [mem_preimage, solidCylinder, mem_prod, mem_closedBall, dist_zero_right,
      Prod.fst_neg, norm_neg, Prod.snd_neg, mem_Icc]
    constructor <;> rintro ⟨hu,hl,hr⟩ <;> exact ⟨hu,by linarith,by linarith⟩
  have hz := ConvexLimits.integral_id_zero_of_neg_invariant
    ((volume : Measure (Space d)).prod (volume : Measure ℝ))
    (isCompact_solidCylinder (d := d) a h).isClosed.measurableSet symm
  change (∫ q in solidCylinder (d := d) a h, q ∂volume) = 0 at hz
  have hmap := (ContinuousLinearMap.fst ℝ (Space d) ℝ).integral_comp_comm hi
  change (∫ q in solidCylinder a h, q.1 ∂volume) =
    (∫ q in solidCylinder a h, q ∂volume).1 at hmap
  rw [hz] at hmap
  exact hmap

/-- Defined on all compact convex sets, including lower-dimensional ones. -/
def weightedHorizontalMoment (ρ : Measure (Space d × ℝ)) (hρ : ρ ≪ volume)
    (first : Integrable (fun q : Space d × ℝ => q.1) ρ) (a h δ : ℝ) :
    C(ConvexLimits.ConvexCompact (Space d × ℝ),Space d) :=
  ⟨fun C => (∫ q in ConvexLimits.points C ∩ solidCylinder a h, q.1 ∂volume) +
      δ • (∫ q in ConvexLimits.points C, q.1 ∂ρ),
    (continuous_clipped_moment a h).add ((continuous_const.smul
      (ConvexLimits.continuous_integral
        ((volume : Measure (Space d)).prod (volume : Measure ℝ)) ρ hρ first)))⟩

theorem weightedHorizontalMoment_balanced {n : ℕ}
    (ρ : Measure (Space d × ℝ)) (hρ : ρ ≪ volume)
    (first : Integrable (fun q : Space d × ℝ => q.1) ρ)
    (a h δ : ℝ) (C : Fin n → ConvexLimits.ConvexCompact (Space d × ℝ))
    (disjoint : Pairwise fun i j => Disjoint
      (interior (ConvexLimits.points (C i))) (interior (ConvexLimits.points (C j))))
    {K : Set (Space d × ℝ)} (cover : (⋃ i, ConvexLimits.points (C i)) = K)
    (inner : solidCylinder a h ⊆ K) (centered : ∫ q in K, q.1 ∂ρ = 0) :
    ∑ i, weightedHorizontalMoment ρ hρ first a h δ (C i) = 0 := by
  let haar := (volume : Measure (Space d)).prod (volume : Measure ℝ)
  have whole := ConvexLimits.integral_partition haar ρ hρ
    (fun i => ConvexLimits.points (C i)) (fun i => (C i).val.isCompact.isClosed)
    (fun i => (C i).property) disjoint cover (fun q => q.1) first.integrableOn
  let A i := ConvexLimits.points (C i) ∩ solidCylinder a h
  have coverA : (⋃ i, A i) = solidCylinder a h := by
    ext q
    constructor
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      exact hi.2
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp (cover.symm ▸ inner hq)
      exact mem_iUnion.mpr ⟨i,hi,hq⟩
  have clip := ConvexLimits.integral_partition haar volume Measure.AbsolutelyContinuous.rfl A
    (fun i => (C i).val.isCompact.isClosed.inter (isCompact_solidCylinder a h).isClosed)
    (fun i => (C i).property.inter ((convex_closedBall _ _).prod (convex_Icc _ _)))
    (fun i j hij => (disjoint hij).mono (interior_mono inter_subset_left)
      (interior_mono inter_subset_left)) coverA (fun q => q.1)
    (continuous_fst.continuousOn.integrableOn_compact (isCompact_solidCylinder a h))
  change (∑ i, ((∫ q in A i, q.1 ∂volume) +
    δ • (∫ q in ConvexLimits.points (C i), q.1 ∂ρ))) = 0
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← whole, ← clip,
    centered, integral_fst_cylinder_zero, smul_zero, add_zero]

end NRR.Localization
