import NRR.CylinderLocalization
import NRR.ConvexCentroids
import NRR.CylinderRigidity

/-! Limiting zero-moment partitions really induce horizontal cylinder slabs.
The base probability below is constructed from ordinary volume. -/

noncomputable section
open Set Topology Filter Metric MeasureTheory
open scoped ENNReal

namespace NRR.Localization

variable {d : ℕ}

def uniformBase (a : ℝ) : Measure (Space d) :=
  (volume (closedBall (0 : Space d) a))⁻¹ • volume.restrict (closedBall 0 a)

theorem base_volume_pos {a : ℝ} (ha : 0 < a) :
    0 < volume (closedBall (0 : Space d) a) :=
  MeasureTheory.Measure.measure_pos_of_nonempty_interior volume (by
    rw [interior_closedBall _ ha.ne']
    exact ⟨0, mem_ball_self ha⟩)

theorem uniformBase_probability {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (uniformBase (d := d) a) := by
  constructor
  simp only [uniformBase, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (base_volume_pos ha).ne'
    (isCompact_closedBall (0 : Space d) a).measure_lt_top.ne

theorem uniformBase_ac (a : ℝ) : uniformBase (d := d) a ≪ volume :=
  Measure.absolutelyContinuous_restrict.smul_left _

theorem uniformBase_dominates (a : ℝ) :
    volume.restrict (closedBall (0 : Space d) a) ≪ uniformBase a :=
  Measure.absolutelyContinuous_smul (by
    exact ENNReal.inv_ne_zero.mpr (isCompact_closedBall (0 : Space d) a).measure_lt_top.ne)

theorem uniformBase_full {a : ℝ} (ha : 0 < a) :
    uniformBase (d := d) a (closedBall 0 a) = 1 := by
  simp only [uniformBase, Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (base_volume_pos ha).ne'
    (isCompact_closedBall (0 : Space d) a).measure_lt_top.ne

theorem uniformBase_prod_restrict (a : ℝ) :
    (uniformBase (d := d) a).prod volume =
      (volume (closedBall (0 : Space d) a))⁻¹ •
        volume.restrict (closedBall (0 : Space d) a ×ˢ (univ : Set ℝ)) := by
  rw [uniformBase, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ]
  rfl

theorem uniformBase_prod_on {a : ℝ} {S : Set (Space d × ℝ)}
    (hS : S ⊆ closedBall 0 a ×ˢ (univ : Set ℝ)) :
    ((uniformBase (d := d) a).prod volume).restrict S =
      (volume (closedBall (0 : Space d) a))⁻¹ • volume.restrict S := by
  rw [uniformBase_prod_restrict, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset hS]

theorem vector_zero_scalar {a h δ : ℝ}
    (ρ : Measure (Space d × ℝ))
    (first : Integrable (fun q : Space d × ℝ => q.1) ρ)
    (C : ConvexLimits.ConvexCompact (Space d × ℝ))
    (zero : (∫ q in ConvexLimits.points C ∩ solidCylinder a h, q.1 ∂volume) +
      δ • (∫ q in ConvexLimits.points C, q.1 ∂ρ) = 0)
    (L : Space d →L[ℝ] ℝ) :
    (∫ q in ConvexLimits.points C ∩ solidCylinder a h, L q.1 ∂volume) +
      δ * (∫ q in ConvexLimits.points C, L q.1 ∂ρ) = 0 := by
  have hi : IntegrableOn (fun q : Space d × ℝ => q.1)
      (ConvexLimits.points C ∩ solidCylinder a h) volume :=
    continuous_fst.continuousOn.integrableOn_compact
      (C.val.isCompact.inter_right (isClosed_closedBall.prod isClosed_Icc))
  have H := congrArg L zero
  simpa only [map_add, map_smul, map_zero, smul_eq_mul,
    L.integral_comp_comm hi, L.integral_comp_comm first.integrableOn] using H

/-- No limiting piece can disappear in the inner cylinder. Once the tail
weight vanishes, cylinder rigidity applies to the actual limiting clips. -/
theorem limiting_clips_are_slabs {n : ℕ}
    (ρ : Measure (Space d × ℝ)) [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    (first : Integrable (fun q : Space d × ℝ => q.1) ρ)
    (C : Fin n → ConvexLimits.ConvexCompact (Space d × ℝ))
    (Ck : ℕ → Fin n → ConvexLimits.ConvexCompact (Space d × ℝ))
    (near : Tendsto Ck atTop (𝓝 C)) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (mass : ∀ i, 0 < ρ (ConvexLimits.points (C i)))
    (height : ∀ i, |⨍ q in ConvexLimits.points (C i), q.2 ∂ρ| < h)
    (covers : solidCylinder a h ⊆ ⋃ i, ConvexLimits.points (C i))
    (disjoint : Pairwise fun i j => Disjoint
      (interior (ConvexLimits.points (C i))) (interior (ConvexLimits.points (C j))))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) (hδ0 : Tendsto δ atTop (𝓝 0))
    (zero : ∀ k i,
      (∫ q in ConvexLimits.points (Ck k i) ∩ solidCylinder a h, q.1 ∂volume) +
        δ k • (∫ q in ConvexLimits.points (Ck k i), q.1 ∂ρ) = 0) :
    ∀ i, ∃ lo hi : ℝ, lo < hi ∧
      ConvexLimits.points (C i) ∩ solidCylinder a h = closedBall 0 a ×ˢ Icc lo hi := by
  letI := uniformBase_probability (d := d) ha
  let A i := ConvexLimits.points (C i) ∩ solidCylinder a h
  have compact (i) : IsCompact (A i) :=
    (C i).val.isCompact.inter_right (isClosed_closedBall.prod isClosed_Icc)
  have convex (i) : Convex ℝ (A i) :=
    (C i).property.inter ((convex_closedBall (0 : Space d) a).prod (convex_Icc (-h) h))
  have nonemptyInterior (i) : (interior (A i)).Nonempty :=
    interior_clip_of_zero_moments ρ hρ first (tendsto_pi_nhds.mp near i) ha hh
      (mass i) (height i) δ hδ (fun k L => vector_zero_scalar ρ first _ (zero k i) L)
  have hcover : (⋃ i, A i) = closedBall 0 a ×ˢ Icc (-h) h := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_right
    · intro q hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp (covers hq)
      exact mem_iUnion.mpr ⟨i, hi, hq⟩
  have disj : Pairwise fun i j => Disjoint (interior (A i)) (interior (A j)) := by
    intro i j hij
    exact (disjoint hij).mono (interior_mono inter_subset_left) (interior_mono inter_subset_left)
  have hrestrict (i) := uniformBase_prod_on (d := d)
    (S := A i) (show A i ⊆ closedBall 0 a ×ˢ (univ : Set ℝ) from
      fun _ hq => ⟨hq.2.1, trivial⟩)
  have positive (i) : 0 < ((uniformBase a).prod volume).real (A i) := by
    have hp : 0 < ((uniformBase a).prod volume) (A i) := by
      have hv := MeasureTheory.Measure.measure_pos_of_nonempty_interior volume (nonemptyInterior i)
      have hm := congrArg (fun m : Measure (Space d × ℝ) => m univ) (hrestrict i)
      simp only [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul] at hm
      rw [hm]
      exact ENNReal.mul_pos
        (ENNReal.inv_ne_zero.mpr (isCompact_closedBall (0 : Space d) a).measure_lt_top.ne) hv.ne'
    exact ENNReal.toReal_pos hp.ne' (compact i).measure_lt_top.ne
  have centered (i) : ∫ q in A i, q.1 ∂((uniformBase a).prod volume) = (0 : Space d) := by
    rw [hrestrict i, integral_smul_measure]
    rw [clipped_moment_zero_of_limit ρ hρ first (tendsto_pi_nhds.mp near i) a h δ hδ0
      (fun k => zero k i), smul_zero]
  exact Cylinder.partition_is_slabs (uniformBase a) (uniformBase_ac a) isClosed_closedBall
    (convex_closedBall _ _) (uniformBase_dominates a) (uniformBase_full ha)
    A compact convex hcover disj positive centered

/-- Uniform localization for an entire compact family of partitions. The
neighborhood need only contain partitions whose inner-cylinder clips are
horizontal slabs; this property is proved for every possible zero limit. -/
theorem compact_cylinder_localization {n : ℕ}
    (ρ : Measure (Space d × ℝ)) [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    (first : Integrable (fun q : Space d × ℝ => q.1) ρ)
    (s : Set (Fin n → ConvexLimits.ConvexCompact (Space d × ℝ)))
    (compact : IsCompact s) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (mass : ∀ C ∈ s, ∀ i, 0 < ρ (ConvexLimits.points (C i)))
    (height : ∀ C ∈ s, ∀ i, |⨍ q in ConvexLimits.points (C i), q.2 ∂ρ| < h)
    (covers : ∀ C ∈ s, solidCylinder a h ⊆ ⋃ i, ConvexLimits.points (C i))
    (disjoint : ∀ C ∈ s, Pairwise fun i j => Disjoint
      (interior (ConvexLimits.points (C i))) (interior (ConvexLimits.points (C j))))
    (U : Set (Fin n → ConvexLimits.ConvexCompact (Space d × ℝ))) (openU : IsOpen U)
    (slabsInU : ∀ C ∈ s, (∀ i, ∃ lo hi : ℝ, lo < hi ∧
      ConvexLimits.points (C i) ∩ solidCylinder a h = closedBall 0 a ×ˢ Icc lo hi) → C ∈ U) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ C ∈ s,
      (∀ i, (∫ q in ConvexLimits.points (C i) ∩ solidCylinder a h, q.1 ∂volume) +
        δ • (∫ q in ConvexLimits.points (C i), q.1 ∂ρ) = 0) → C ∈ U := by
  classical
  by_contra! bad
  have witnesses (k : ℕ) := bad (1 / ((k : ℝ) + 1)) (by positivity)
  choose δ hδ small C inS zero outside using witnesses
  have toZero : Tendsto δ atTop (𝓝 0) :=
    squeeze_zero (fun k => (hδ k).le) (fun k => (small k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨S, hS, σ, hσ, near⟩ := compact.tendsto_subseq inS
  have hs : S ∈ U := slabsInU S hS (limiting_clips_are_slabs ρ hρ first S (C ∘ σ) near
    ha hh (mass S hS) (height S hS) (covers S hS) (disjoint S hS)
    (δ ∘ σ) (fun k => hδ (σ k)) (toZero.comp hσ.tendsto_atTop)
    (fun k i => zero (σ k) i))
  exact ((openU.isClosed_compl).mem_of_tendsto near
    (Eventually.of_forall fun k => outside (σ k))) hs

end NRR.Localization
