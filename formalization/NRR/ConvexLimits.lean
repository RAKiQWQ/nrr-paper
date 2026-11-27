import NRR.Moments
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! Hausdorff continuity for compact convex sets in arbitrary finite-dimensional
real normed spaces, including the product coordinates used by the cylinder. -/

noncomputable section
open Set Filter Topology TopologicalSpace Metric MeasureTheory

namespace NRR.ConvexLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev ConvexCompact (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {C : NonemptyCompacts E // Convex ℝ (C : Set E)}

abbrev points (C : ConvexCompact E) : Set E := C.val

theorem exists_support_unitBall (f : E →L[ℝ] ℝ) :
    ∃ u : E, ‖u‖ ≤ 1 ∧ f u = ‖f‖ := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    ⟨0, by simp⟩ f.continuous.continuousOn
  have hnonneg : 0 ≤ f u := by simpa using hmax (by simp : (0 : E) ∈ closedBall 0 1)
  have hnorm : ‖f‖ ≤ f u := ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg (by
    intro x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h := hmax (show -x ∈ closedBall (0 : E) 1 by simp [mem_closedBall, dist_eq_norm, hx])
      change f (-x) ≤ f u at h
      simpa only [map_neg, neg_le] using h
    · exact hmax (by simp [mem_closedBall, dist_eq_norm, hx]))
  have hun : ‖u‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hu
  exact ⟨u, hun, le_antisymm
    ((le_abs_self _).trans ((f.le_opNorm u).trans (mul_le_of_le_one_right (norm_nonneg _) hun))) hnorm⟩

theorem mem_of_inner_ball (C D : ConvexCompact E) {x : E} {r : ℝ}
    (hr : 0 < r) (ballIn : closedBall x r ⊆ points C) (near : dist C.val D.val < r) :
    x ∈ points D := by
  by_contra hx
  obtain ⟨f, b, hf, hb⟩ := geometric_hahn_banach_closed_point D.property D.val.isCompact.isClosed hx
  have hne : f ≠ 0 := by
    intro he
    obtain ⟨y, hy⟩ := D.val.nonempty
    have h := (hf y hy).trans hb
    simp [he] at h
  obtain ⟨u, hun, hu⟩ := exists_support_unitBall f
  let z := x + r • u
  have hz : z ∈ points C := ballIn (by
    simp only [z, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hun)
  obtain ⟨w, hw, hd⟩ := exists_dist_lt_of_hausdorffDist_lt hz near (edist_ne_top C.val D.val)
  have hbound : f (z-w) ≤ ‖f‖ * ‖z-w‖ := (le_abs_self _).trans (f.le_opNorm (z-w))
  have hlt : f (z-w) < ‖f‖ * r := hbound.trans_lt
    (mul_lt_mul_of_pos_left (by simpa [dist_eq_norm] using hd) (norm_pos_iff.mpr hne))
  have hzval : f z = f x + r * ‖f‖ := by simp [z, hu]
  rw [map_sub, hzval] at hlt
  linarith [hf w hw]

theorem eventually_mem_iff {C : ConvexCompact E} {Ck : ℕ → ConvexCompact E}
    (near : Tendsto Ck atTop (𝓝 C)) {x : E} (hx : x ∉ frontier (points C)) :
    ∀ᶠ k in atTop, (x ∈ points (Ck k) ↔ x ∈ points C) := by
  have hc : Tendsto (fun k => (Ck k).val) atTop (𝓝 C.val) :=
    (continuous_subtype_val.tendsto C).comp near
  by_cases h : x ∈ points C
  · have hi : x ∈ interior (points C) := by
      by_contra he
      exact hx ⟨subset_closure h, he⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
    filter_upwards [(Metric.tendsto_nhds.mp hc) (r/2) (by linarith)] with k hk
    exact iff_of_true (mem_of_inner_ball C (Ck k) (by linarith : 0 < r/2)
      ((closedBall_subset_ball (by linarith : r/2 < r)).trans hball)
      (by rwa [dist_comm C.val (Ck k).val])) h
  · have hpos : 0 < infDist x (points C) := by
      by_contra! hn
      exact h ((C.val.isCompact.isClosed.mem_iff_infDist_zero C.val.nonempty).mpr
        (le_antisymm hn infDist_nonneg))
    have ht := ((lipschitz_infDist_set x).continuous.tendsto C.val).comp hc
    filter_upwards [ht.eventually (lt_mem_nhds hpos)] with k hk
    exact iff_of_false (fun hmem => (ne_of_gt hk) (infDist_zero_of_mem hmem)) h

variable [MeasurableSpace E] [BorelSpace E]

/-- Convex indicators converge away from a Haar-null frontier, so every
integrable density has continuous compact-convex set integrals. -/
theorem continuous_integral (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (μ : Measure E) (hμ : μ ≪ ν) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} (hf : Integrable f μ) :
    Continuous (fun C : ConvexCompact E => ∫ x in points C, f x ∂μ) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro Ck C hc
  have meas (D : ConvexCompact E) : MeasurableSet (points D) :=
    D.val.isCompact.isClosed.measurableSet
  have hnull : ∀ᵐ x ∂μ, x ∉ frontier (points C) :=
    compl_mem_ae_iff.mpr (hμ (C.property.addHaar_frontier ν))
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => (points (Ck k)).indicator f x) atTop
      (𝓝 ((points C).indicator f x)) := by
    filter_upwards [hnull] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_iff hc hx] with k hk
    by_cases h : x ∈ points C
    · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hk.mpr h)]
    · simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun e => h (hk.mp e))]
  simp only [← integral_indicator (meas _)]
  exact tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun k => hf.aestronglyMeasurable.indicator (meas _)) hf.norm
    (fun k => Eventually.of_forall (fun x => by
      by_cases h : x ∈ points (Ck k) <;> simp [Set.indicator, h])) hlim

end NRR.ConvexLimits
