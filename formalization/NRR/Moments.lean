import NRR.Statement
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sequences
import Mathlib.Tactic

open MeasureTheory Set Topology TopologicalSpace Filter Metric
noncomputable section

namespace NRR.Moments

abbrev points {d : ℕ} (C : CompactConvex d) : Set (Space d) := C.val

/-- A Hausdorff approximation by a convex set cannot omit the center of
a ball in the limiting set once the error is smaller than its radius. -/
theorem mem_of_inner_ball {d : ℕ} (C D : CompactConvex d) {x : Space d} {r : ℝ}
    (hr : 0 < r) (ballIn : closedBall x r ⊆ points C) (near : dist C.val D.val < r) :
    x ∈ points D := by
  by_contra hx
  obtain ⟨f, b, hf, hb⟩ := geometric_hahn_banach_closed_point D.property D.val.isCompact.isClosed hx
  let v : Space d := (InnerProductSpace.toDual ℝ (Space d)).symm f
  have hv (u : Space d) : inner ℝ v u = f u := InnerProductSpace.toDual_symm_apply
  have hne : v ≠ 0 := by
    intro he
    obtain ⟨y, hy⟩ := D.val.nonempty
    have hy' := (hf y hy).trans hb
    rw [← hv, ← hv, he] at hy'
    simp at hy'
  let u := ‖v‖⁻¹ • v
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hne
  have hu : inner ℝ v u = ‖v‖ := by
    dsimp [u]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hne]
  let z := x + r • u
  have hz : z ∈ points C := ballIn (by
    simp [z, mem_closedBall, dist_eq_norm, norm_smul, hun, abs_of_pos hr])
  obtain ⟨w, hw, hd⟩ := exists_dist_lt_of_hausdorffDist_lt hz near (edist_ne_top C.val D.val)
  have hlt : inner ℝ v (z - w) < ‖v‖ * r :=
    (real_inner_le_norm _ _).trans_lt
      (mul_lt_mul_of_pos_left (by simpa [dist_eq_norm] using hd) (norm_pos_iff.mpr hne))
  have hur : inner ℝ v z = f x + r * ‖v‖ := by
    simp [z, inner_add_right, real_inner_smul_right, hu, hv x]
  rw [inner_sub_right, hur, hv w] at hlt
  linarith [hf w hw]

theorem eventually_mem_iff {d : ℕ} {C : CompactConvex d} {Ck : ℕ → CompactConvex d}
    (near : Tendsto Ck atTop (𝓝 C)) {x : Space d} (hx : x ∉ frontier (points C)) :
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

/-- Arbitrary integrable densities on the body give Hausdorff-continuous
moments, including at lower-dimensional convex limits. -/
theorem continuous_integral {d : ℕ} (μ : Measure (Space d)) (hμ : μ ≪ volume)
    {f : Space d → ℝ} (hf : Integrable f μ) :
    Continuous (fun C : CompactConvex d => ∫ x in points C, f x ∂μ) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro Ck C hc
  have meas (D : CompactConvex d) : MeasurableSet (points D) := D.val.isCompact.isClosed.measurableSet
  have hnull : ∀ᵐ x ∂μ, x ∉ frontier (points C) :=
    compl_mem_ae_iff.mpr (hμ (C.property.addHaar_frontier volume))
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

end NRR.Moments
