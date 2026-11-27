import NRR.RootSums
import NRR.SurfaceSheets

open Set Topology
noncomputable section

namespace NRR.LocalModel

open RootSums
variable {m : ℕ} [NeZero m]

def squareTest (h : ℂ ≃ₜ ℂ) : C(ℂ, ℂ) := ⟨fun z => (h.symm z)^2, by fun_prop⟩

def residual (h : ℂ ≃ₜ ℂ) : C(Surface.locus (shift (m := m)), ℂ) :=
  ⟨fun x => squareTest h (-(∑ i, h (x.val i))) - rootValue x, by
    have hc (i : Fin m) : Continuous (fun x : Surface.locus (shift (m := m)) => h (x.val i)) :=
      h.continuous.comp ((continuous_apply i).comp continuous_subtype_val)
    exact ((squareTest h).continuous.comp (continuous_finset_sum _ (fun i _ => hc i)).neg).sub
      (Surface.projection realShift).continuous⟩

/-- An exterior extension on the actual square-root surface gives a correction
of the distinguished block for *every* zero-sum configuration. The other blocks
use just constant shifts. Both arguments to D come from the neighboring cuts. -/
theorem planar_correction_of_extension (h : ℂ ≃ₜ ℂ) (hdiff : ∀ z, h z - h (-z) = 2*z)
    (g : C(Surface.locus (shift (m := m)), ℂ)) (hg : ∀ z, g z ≠ 0) (R : ℝ)
    (hext : ∀ x, R ≤ ‖rootValue x‖ → g x = residual h x) :
    ∃ (M : ℝ) (D : C(ℂ × ℂ, ℂ)), 0 < M ∧ (∀ y, ‖D y‖ ≤ M) ∧
      ∀ (w : Fin m → ℂ) (w₂ q : ℂ), (∑ i, w i) + w₂ = 0 →
        (∀ i, squareTest h (w i) - shift i = q) →
        squareTest h w₂ + D (w 0, (∑ i, w i) - w 0) ≠ q := by
  classical
  let bad := finite_multiple_readings (m := m) h hdiff
  let a := bad.toFinset
  obtain ⟨B, hB⟩ := (a.finite_toSet.image (fun z => ‖rootValue z‖)).bddAbove
  let T := max B R + 1
  let core := Surface.diskCore (realShift (m := m)) T
  have inner (x : Surface.locus (shift (m := m))) (hx : ‖rootValue x‖ < T) : x ∈ interior core := by
    have hsub : {y | ‖Surface.projection realShift y‖ < T} ⊆ core := by
      intro y hy
      change Surface.projection realShift y ∈ Metric.closedBall (0 : ℂ) T
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hy
    exact interior_maximal hsub
      (isOpen_lt (Surface.projection realShift).continuous.norm continuous_const) hx
  have hinside (x) (hx : x ∈ a) : x ∈ interior core := by
    apply inner
    have := hB (Set.mem_image_of_mem (fun z => ‖rootValue z‖) hx)
    exact this.trans_lt (lt_of_le_of_lt (le_max_left B R) (lt_add_one _))
  let old : C(ℂ × ℂ, ℂ) := ⟨fun p => squareTest h (-p.1-p.2),
    (squareTest h).continuous.comp (continuous_fst.neg.sub continuous_snd)⟩
  have hold (x : Surface.locus (shift (m := m))) :
      old (Surface.reading h (restSum h) x) - rootValue x = residual h x := by
    change squareTest h (-h (x.val 0) - ((∑ i, h (x.val i))-h (x.val 0))) - _ = _
    rw [show -h (x.val 0) - ((∑ i, h (x.val i))-h (x.val 0)) = -(∑ i, h (x.val i)) by abel]
    rfl
  obtain ⟨M, D, hM, hD, haven⟩ := Surface.correction_of_extension shift h (restSum h)
    old core (Surface.isCompact_diskCore realShift T) a hinside
    (fun x y hxy he => bad.mem_toFinset.mpr ⟨y, hxy, he⟩) g hg (fun x hx => by
      have hT := le_of_not_gt (mt (inner x) hx)
      exact (hext x ((le_max_right B R).trans ((le_add_of_nonneg_right zero_le_one).trans hT))).trans
        (hold x).symm)
  refine ⟨M, D, hM, hD, fun w w₂ q hz hf => ?_⟩
  let x : Surface.locus (shift (m := m)) := ⟨fun i => h.symm (w i), fun i => (hf i).trans (hf 0).symm⟩
  have hr : Surface.reading h (restSum h) x = (w 0, (∑ i, w i) - w 0) := by
    ext1 <;> simp [Surface.reading, restSum, x]
  have hx : x.val 0 ^ 2 - shift (0 : Fin m) = q := hf 0
  have hw : -(w 0) - ((∑ i, w i) - w 0) = w₂ := by linear_combination -hz
  have H := haven x
  rw [hr, hx] at H
  simpa only [old, ContinuousMap.coe_mk, hw] using H

end NRR.LocalModel
