import NRR.SurfaceResidualWinding
import NRR.SurfaceExtensionEnds
import NRR.EndDegrees

/-! The non-prime-power planar correction, conditional only on realizing
the specified planar two-branch winding profile. -/

open Set Topology Finset
open scoped unitInterval
noncomputable section

namespace NRR.LocalModel

open Surface RootSums

/-- The first sign is positive, and the subset records the other
positive signs. -/
def labelMask (r : ℕ) : EndLabel (r+1) ≃ Finset (Fin r) where
  toFun a := Finset.univ.filter (fun i => a.val i.succ = false)
  invFun S := ⟨Fin.cons false (fun i => decide (i ∉ S)), rfl⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    refine Fin.cases a.property.symm (fun j => ?_) i
    cases e : a.val j.succ <;> simp [e]
  right_inv S := by ext i; simp

theorem positiveCount_eq_mask {r : ℕ} (a : EndLabel (r+1)) :
    positiveCount a.val = (labelMask r a).card + 1 := by
  simp only [positiveCount, labelMask, Equiv.coe_fn_mk, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp [a.property, add_comm]

private theorem label_total {r : ℕ} (d : ℕ → ℤ)
    (hd : (∑ S : Finset (Fin r), (d (S.card+1) + d (S.card+2))) = 0) :
    (∑ a : EndLabel (r+1), (d (positiveCount a.val+1) + d (positiveCount a.val))) = 0 := by
  simp only [positiveCount_eq_mask]
  calc
    _ = ∑ S : Finset (Fin r), (d (S.card+1+1) + d (S.card+1)) :=
      (labelMask r).sum_comp (fun S => d (S.card+1+1) + d (S.card+1))
    _ = ∑ S : Finset (Fin r), (d (S.card+1) + d (S.card+2)) := by
      apply sum_congr rfl
      intro S _
      exact add_comm _ _
    _ = 0 := hd

theorem realShift_injective {m : ℕ} : Function.Injective (realShift (m := m)) := by
  intro i j he
  apply Fin.ext
  apply (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective
  change ((2 : ℝ)^i.val)^2 = ((2 : ℝ)^j.val)^2 at he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · exact he
  · have hi : 0 < (2 : ℝ)^i.val := by positivity
    have hj : 0 < (2 : ℝ)^j.val := by positivity
    linarith

/-- For every non-prime-power block count there is an integer angular
profile such that any positively homogeneous plane homeomorphism with
that profile and the stated antipodal identity gives a bounded correction
depending only on two neighboring interfaces. -/
theorem planar_correction_of_winding_realization (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ a : ℕ → ℤ, ∀ h : ℂ ≃ₜ ℂ, h 0 = 0 →
      (∀ z, h z - h (-z) = 2*z) →
      (∀ t : ℝ, 0 < t → ∀ z, h ((t : ℂ)*z) = (t : ℂ)*h z) →
      ∀ H : C(I × ℂ, ℂ), (∀ s, Function.Injective (fun z => H (s,z))) →
      (∀ z, H (0,z) = z) → (∀ z, H (1,z) = h z) →
      ∀ (avoid : ∀ z ≠ 0, ∀ j ≤ r+2, branchSum h (r+2) j z ≠ 0),
      (∀ j (hj : j ≤ r+2), complexWinding (branchLoop h (r+2) j)
        (fun u => avoid u u.coe_ne_zero j hj) = (Binomial.degreeProfile (r+2) a j : ℝ)) →
      ∃ (M : ℝ) (D : C(ℂ × ℂ, ℂ)), 0 < M ∧ (∀ y, ‖D y‖ ≤ M) ∧
        ∀ (w : Fin (r+1) → ℂ) (w₂ q : ℂ), (∑ i, w i) + w₂ = 0 →
          (∀ i, squareTest h (w i) - shift i = q) →
          squareTest h w₂ + D (w 0, (∑ i, w i) - w 0) ≠ q := by
  obtain ⟨a, _, _, balanced⟩ := Binomial.exists_balanced_profile r hn
  refine ⟨a, ?_⟩
  intro h hzero hdiff hh H hinj h₀ h₁ avoid degrees
  let b := realShift (m := r+1)
  let old := residual (m := r+1) h
  have cf := (squareTest h).continuous
  obtain ⟨T,hT,far⟩ := nonzero_outside_disk h.continuous cf hh (squareTest_pos_mul h hh) (shift (m := r+1))
    (fun signs u => end_limit_of_avoid h hzero avoid signs u)
  obtain ⟨e₁,he₁,hdeg⟩ := exists_actual_residual_winding h hzero hh H hinj h₀ h₁ avoid
    (shift (m := r+1))
  obtain ⟨e₂,he₂,fill⟩ := fillDiskOfZeroTotalWinding b realShift_injective
  let t := min (min e₁ e₂) (T+1)⁻¹ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hsmall : t < min (min e₁ e₂) (T+1)⁻¹ := by dsimp [t] at ht ⊢; linarith
  have ht₁ := hsmall.trans_le ((min_le_left _ _).trans (min_le_left e₁ e₂))
  have ht₂ := hsmall.trans_le ((min_le_left _ _).trans (min_le_right e₁ e₂))
  have hfar : T < (t⁻¹)^2 := by
    have hi := (inv_lt_inv₀ (show 0 < (T+1)⁻¹ by positivity) ht).mpr
      (hsmall.trans_le (min_le_right _ _))
    rw [inv_inv] at hi
    nlinarith [sq_nonneg (t⁻¹-1)]
  have outside (x : realLocus b) (hx : (t⁻¹)^2 ≤ ‖projection b x‖) : old x ≠ 0 :=
    sub_ne_zero.mpr (far (rootValue x) (hfar.trans_le hx) x.val (rootValue_eq x))
  obtain ⟨hs, hfill⟩ := fill t ht ht₂
  have per (c : EndLabel (r+1)) : boundaryWinding b ht hs old
      (fun x => outside x.val x.property.ge) c =
      ((Binomial.degreeProfile (r+2) a (positiveCount c.val+1) +
        Binomial.degreeProfile (r+2) a (positiveCount c.val)) : ℤ) := by
    let e := endBoundaryHomeomorph (shift (m := r+1)) ht hs
    let loop := (old.restrict _).comp (boundaryCircle e c)
    obtain ⟨hloop, hw⟩ := hdeg t ht ht₁ c.val loop (fun _ => rfl)
    change complexWinding loop hloop = _
    rw [hw, Int.cast_add]
    exact congrArg₂ (· + ·) (degrees _ (by have := positiveCount_le c.val; omega))
      (degrees _ (by have := positiveCount_le c.val; omega))
  have total := label_total (Binomial.degreeProfile (r+2) a) balanced
  obtain ⟨G, hG, fix⟩ := hfill old outside (by
    rw [sum_congr rfl fun c _ => per c, ← Int.cast_sum, total, Int.cast_zero])
  apply planar_correction_of_extension h hdiff G hG ((t⁻¹)^2+1)
  intro x hx
  apply fix
  intro inside
  have hd := interior_subset inside
  change projection b x ∈ Metric.closedBall (0 : ℂ) ((t⁻¹)^2) at hd
  rw [Metric.mem_closedBall, dist_zero_right] at hd
  change ‖rootValue x‖ ≤ _ at hd
  linarith

end NRR.LocalModel

