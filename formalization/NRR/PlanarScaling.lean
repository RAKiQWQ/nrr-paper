import NRR.PlanarExistence

/-! Quantitative scaling of the two-interface correction. -/

open Set Topology Finset
noncomputable section
set_option maxHeartbeats 800000

namespace NRR.LocalModel

open RootSums

def scaledCorrection (σ : ℝ) (D : C(ℂ × ℂ, ℂ)) : C(ℂ × ℂ, ℂ) :=
  ⟨fun y => (σ:ℂ)^2 * D (y.1/(σ:ℂ), y.2/(σ:ℂ)), by fun_prop⟩

theorem scaledCorrection_bound (σ : ℝ) (D : C(ℂ × ℂ, ℂ)) {M : ℝ}
    (hD : ∀ y, ‖D y‖ ≤ M) (y : ℂ × ℂ) :
    ‖scaledCorrection σ D y‖ ≤ σ^2 * M := by
  simp only [scaledCorrection,ContinuousMap.coe_mk]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (hD _) (sq_nonneg σ)

theorem squareTest_div (h : ℂ ≃ₜ ℂ)
    (hh : ∀ t : ℝ, 0 < t → ∀ z, h ((t:ℂ)*z) = (t:ℂ)*h z)
    {σ : ℝ} (hσ : 0 < σ) (z : ℂ) :
    squareTest h (z/(σ:ℂ)) = squareTest h z/(σ:ℂ)^2 := by
  have he := Surface.squareTest_pos_mul h hh σ⁻¹ (inv_pos.mpr hσ) z
  simpa only [Complex.ofReal_inv, inv_mul_eq_div, inv_pow] using he

/-- The local exclusion survives arbitrary positive rescaling, and its
correction is uniformly of quadratic size. -/
theorem scaled_planar_avoid {m : ℕ} [NeZero m] (h : ℂ ≃ₜ ℂ)
    (hh : ∀ t : ℝ, 0 < t → ∀ z, h ((t:ℂ)*z) = (t:ℂ)*h z)
    (D : C(ℂ × ℂ, ℂ))
    (avoid : ∀ (w : Fin m → ℂ) (w₂ q : ℂ), (∑ i, w i) + w₂ = 0 →
      (∀ i, squareTest h (w i) - shift i = q) →
      squareTest h w₂ + D (w 0, (∑ i, w i) - w 0) ≠ q)
    {σ : ℝ} (hσ : 0 < σ) (w : Fin m → ℂ) (w₂ q : ℂ)
    (balanced : (∑ i, w i) + w₂ = 0)
    (fair : ∀ i, squareTest h (w i) - (σ:ℂ)^2 * shift i = q) :
    squareTest h w₂ + scaledCorrection σ D (w 0, (∑ i, w i) - w 0) ≠ q := by
  have hσc : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hσ2 : (σ:ℂ)^2 ≠ 0 := pow_ne_zero 2 hσc
  have hb : (∑ i, w i/(σ:ℂ)) + w₂/(σ:ℂ) = 0 := by
    rw [← sum_div, ← add_div, balanced, zero_div]
  have hf (i : Fin m) : squareTest h (w i/(σ:ℂ)) - shift i = q/(σ:ℂ)^2 := by
    rw [squareTest_div h hh hσ]
    apply (eq_div_iff hσ2).mpr
    calc
      _ = squareTest h (w i) - (σ:ℂ)^2 * shift i := by field_simp
      _ = q := fair i
  have hn := avoid (fun i => w i/(σ:ℂ)) (w₂/(σ:ℂ)) (q/(σ:ℂ)^2) hb hf
  intro he
  apply hn
  dsimp only at hn ⊢
  rw [squareTest_div h hh hσ, ← sum_div, ← sub_div]
  apply (eq_div_iff hσ2).mpr
  change (squareTest h w₂/(σ:ℂ)^2 + D (w 0/(σ:ℂ), ((∑ i, w i)-w 0)/(σ:ℂ))) *
    (σ:ℂ)^2 = q
  calc
    _ = squareTest h w₂ + scaledCorrection σ D (w 0, (∑ i, w i)-w 0) := by
      dsimp [scaledCorrection]
      field_simp
    _ = q := he

end NRR.LocalModel
