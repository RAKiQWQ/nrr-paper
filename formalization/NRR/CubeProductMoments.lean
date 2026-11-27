import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Lebesgue moments of genuine products with the passive cube. These results
assume a product block; they do not assert the geometric rigidity needed to
deduce that an arbitrary convex partition consists of product blocks. -/

noncomputable section
open Set MeasureTheory

namespace NRR.CubeProductMoments

abbrev Active := (ℝ × ℝ) × ℝ
abbrev Passive (k : ℕ) := Fin k → ℝ

/-- This includes the one-point zero-dimensional cube. -/
def passiveCube (k : ℕ) : Set (Passive k) := Icc (fun _ => -1) (fun _ => 1)

theorem passiveCube_volume (k : ℕ) :
    (volume (passiveCube k)).toReal = (2 : ℝ) ^ k := by
  rw [passiveCube, Real.volume_Icc_pi_toReal (by intro i; norm_num)]
  norm_num

/-- Fubini for an arbitrary active density, with actual ambient volume. -/
theorem integral_active (k : ℕ) (B : Set Active) (f : Active → ℝ) :
    (∫ v in B ×ˢ passiveCube k, f v.1 ∂volume) =
      (2 : ℝ) ^ k * ∫ x in B, f x ∂volume := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_fst]
  simp [Measure.real, passiveCube_volume, smul_eq_mul]

theorem normalized_integral_active (k : ℕ) (n : ℝ) (B : Set Active)
    (f : Active → ℝ) :
    n / 2 ^ (k + 3) * (∫ v in B ×ˢ passiveCube k, f v.1 ∂volume) =
      n / 8 * ∫ x in B, f x ∂volume := by
  rw [integral_active, pow_add]
  norm_num
  field_simp

theorem integral_passiveCube_coordinate (k : ℕ) (j : Fin k) :
    (∫ r in passiveCube k, r j ∂volume) = 0 := by
  let f : Passive k → ℝ := (passiveCube k).indicator (fun r => r j)
  have hmem (r : Passive k) : -r ∈ passiveCube k ↔ r ∈ passiveCube k := by
    simp only [passiveCube, mem_Icc, Pi.le_def, Pi.neg_apply]
    constructor <;> intro h <;> constructor <;> intro i <;>
      have h₁ := h.1 i <;> have h₂ := h.2 i <;> linarith
  have hodd (r : Passive k) : f (-r) = -f r := by
    by_cases h : r ∈ passiveCube k
    · simp [f, h, hmem r]
    · simp [f, h, hmem r]
  have heq := integral_neg_eq_self f (volume : Measure (Passive k))
  simp_rw [hodd, integral_neg] at heq
  have hz : (∫ r, f r ∂volume) = 0 := by linarith
  change (∫ r, (passiveCube k).indicator (fun r => r j) r ∂volume) = 0 at hz
  rw [integral_indicator (show MeasurableSet (passiveCube k) from measurableSet_Icc)] at hz
  exact hz

/-- Every extra first moment vanishes on a product block. -/
theorem normalized_integral_passive (k : ℕ) (n : ℝ) (B : Set Active) (j : Fin k) :
    n / 2 ^ (k + 3) * (∫ v in B ×ˢ passiveCube k, v.2 j ∂volume) = 0 := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_fun_snd (fun r : Passive k => r j), integral_passiveCube_coordinate]
  simp

/-- The four densities in the cube construction, in their specified order. -/
def density (i : Fin 4) (x : Active) : ℝ :=
  ![x.1.1, x.1.2, (1 + x.1.1) * x.2, x.1.2 * x.2] i

def moments3 (n : ℝ) (B : Set Active) : Fin 4 → ℝ :=
  fun i => n / 8 * ∫ x in B, density i x ∂volume

def productMoments (k : ℕ) (n : ℝ) (B : Set Active) : Fin 4 → ℝ :=
  fun i => n / 2 ^ (k + 3) * ∫ v in B ×ˢ passiveCube k, density i v.1 ∂volume

/-- All four volume moments agree, including when `k = 0`. -/
theorem productMoments_eq (k : ℕ) (n : ℝ) (B : Set Active) :
    productMoments k n B = moments3 n B := by
  funext i
  exact normalized_integral_active k n B (density i)

/-- The very same scalar readouts transfer an exclusion from three dimensions
to product blocks. They may in particular evaluate two rational polynomials;
no change of coefficients or readouts is necessary. -/
theorem transfer_exclusion {ι : Type*} (k : ℕ) (n : ℝ) (B : ι → Set Active)
    (P Q : (Fin 4 → ℝ) → ℝ)
    (h : ¬ ∃ p q : ℝ, ∀ i, P (moments3 n (B i)) = p ∧ Q (moments3 n (B i)) = q) :
    ¬ ∃ p q : ℝ, ∀ i,
      P (productMoments k n (B i)) = p ∧ Q (productMoments k n (B i)) = q := by
  simpa only [productMoments_eq] using h

end NRR.CubeProductMoments
