import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace NRR.LocalModel

open Finset

/-- A sum of n points drawn from the two inverse images of a nonzero
common value, with j copies of the first inverse image. -/
def branchSum (h : ℂ → ℂ) (n j : ℕ) (z : ℂ) : ℂ :=
  (j : ℂ) * h z + ((n - j : ℕ) : ℂ) * h (-z)

theorem balanced_square_rigidity {n : ℕ} [NeZero n] (h : ℂ ≃ ℂ) (hzero : h 0 = 0)
    (avoid : ∀ z ≠ 0, ∀ j ≤ n, branchSum h n j z ≠ 0)
    (w : Fin n → ℂ) (balanced : ∑ i, w i = 0)
    (fair : ∀ i j, (h.symm (w i)) ^ 2 = (h.symm (w j)) ^ 2) :
    ∀ i, w i = 0 := by
  classical
  let z := h.symm (w 0)
  have branches (i : Fin n) : w i = h z ∨ w i = h (-z) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (fair i 0) with hi | hi
    · exact Or.inl (by simpa [z] using congrArg h hi)
    · exact Or.inr (by simpa [z] using congrArg h hi)
  have hz : z = 0 := by
    by_contra hn
    let a : Finset (Fin n) := univ.filter (fun i => w i = h z)
    have ha : a ⊆ univ := subset_univ a
    have hcard : a.card ≤ n := by simpa using Finset.card_le_card ha
    have hsum : (∑ i, w i) = branchSum h n a.card z := by
      rw [← Finset.sum_sdiff ha]
      have hl : ∀ i ∈ a, w i = h z := fun i hi => (mem_filter.mp hi).2
      have hr : ∀ i ∈ univ \ a, w i = h (-z) := by
        intro i hi
        exact (branches i).resolve_left (fun e => (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, e⟩))
      rw [sum_congr rfl hr, sum_congr rfl hl]
      simp [branchSum, card_sdiff_of_subset ha, nsmul_eq_mul, add_comm]
    exact avoid z hn a.card hcard (hsum.symm.trans balanced)
  intro i
  simpa [hz, hzero] using branches i

/-- The expansion used to avoid all intermediate roots in the two-branch map.
`s` and `v` are real angular data, with opposite values at antipodal arguments. -/
theorem angular_expansion (n j : ℕ) (hj : j ≤ n) (u : ℂ) (s v : ℝ) :
    (j : ℂ) * (u * (1 + s) * (1 + Complex.I * v)) +
      ((n - j : ℕ) : ℂ) * ((-u) * (1 - s) * (1 - Complex.I * v)) =
      u * ((2 * (j : ℂ) - n + n * s) +
        Complex.I * ((n : ℂ) + (2 * (j : ℂ) - n) * s) * v) := by
  rw [Nat.cast_sub hj]
  ring

theorem angular_nonzero (n j : ℕ) (hn : 0 < n) (hj : j ≤ n)
    (s v : ℝ) (hs₁ : -1 < s) (hs₂ : s < 1)
    (miss : v = 0 → 2 * (j : ℝ) - n + n * s ≠ 0) :
    (↑(2 * (j : ℝ) - n + n * s) : ℂ) +
      Complex.I * ↑((n : ℝ) + (2 * (j : ℝ) - n) * s) * ↑v ≠ 0 := by
  have hjr : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < (n : ℝ) + (2 * (j : ℝ) - n) * s := by
    have h₁ := mul_nonneg (show 0 ≤ (j : ℝ) by positivity) (show 0 ≤ 1+s by linarith)
    have h₂ := mul_nonneg (sub_nonneg.mpr hjr) (show 0 ≤ 1-s by linarith)
    by_cases h : (j : ℝ) = 0
    · nlinarith [mul_pos hnr (show 0 < 1-s by linarith)]
    · nlinarith [mul_pos (lt_of_le_of_ne (by positivity : 0 ≤ (j : ℝ)) (Ne.symm h))
        (show 0 < 1+s by linarith)]
  intro heq
  have him := congrArg Complex.im heq
  have hre := congrArg Complex.re heq
  simp [Complex.add_im, Complex.mul_im, Complex.mul_re] at him
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im] at hre
  exact miss (by rcases him with h | h; exact (hc.ne' h).elim; exact h) hre

end NRR.LocalModel
