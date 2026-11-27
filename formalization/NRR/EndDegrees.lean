import NRR.Binomial
import Mathlib.Data.Nat.Choose.Sum

/-! Binomial multiplicities of the prescribed end windings for arbitrary n. -/

namespace NRR.Binomial
open Finset

private def halfEntry (n : ℕ) (a : ℕ → ℤ) (j : ℕ) : ℤ :=
  (if j = 0 then 1 else 0) + (if j ∈ halfIndices n then a j else 0)

/-- At an even central index both contributions are present. -/
def degreeProfile (n : ℕ) (a : ℕ → ℤ) (j : ℕ) : ℤ :=
  halfEntry n a j + halfEntry n a (n-j)

theorem degreeProfile_symm (n : ℕ) (a : ℕ → ℤ) {j : ℕ} (hj : j ≤ n) :
    degreeProfile n a (n-j) = degreeProfile n a j := by
  simp only [degreeProfile, Nat.sub_sub_self hj, add_comm]

theorem degreeProfile_zero (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℤ) : degreeProfile n a 0 = 1 := by
  have hh : ¬n ≤ n/2 := by omega
  simp [degreeProfile, halfEntry, halfIndices, hh, show n ≠ 0 by omega]

private theorem halfEntry_sum (n : ℕ) (a : ℕ → ℤ) :
    (∑ j ∈ range (n+1), (n.choose j : ℤ) * halfEntry n a j) =
      1 + ∑ j ∈ halfIndices n, a j * n.choose j := by
  classical
  have hh : ((range (n+1)).filter (· ∈ halfIndices n)) = halfIndices n := by
    ext j
    simp only [mem_filter, mem_range, and_iff_right_iff_imp]
    intro hj
    have := (mem_Icc.mp hj).2
    omega
  simp only [halfEntry, mul_add, sum_add_distrib, mul_ite, mul_zero, mul_one]
  rw [← sum_filter, ← sum_filter, hh]
  simp [mul_comm]

private theorem reflect_row (n : ℕ) (f : ℕ → ℤ) :
    (∑ j ∈ range (n+1), (n.choose j : ℤ) * f (n-j)) =
    ∑ j ∈ range (n+1), (n.choose j : ℤ) * f j := by
  calc
    _ = ∑ j ∈ range (n+1), (n.choose (n-j) : ℤ) * f (n-j) := by
      apply sum_congr rfl
      intro j hj
      rw [Nat.choose_symm (by simpa [Nat.lt_succ_iff] using hj : j ≤ n)]
    _ = _ := by
      simpa using sum_range_reflect (fun j => (n.choose j : ℤ) * f j) (n+1)

theorem degreeProfile_sum (n : ℕ) (a : ℕ → ℤ) :
    (∑ j ∈ range (n+1), (n.choose j : ℤ) * degreeProfile n a j) =
      2 * (1 + ∑ j ∈ halfIndices n, a j * n.choose j) := by
  simp only [degreeProfile, mul_add, sum_add_distrib, reflect_row, halfEntry_sum, two_mul]
  abel

/-- Fix the sign of the first of r+1 roots. Among the other r roots, choose
the positive subset. Each end has the two adjacent contributions shown below. -/
theorem twice_end_sum (r : ℕ) (d : ℕ → ℤ)
    (symm : ∀ j ≤ r+2, d (r+2-j) = d j) :
    2 * (∑ S : Finset (Fin r), (d (S.card+1) + d (S.card+2))) =
      ∑ j ∈ range (r+3), ((r+2).choose j : ℤ) * d j := by
  have end_eq : (∑ S : Finset (Fin r), (d (S.card+1) + d (S.card+2))) =
      ∑ j ∈ range (r+2), ((r+1).choose j : ℤ) * d (j+1) := by
    have H := sum_powerset_apply_card (x := (univ : Finset (Fin r))) (fun j => d (j+1) + d (j+2))
    simp only [powerset_univ, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add, sum_add_distrib] at H
    rw [sum_add_distrib]
    exact H.trans (Finset.sum_choose_succ_mul (fun j _ => d (j+1)) r).symm
  have hhalf : (∑ j ∈ range (r+2), ((r+1).choose j : ℤ) * d j) =
      ∑ j ∈ range (r+2), ((r+1).choose j : ℤ) * d (j+1) := by
    rw [← reflect_row (r+1) d]
    apply sum_congr rfl
    intro j hj
    have hj' : j < r+2 := mem_range.mp hj
    have he : r+1-j = r+2-(j+1) := by omega
    rw [he, symm (j+1) (by omega)]
  rw [end_eq, Finset.sum_choose_succ_mul (fun j _ => d j) (r+1), hhalf, two_mul]

/-- The actual integer prescription on all sign representatives has total zero
for each non-prime-power block count. -/
theorem exists_balanced_profile (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ a : ℕ → ℤ, let d := degreeProfile (r+2) a
      d 0 = 1 ∧ (∀ j ≤ r+2, d (r+2-j) = d j) ∧
      (∑ S : Finset (Fin r), (d (S.card+1) + d (S.card+2))) = 0 := by
  obtain ⟨a, ha⟩ := exists_cancelling_coefficients (by omega : 2 ≤ r+2) hn
  have hs := fun j (hj : j ≤ r+2) => degreeProfile_symm (r+2) a hj
  refine ⟨a, degreeProfile_zero _ (by omega) _, hs, ?_⟩
  have h := twice_end_sum r (degreeProfile (r+2) a) hs
  rw [degreeProfile_sum, ha, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end NRR.Binomial
