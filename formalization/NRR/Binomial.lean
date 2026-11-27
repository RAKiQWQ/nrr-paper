import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace NRR.Binomial

open Finset

/-- The smaller representative from every complementary pair of inner indices. -/
def halfIndices (n : ℕ) := Icc 1 (n / 2)

def halfGcd (n : ℕ) := (halfIndices n).gcd n.choose

private theorem scaled_choose {p : ℕ} [Fact p.Prime] (a m j : ℕ) :
    (p ^ a * m).choose (p ^ a * j) ≡ m.choose j [MOD p] := by
  induction a with
  | zero => simpa using (Nat.ModEq.refl (m.choose j) : m.choose j ≡ m.choose j [MOD p])
  | succ a ih =>
    rw [pow_succ', Nat.mul_assoc, Nat.mul_assoc]
    have hp : 0 < p := (Fact.out : p.Prime).pos
    exact Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans (by
      simpa [hp, Nat.mul_div_cancel_left] using ih)

private theorem halfGcd_dvd_choose {n j : ℕ} (hj : 0 < j) (hj' : j < n) :
    halfGcd n ∣ n.choose j := by
  by_cases h : j ≤ n / 2
  · exact Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨hj, h⟩)
  · rw [← Nat.choose_symm hj'.le]
    exact Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem halfGcd_eq_one_iff {n : ℕ} (hn : 2 ≤ n) :
    halfGcd n = 1 ↔ ¬ IsPrimePow n := by
  constructor
  · intro h hpow
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
    have hd : p ∣ halfGcd (p ^ a) := Finset.dvd_gcd (fun j hj => by
      obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hj
      exact hp.dvd_choose_pow (by omega) (by omega))
    exact hp.not_dvd_one (h ▸ hd)
  · intro hnpp
    by_contra h
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
    have hm1 : 1 < m := by
      rcases m with _ | _ | m
      · simp_all
      · simp only [Nat.reduceAdd, mul_one] at heq
        exact False.elim (hnpp ((isPrimePow_nat_iff _).mpr
          ⟨p, a, hp, by by_contra! hz; simp_all, heq.symm⟩))
      · omega
    have hpa : 0 < p ^ a := pow_pos hp.pos _
    have hlt : p ^ a < n := by rw [heq]; simpa using Nat.mul_lt_mul_of_pos_left hm1 hpa
    have hc := hd.trans (halfGcd_dvd_choose hpa hlt)
    have hmod : n.choose (p ^ a) ≡ m [MOD p] := by
      simpa [heq] using scaled_choose (p := p) a m 1
    exact hm ((hmod.dvd_iff dvd_rfl).mp hc)

private theorem gcd_combination (s : Finset ℕ) (b : ℕ → ℕ) :
    ∃ a : ℕ → ℤ, ∑ j ∈ s, a j * b j = (s.gcd b : ℕ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨a, ha⟩ := ih
    let x := Nat.gcdA (b j) (s.gcd b)
    let y := Nat.gcdB (b j) (s.gcd b)
    refine ⟨fun k => if k = j then x else y * a k, ?_⟩
    simp only [Finset.sum_insert hj]
    have hsum : (∑ k ∈ s, (if k = j then x else y * a k) * b k) =
        y * ∑ k ∈ s, a k * b k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_neg (show k ≠ j from fun e => hj (e ▸ hk)), mul_assoc]
    rw [hsum, ha, Finset.gcd_insert]
    exact (by simpa [x, y, mul_comm] using (Nat.gcd_eq_gcd_ab (b j) (s.gcd b)).symm)

/-- Integer coefficients on the half row are sufficient, with the full central
coefficient included when n is even. This is the arithmetic input to the surface. -/
theorem exists_cancelling_coefficients {n : ℕ} (hn : 2 ≤ n) (hnpp : ¬ IsPrimePow n) :
    ∃ a : ℕ → ℤ, 1 + ∑ j ∈ halfIndices n, a j * n.choose j = 0 := by
  obtain ⟨a, ha⟩ := gcd_combination (halfIndices n) n.choose
  change _ = (halfGcd n : ℤ) at ha
  rw [(halfGcd_eq_one_iff hn).mpr hnpp] at ha
  exact ⟨fun j => -a j, by simp only [neg_mul, Finset.sum_neg_distrib, ha]; norm_num⟩

end NRR.Binomial
