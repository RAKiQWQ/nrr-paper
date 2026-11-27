import NRR.Statement
import NRR.Partitions
import Mathlib.Tactic

/-!
The test map for the positive direction of the classification.

These lemmas construct and identify the continuous, permutation-equivariant
map into copies of the reduced regular representation. They do not assert
the configuration-space zero theorem needed to finish prime-power existence.
-/

noncomputable section
open Set MeasureTheory Finset

namespace NRR.PrimePower

def rowMean {n : ℕ} (v : Fin n → ℝ) : ℝ := (∑ i, v i) / (n : ℝ)

def centered {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := fun i => v i - rowMean v

theorem sum_centered {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    ∑ i, centered v i = 0 := by
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [centered, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, rowMean]
  field_simp
  ring

theorem centered_eq_zero_iff {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    centered v = 0 ↔ ∀ i j, v i = v j := by
  constructor
  · intro h i j
    have hi : v i - rowMean v = 0 := congrFun h i
    have hj : v j - rowMean v = 0 := congrFun h j
    linarith
  · intro h
    funext i
    have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hs : (∑ j, v j) = (n : ℝ) * v i := by
      calc
        _ = ∑ _j : Fin n, v i := sum_congr rfl (fun j _ => h j i)
        _ = _ := by simp
    change v i - (∑ j, v j) / (n : ℝ) = 0
    rw [hs]
    field_simp
    ring

theorem rowMean_reindex {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ) :
    rowMean (fun i => v (σ i)) = rowMean v := by
  unfold rowMean
  rw [Equiv.sum_comp σ v]

theorem centered_reindex {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ) :
    centered (fun i => v (σ i)) = fun i => centered v (σ i) := by
  funext i
  simp only [centered, rowMean_reindex]

/-- One reduced permutation representation for each characteristic. -/
def reducedValues (d n : ℕ) : Submodule ℝ (Fin (d - 1) → Fin n → ℝ) where
  carrier := {v | ∀ k, ∑ i, v k i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw k
    simp only [Pi.add_apply, sum_add_distrib, hv k, hw k, add_zero]
  smul_mem' := by
    intro r v hv k
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, hv k, mul_zero]

abbrev ReducedValues (d n : ℕ) := reducedValues d n

/-- Deleting one coordinate in each zero-sum row is a linear equivalence.
The deleted value is reconstructed as the negative sum of the others. -/
def reducedValuesEquiv (d m : ℕ) :
    ReducedValues d (m + 1) ≃ₗ[ℝ] (Fin (d - 1) → Fin m → ℝ) where
  toFun v k i := v.val k i.succ
  invFun w := ⟨fun k => Fin.cons (-(∑ i, w k i)) (w k), by
    intro k
    simp [Fin.sum_univ_succ]⟩
  left_inv v := by
    apply Subtype.ext
    funext k i
    refine Fin.cases ?_ (fun j => ?_) i
    · change -(∑ j : Fin m, v.val k j.succ) = v.val k 0
      have hv := v.property k
      rw [Fin.sum_univ_succ] at hv
      linarith
    · rfl
  right_inv w := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_reducedValues (d m : ℕ) :
    Module.finrank ℝ (ReducedValues d (m + 1)) = (d - 1) * m := by
  rw [(reducedValuesEquiv d m).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Centering the characteristic values removes precisely their common value. -/
def evaluation {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) :
    C(Fin n → Body d, ReducedValues d n) where
  toFun S := ⟨fun k => centered (fun i => φ k (S i).toCompactConvex),
    fun k => sum_centered hn _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    apply continuous_pi
    intro i
    let v (j : Fin n) : (Fin n → Body d) → ℝ := fun S => φ k (S j).toCompactConvex
    have cv (j : Fin n) : Continuous (v j) :=
      (φ k).continuous.comp
        ((continuous_subtype_val.comp (continuous_apply j)).subtype_mk _)
    exact (cv i).sub ((continuous_finset_sum _ (fun j _ => cv j)).div_const _)

theorem evaluation_eq_zero_iff {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (S : Fin n → Body d) :
    (evaluation hn φ S).val = 0 ↔
      ∀ k i j, φ k (S i).toCompactConvex = φ k (S j).toCompactConvex := by
  constructor
  · intro h k
    exact (centered_eq_zero_iff hn _).mp (congrFun h k)
  · intro h
    funext k
    exact (centered_eq_zero_iff hn _).mpr (h k)

/-- Relabeling the cells relabels the test vector by exactly the same permutation. -/
theorem evaluation_reindex {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (σ : Equiv.Perm (Fin n))
    (S : Fin n → Body d) :
    (evaluation hn φ (fun i => S (σ i))).val =
      fun k i => (evaluation hn φ S).val k (σ i) := by
  funext k
  change centered (fun i => φ k (S (σ i)).toCompactConvex) =
    fun i => centered (fun j => φ k (S j).toCompactConvex) (σ i)
  exact centered_reindex σ (fun j => φ k (S j).toCompactConvex)

/-- Pull the same test map back along an actual continuous family of cells. -/
def testMap {X : Type*} [TopologicalSpace X] {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (cell : Fin n → C(X, Body d)) :
    C(X, ReducedValues d n) :=
  (evaluation hn φ).comp ⟨fun x i => cell i x, continuous_pi (fun i => (cell i).continuous)⟩

theorem testMap_eq_zero_iff {X : Type*} [TopologicalSpace X] {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (cell : Fin n → C(X, Body d)) (x : X) :
    testMap hn φ cell x = 0 ↔
      ∀ k i j, φ k (cell i x).toCompactConvex = φ k (cell j x).toCompactConvex := by
  rw [← Subtype.val_inj]
  exact evaluation_eq_zero_iff hn φ (fun i => cell i x)

/-- A zero of the characteristic test map supplies precisely the missing
equal-value condition; coverage and equal mass come from the geometric family. -/
theorem fairPartition_of_testMap_zero {X : Type*} [TopologicalSpace X] {d n : ℕ}
    (hn : 0 < n) (K : Body d) (μ : Measure (Space d))
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (cell : Fin n → C(X, Body d))
    (x : X) (hp : BodyPartition K (fun i => cell i x))
    (hm : EqualMass μ (fun i => cell i x)) (hz : testMap hn φ cell x = 0) :
    ∃ S : Fin n → Body d, BodyPartition K S ∧ EqualMass μ S ∧
      ∀ k i j, φ k (S i).toCompactConvex = φ k (S j).toCompactConvex := by
  exact ⟨fun i => cell i x, hp, hm, (testMap_eq_zero_iff hn φ cell x).mp hz⟩

end NRR.PrimePower
