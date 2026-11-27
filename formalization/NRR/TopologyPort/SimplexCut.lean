/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Tactic

/-!
# Morphisms to `⦋1⦌`

We define a bijective map `SimplexCategory.toMk₁ : Fin (n + 2) → ⦋n⦌ ⟶ ⦋1⦌`.
This is used in the file `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne`
in the study of simplices in the simplicial set `Δ[1]`.

-/



universe u

open CategoryTheory

open scoped Simplicial

namespace SimplexCategory

/-- Given `i : Fin (n + 2)`, this is the morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex
category which corresponds to the monotone map `Fin (n + 1) → Fin 2` which
takes `i` times the value `0`. -/
def toMk₁ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋1⦌ :=
  Hom.mk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs with h₁ h₂ h₂ <;> try norm_num
        exact False.elim (h₁ (lt_of_le_of_lt (by exact h) h₂)) }

@[local grind =]
lemma toMk₁_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
  toMk₁ i j = if j.castSucc < i then 0 else 1 := rfl



lemma toMk₁_apply_eq_zero_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    toMk₁ i j = 0 ↔ j.castSucc < i := by
  change (if j.castSucc < i then (0 : Fin 2) else 1) = 0 ↔ j.castSucc < i
  split_ifs <;> simp_all

lemma toMk₁_of_castSucc_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    toMk₁ i j = 0 := by
  change (if j.castSucc < i then (0 : Fin 2) else 1) = 0
  rw [if_pos h]

lemma toMk₁_apply_eq_one_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    toMk₁ i j = 1 ↔ i ≤ j.castSucc := by
  change (if j.castSucc < i then (0 : Fin 2) else 1) = 1 ↔ i ≤ j.castSucc
  by_cases h : j.castSucc < i
  · simp [h,not_le.mpr h]
  · simp [h,not_lt.mp h]

lemma toMk₁_of_le_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    toMk₁ i j = 1 := by
  change (if j.castSucc < i then (0 : Fin 2) else 1) = 1
  rw [if_neg (not_lt.mpr h)]

lemma δ_comp_toMk₁_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc) :
    δ j ≫ toMk₁ i =
      toMk₁ (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))
  simp only [Fin.castSucc_le_castSucc_iff] at h
  rw [Fin.castPred_castSucc]
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i.castSucc (j.succAbove k) = _
  change (if (j.succAbove k).val < i.val then (0 : Fin 2) else 1) =
    (if k.val < i.val then 0 else 1)
  change i.val ≤ j.val at h
  simp only [Fin.succAbove,Fin.lt_def,Fin.coe_castSucc,apply_ite Fin.val,Fin.val_succ]
  split_ifs <;> omega

lemma δ_comp_toMk₁_of_lt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    δ j ≫ toMk₁ i = toMk₁ (i.pred (Fin.ne_zero_of_lt h)) := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  rw [Fin.pred_succ]
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i.succ (j.succAbove k) = _
  change (if (j.succAbove k).val < i.val+1 then (0 : Fin 2) else 1) =
    (if k.val < i.val then 0 else 1)
  change j.val < i.val+1 at h
  simp only [Fin.succAbove,Fin.lt_def,Fin.coe_castSucc,apply_ite Fin.val,Fin.val_succ]
  split_ifs <;> omega

lemma σ_comp_toMk₁_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    σ j ≫ toMk₁ i = toMk₁ i.castSucc := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i (j.predAbove k) = _
  change (if (j.predAbove k).val < i.val then (0 : Fin 2) else 1) =
    (if k.val < i.val then 0 else 1)
  change i.val ≤ j.val at h
  simp only [Fin.predAbove,Fin.lt_def,Fin.coe_castSucc,apply_dite Fin.val,
    Fin.coe_pred,Fin.coe_castPred,dite_eq_ite]
  split_ifs <;> omega

lemma σ_comp_toMk₁_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    σ j ≫ toMk₁ i = toMk₁ i.succ := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  change toMk₁ i (j.predAbove k) = _
  change (if (j.predAbove k).val < i.val then (0 : Fin 2) else 1) =
    (if k.val < i.val+1 then 0 else 1)
  change j.val < i.val at h
  simp only [Fin.predAbove,Fin.lt_def,Fin.coe_castSucc,apply_dite Fin.val,
    Fin.coe_pred,Fin.coe_castPred,dite_eq_ite]
  split_ifs <;> omega


end SimplexCategory
