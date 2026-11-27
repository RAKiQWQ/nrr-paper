import NRR.PrimePowerTopologyTwistedFundamental
import NRR.SingularHomologySubdivisionGeometry
import NRR.SingularHomologyLocalComparison
import Mathlib.Algebra.BigOperators.Fin

/-! A finite configuration detected by precisely one actual staircase simplex.
The constructions below concern the genuine cube collapse and singular maps. -/

noncomputable section
open Set Topology CategoryTheory
open scoped OnePoint NNReal
open NRR.PrimePower NRR.SingularHomology
open NRR.SingularHomology.SimplexGeometry

namespace NRR.PrimePowerTopology

theorem staircaseCoordinate_antitone {m : ℕ} (π : Equiv.Perm (Fin m))
    (x : Simplex m) {a b : Fin m} (hab : π a ≤ π b) :
    staircaseCoordinate π b x ≤ staircaseCoordinate π a x := by
  classical
  apply Finset.sum_le_sum
  intro k hk
  by_cases hb : (π b).val < k.val
  · have ha : (π a).val < k.val := lt_of_le_of_lt hab hb
    simp [ha, hb]
  · simp only [if_neg hb]
    split_ifs <;> positivity

/-- Every positive barycentric coordinate makes the coordinate ordering strict. -/
theorem staircaseCoordinate_strictAntitone {m : ℕ} (π : Equiv.Perm (Fin m))
    (x : Simplex m) (hx : ∀ k, 0 < (x k : ℝ)) {a b : Fin m}
    (hab : π a < π b) :
    staircaseCoordinate π b x < staircaseCoordinate π a x := by
  classical
  apply Finset.sum_lt_sum
  · intro k hk
    by_cases hb : (π b).val < k.val
    · have ha : (π a).val < k.val := lt_trans hab hb
      simp [ha, hb]
    · simp only [if_neg hb]
      split_ifs <;> positivity
  · refine ⟨(π a).succ, Finset.mem_univ _, ?_⟩
    have ha : (π a).val < ((π a).succ).val := by simp
    have hb : ¬ (π b).val < ((π a).succ).val := by
      simp only [Fin.val_succ]
      exact Nat.not_lt.mpr hab
    simpa only [if_pos ha, if_neg hb] using hx (π a).succ

/-- The uniform barycenter in the actual topological simplex. -/
def staircaseBarycenter (m : ℕ) : Simplex m :=
  faceCenter Finset.univ ⟨0, Finset.mem_univ _⟩

@[simp] theorem staircaseBarycenter_apply (m : ℕ) (k : Fin (m+1)) :
    staircaseBarycenter m k = (m+1 : ℝ≥0)⁻¹ := by
  simp [staircaseBarycenter, faceCenter_apply]

theorem staircaseBarycenter_pos (m : ℕ) (k : Fin (m+1)) :
    0 < (staircaseBarycenter m k : ℝ) := by
  simp only [staircaseBarycenter_apply, NNReal.coe_inv]
  positivity

/-- The selected cube point is the actual image of the uniform barycenter. -/
def staircaseSelectedCubePoint (m : ℕ) : Fin m → Set.Icc (0 : ℝ) 1 :=
  staircaseUnitCubeSimplex (Equiv.refl _) (staircaseBarycenter m)

theorem staircaseSelectedCubePoint_strictAnti (m : ℕ) :
    StrictAnti (fun a => (staircaseSelectedCubePoint m a).val) := by
  intro a b hab
  exact staircaseCoordinate_strictAntitone (Equiv.refl _) _
    (staircaseBarycenter_pos m) hab

theorem staircaseSelectedCubePoint_interior (d n : ℕ) :
    staircaseSelectedCubePoint (n*d) ∈ configurationCubeInterior d n := by
  classical
  intro a
  constructor
  · change 0 < staircaseCoordinate (Equiv.refl _) a (staircaseBarycenter (n*d))
    apply Finset.sum_pos'
    · intro k hk
      split_ifs <;> positivity
    · refine ⟨a.succ, Finset.mem_univ _, ?_⟩
      simpa using staircaseBarycenter_pos (n*d) a.succ
  · have hs : (∑ k : Fin (n*d+1),
        (staircaseBarycenter (n*d) k : ℝ)) = 1 := by
      exact_mod_cast (staircaseBarycenter (n*d)).property
    change staircaseCoordinate (Equiv.refl _) a (staircaseBarycenter (n*d)) < 1
    rw [← hs]
    apply Finset.sum_lt_sum
    · intro k hk
      split_ifs <;> first | exact le_rfl | positivity
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simpa using staircaseBarycenter_pos (n*d) 0

/-- A strict identity ordering cannot be realized by any other chamber. -/
theorem staircaseUnitCubeSimplex_selected_eq_perm {m : ℕ}
    (π : Equiv.Perm (Fin m)) (x : Simplex m)
    (hx : staircaseUnitCubeSimplex π x = staircaseSelectedCubePoint m) :
    π = Equiv.refl _ := by
  have hmono : StrictMono π := by
    intro a b hab
    by_contra h
    have hle : π b ≤ π a := le_of_not_gt h
    have hcoord := staircaseCoordinate_antitone π x hle
    have ha := congrArg (fun y => (y a).val) hx
    have hb := congrArg (fun y => (y b).val) hx
    change staircaseCoordinate π a x = _ at ha
    change staircaseCoordinate π b x = _ at hb
    rw [ha, hb] at hcoord
    exact (not_le_of_gt (staircaseSelectedCubePoint_strictAnti m hab)) hcoord
  let e : Fin m ≃o Fin m := ⟨π, hmono.le_iff_le⟩
  have he : e = OrderIso.refl (Fin m) := Subsingleton.elim _ _
  ext a
  exact congrArg Fin.val (congrArg (fun f : Fin m ≃o Fin m => f a) he)

theorem configurationCubeInteriorEuclidean_apply {d n : ℕ}
    (x : configurationCubeInterior d n) (i : Fin n) (j : Fin d) :
    EuclideanSpace.equiv (Fin d) ℝ (configurationCubeInteriorEuclidean d n x i) j =
      unitOpenIntervalToReal
        ⟨(x.val (configurationAxisEquiv d n (i,j))).val,
          x.property (configurationAxisEquiv d n (i,j))⟩ := by
  simp [configurationCubeInteriorEuclidean]

/-- Distinct scalar cube coordinates imply distinct sites, using any one
physical coordinate. This is why the hypothesis `0 < d` suffices. -/
theorem staircaseSelectedCubePoint_injective {d n : ℕ} (hd : 0 < d) :
    Function.Injective (configurationCubeInteriorEuclidean d n
      ⟨staircaseSelectedCubePoint (n*d), staircaseSelectedCubePoint_interior d n⟩) := by
  intro i l hil
  let j : Fin d := ⟨0,hd⟩
  have hc := congrArg (fun p : Space d => EuclideanSpace.equiv (Fin d) ℝ p j) hil
  simp only [configurationCubeInteriorEuclidean_apply] at hc
  have hs := unitOpenIntervalToReal.injective hc
  have hv := congrArg Subtype.val hs
  have ha := (staircaseSelectedCubePoint_strictAnti (n*d)).injective hv
  have hp := (configurationAxisEquiv d n).injective ha
  exact congrArg Prod.fst hp

/-- The actual finite configuration selected by the identity chamber. -/
def staircaseSelectedConfiguration {d n : ℕ} (hd : 0 < d) : Configuration d n :=
  ⟨configurationCubeInteriorEuclidean d n
    ⟨staircaseSelectedCubePoint (n*d), staircaseSelectedCubePoint_interior d n⟩,
    staircaseSelectedCubePoint_injective hd⟩

@[simp] theorem configurationCubeCollapse_selected {d n : ℕ} (hd : 0 < d) :
    configurationCubeCollapse d n (staircaseSelectedCubePoint (n*d)) =
      (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n)) :=
  configurationCubeCollapse_interior_configuration _ (staircaseSelectedCubePoint_injective hd)

/-- Every finite configuration has exactly its chart inverse as cube fiber. -/
theorem configurationCubeCollapse_finite_fiber {d n : ℕ}
    (x : ConfigurationCube d n) (z : Configuration d n)
    (hx : configurationCubeCollapse d n x = (z : OnePoint (Configuration d n))) :
    x = ((configurationCubeInteriorEuclidean d n).symm z.val).val := by
  by_cases hi : x ∈ configurationCubeInterior d n
  · let y : configurationCubeInterior d n := ⟨x,hi⟩
    by_cases hinj : Function.Injective (configurationCubeInteriorEuclidean d n y)
    · rw [configurationCubeCollapse_interior_configuration y hinj] at hx
      have he := congrArg Subtype.val (OnePoint.coe_injective hx)
      have hy := (configurationCubeInteriorEuclidean d n).eq_symm_apply.mpr he
      exact congrArg Subtype.val hy
    · rw [configurationCubeCollapse_interior_collision y hinj] at hx
      exact ((OnePoint.coe_ne_infty z) hx.symm).elim
  · rw [configurationCubeCollapse_boundary x hi] at hx
    exact ((OnePoint.coe_ne_infty z) hx.symm).elim

theorem configurationCubeCollapse_selected_fiber {d n : ℕ} (hd : 0 < d)
    (x : ConfigurationCube d n)
    (hx : configurationCubeCollapse d n x =
      (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n))) :
    x = staircaseSelectedCubePoint (n*d) := by
  simpa [staircaseSelectedConfiguration] using
    configurationCubeCollapse_finite_fiber x (staircaseSelectedConfiguration hd) hx

@[simp] theorem configurationStaircaseSimplex_selected_barycenter {d n : ℕ}
    (hd : 0 < d) :
    configurationStaircaseSimplex (Equiv.refl (Fin (n*d))) (staircaseBarycenter (n*d)) =
      (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n)) :=
  configurationCubeCollapse_selected hd

/-- Every other actual collapsed staircase simplex avoids the selected finite point. -/
theorem configurationStaircaseSimplex_avoids_selected {d n : ℕ} (hd : 0 < d)
    (π : Equiv.Perm (Fin (n*d))) (hπ : π ≠ Equiv.refl _) (x : Simplex (n*d)) :
    configurationStaircaseSimplex π x ≠
      (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n)) := by
  intro hx
  exact hπ (staircaseUnitCubeSimplex_selected_eq_perm π x
    (configurationCubeCollapse_selected_fiber hd _ hx))

/-! Explicit inverse barycentric coordinates for the closed identity chamber. -/

private theorem staircase_sum_differences {m : ℕ} (f : Fin (m+2) → ℝ) :
    (∑ k : Fin (m+1), (f k.castSucc - f k.succ)) =
      f 0 - f (Fin.last (m+1)) := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_castSucc f
  have h₂ := Fin.sum_univ_succ f
  linarith

private theorem staircase_tail_sum_differences {m : ℕ}
    (f : Fin (m+2) → ℝ) (a : Fin m) :
    (∑ k : Fin (m+1), if a.val < k.val then f k.castSucc - f k.succ else 0) =
      f a.succ.castSucc - f (Fin.last (m+1)) := by
  classical
  let g : Fin (m+2) → ℝ := fun k =>
    if k.val ≤ a.val then f a.succ.castSucc else f k
  have hg (k : Fin (m+1)) :
      (if a.val < k.val then f k.castSucc - f k.succ else 0) =
        g k.castSucc - g k.succ := by
    change (if a.val < k.val then f k.castSucc - f k.succ else 0) =
      (if k.val ≤ a.val then f a.succ.castSucc else f k.castSucc) -
        (if k.val+1 ≤ a.val then f a.succ.castSucc else f k.succ)
    by_cases h : a.val < k.val
    · have h₁ : ¬ k.val ≤ a.val := by omega
      have h₂ : ¬ k.val+1 ≤ a.val := by omega
      simp only [if_pos h, if_neg h₁, if_neg h₂]
    · have h₁ : k.val ≤ a.val := by omega
      by_cases h₂ : k.val+1 ≤ a.val
      · simp only [if_neg h, if_pos h₁, if_pos h₂, sub_self]
      · have he : k.succ = a.succ.castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.coe_castSucc]
          omega
        simp only [if_neg h, if_pos h₁, if_neg h₂, he, sub_self]
  simp_rw [hg]
  rw [staircase_sum_differences]
  have ha : ¬ m+1 ≤ a.val := by omega
  simp only [g, Fin.val_zero, Fin.val_last, Nat.zero_le, if_true, if_neg ha]

def staircaseClosedChamber (m : ℕ) : Set (Fin m → Set.Icc (0 : ℝ) 1) :=
  {y | Antitone (fun a => (y a).val)}

/-- Extend cube coordinates by the endpoint values 1 and 0. Consecutive
differences are precisely the inverse barycentric coordinates. -/
def staircaseExtendedCoordinate {m : ℕ} (y : Fin m → Set.Icc (0 : ℝ) 1)
    (k : Fin (m+2)) : ℝ :=
  if h₀ : k.val = 0 then 1 else
    if h : k.val ≤ m then (y ⟨k.val-1, by omega⟩).val else 0

@[simp] theorem staircaseExtendedCoordinate_zero {m : ℕ}
    (y : Fin m → Set.Icc (0 : ℝ) 1) : staircaseExtendedCoordinate y 0 = 1 := by
  simp [staircaseExtendedCoordinate]

@[simp] theorem staircaseExtendedCoordinate_last {m : ℕ}
    (y : Fin m → Set.Icc (0 : ℝ) 1) :
    staircaseExtendedCoordinate y (Fin.last (m+1)) = 0 := by
  simp [staircaseExtendedCoordinate]

@[simp] theorem staircaseExtendedCoordinate_succ {m : ℕ}
    (y : Fin m → Set.Icc (0 : ℝ) 1) (a : Fin m) :
    staircaseExtendedCoordinate y a.castSucc.succ = (y a).val := by
  have ha : a.val+1 ≤ m := by omega
  simp [staircaseExtendedCoordinate, ha]

theorem staircaseExtendedCoordinate_step {m : ℕ} (y : staircaseClosedChamber m)
    (k : Fin (m+1)) :
    staircaseExtendedCoordinate y.val k.succ ≤
      staircaseExtendedCoordinate y.val k.castSucc := by
  have hk : k.val ≤ m := Nat.le_of_lt_succ k.isLt
  by_cases h₀ : k.val = 0
  · by_cases h : k.val+1 ≤ m
    · have h' : 1 ≤ m := by omega
      simpa [staircaseExtendedCoordinate, h₀, h'] using
        (y.val ⟨k.val, by omega⟩).property.2
    · have hm : m = 0 := by omega
      simp [staircaseExtendedCoordinate, h₀, hm]
  · by_cases h : k.val+1 ≤ m
    · have hlt : k.val < m := by omega
      have hle : (⟨k.val-1, by omega⟩ : Fin m) ≤ ⟨k.val,hlt⟩ := by
        change k.val-1 ≤ k.val
        omega
      simpa [staircaseExtendedCoordinate, h₀, h, hk] using y.property hle
    · simpa [staircaseExtendedCoordinate, h₀, h, hk] using
        (y.val ⟨k.val-1, by omega⟩).property.1

def staircaseCubeInverse {m : ℕ} (y : staircaseClosedChamber m) : Simplex m :=
  ⟨fun k => ⟨staircaseExtendedCoordinate y.val k.castSucc -
    staircaseExtendedCoordinate y.val k.succ,
    sub_nonneg.mpr (staircaseExtendedCoordinate_step y k)⟩, by
      apply NNReal.eq
      simp only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one]
      change (∑ k : Fin (m+1),
        (staircaseExtendedCoordinate y.val k.castSucc -
          staircaseExtendedCoordinate y.val k.succ)) = 1
      rw [staircase_sum_differences]
      simp⟩

@[simp] theorem staircaseUnitCubeSimplex_inverse {m : ℕ}
    (y : staircaseClosedChamber m) :
    staircaseUnitCubeSimplex (Equiv.refl _) (staircaseCubeInverse y) = y.val := by
  funext a
  apply Subtype.ext
  change (∑ k : Fin (m+1), if a.val < k.val then
    staircaseExtendedCoordinate y.val k.castSucc -
      staircaseExtendedCoordinate y.val k.succ else 0) = (y.val a).val
  rw [staircase_tail_sum_differences]
  simp

theorem staircaseExtendedCoordinate_simplex {m : ℕ} (x : Simplex m)
    (k : Fin (m+2)) :
    staircaseExtendedCoordinate (staircaseUnitCubeSimplex (Equiv.refl _) x) k =
      ∑ j : Fin (m+1), if k.val ≤ j.val then (x j : ℝ) else 0 := by
  classical
  by_cases h₀ : k.val = 0
  · simp only [staircaseExtendedCoordinate, h₀, dite_true, Nat.zero_le, if_true]
    exact_mod_cast x.property.symm
  · by_cases h : k.val ≤ m
    · simp only [staircaseExtendedCoordinate, dif_neg h₀, dif_pos h]
      change (∑ j : Fin (m+1), if k.val-1 < j.val then (x j : ℝ) else 0) = _
      apply Finset.sum_congr rfl
      intro j hj
      have he : k.val-1 < j.val ↔ k.val ≤ j.val := by omega
      simp only [he]
    · simp only [staircaseExtendedCoordinate, dif_neg h₀, dif_neg h]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have he : ¬ k.val ≤ j.val := by have := j.isLt; omega
      simp [he]

theorem staircaseCubeInverse_simplex {m : ℕ} (x : Simplex m) :
    staircaseCubeInverse
      ⟨staircaseUnitCubeSimplex (Equiv.refl _) x,
        fun _ _ hab => staircaseCoordinate_antitone (Equiv.refl _) x hab⟩ = x := by
  classical
  apply Subtype.ext
  funext k
  apply NNReal.eq
  change staircaseExtendedCoordinate (staircaseUnitCubeSimplex (Equiv.refl _) x) k.castSucc -
    staircaseExtendedCoordinate (staircaseUnitCubeSimplex (Equiv.refl _) x) k.succ = (x k : ℝ)
  rw [staircaseExtendedCoordinate_simplex, staircaseExtendedCoordinate_simplex,
    ← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin (m+1), ((if k.castSucc.val ≤ j.val then (x j : ℝ) else 0) -
        (if k.succ.val ≤ j.val then (x j : ℝ) else 0))) =
        ((if k.castSucc.val ≤ k.val then (x k : ℝ) else 0) -
          (if k.succ.val ≤ k.val then (x k : ℝ) else 0)) := by
      apply Finset.sum_eq_single k
      · intro j hj hjk
        have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        by_cases h : k.val ≤ j.val
        · have h' : k.val+1 ≤ j.val := by omega
          simp [h, h']
        · have h' : ¬ k.val+1 ≤ j.val := by omega
          simp [h, h']
      · simp
    _ = (x k : ℝ) := by simp

/-- A genuine homeomorphism from the entire simplex onto its closed cube chamber. -/
def staircaseChamberHomeomorph (m : ℕ) : Simplex m ≃ₜ staircaseClosedChamber m :=
  Continuous.homeoOfEquivCompactToT2 (f := {
    toFun := fun x => ⟨staircaseUnitCubeSimplex (Equiv.refl _) x,
      fun _ _ hab => staircaseCoordinate_antitone (Equiv.refl _) x hab⟩
    invFun := staircaseCubeInverse
    left_inv := staircaseCubeInverse_simplex
    right_inv := fun y => Subtype.ext (staircaseUnitCubeSimplex_inverse y) })
    ((staircaseUnitCubeSimplex (Equiv.refl _)).continuous.subtype_mk _)

end NRR.PrimePowerTopology
