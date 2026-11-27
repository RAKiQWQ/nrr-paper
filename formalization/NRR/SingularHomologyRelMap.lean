/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from Submission/Homology/PairHomotopy.lean and RelMap.lean in
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
Generalized to arbitrary ring coefficients in `ModuleCat R`.
-/
import NRR.SingularHomologyPair

/-! Actual relative chain and homology maps of pairs, with the natural long
exact sequence. No homotopy or configuration-space conclusion is assumed. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology

namespace NRR.SingularHomology

variable (R : Type) [Ring R] {A X B Y : TopCat.{0}}

def relComplexMap (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relComplex R i ⟶ relComplex R j :=
  cokernel.map _ _ (CsingMap R fA) (CsingMap R f)
    (by rw [← CsingMap_comp,← CsingMap_comp,w])

def HrelMap (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    Hrel R n i ⟶ Hrel R n j :=
  HomologicalComplex.homologyMap (relComplexMap R i j w) n

@[reassoc (attr := simp)]
theorem relProj_comp_relComplexMap (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relProj R i ≫ relComplexMap R i j w = CsingMap R f ≫ relProj R j :=
  cokernel.π_desc _ _ _

@[simp] theorem relComplexMap_id (i : A ⟶ X) [Mono i] :
    relComplexMap R i i (show i ≫ 𝟙 X = 𝟙 A ≫ i by simp) = 𝟙 _ := by
  have hepi : Epi (relProj R i) := coequalizer.π_epi
  apply hepi.left_cancellation
  simp only [relProj_comp_relComplexMap,CsingMap_id,Category.id_comp,Category.comp_id]

@[simp] theorem HrelMap_id (n : ℕ) (i : A ⟶ X) [Mono i] :
    HrelMap R n i i (show i ≫ 𝟙 X = 𝟙 A ≫ i by simp) = 𝟙 _ := by
  rw [HrelMap,relComplexMap_id,HomologicalComplex.homologyMap_id]
  rfl

theorem relComplexMap_comp {C Z : TopCat.{0}}
    (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j] (k : C ⟶ Z) [Mono k]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    {gB : B ⟶ C} {g : Y ⟶ Z} (w' : j ≫ g = gB ≫ k) :
    relComplexMap R i j w ≫ relComplexMap R j k w' =
      relComplexMap R i k (show i ≫ f ≫ g = (fA ≫ gB) ≫ k by
        rw [← Category.assoc,w,Category.assoc,w',Category.assoc]) := by
  have hepi : Epi (relProj R i) := coequalizer.π_epi
  apply hepi.left_cancellation
  rw [relProj_comp_relComplexMap_assoc,relProj_comp_relComplexMap,relProj_comp_relComplexMap]
  rw [CsingMap_comp,Category.assoc]

theorem HrelMap_comp {C Z : TopCat.{0}} (n : ℕ)
    (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j] (k : C ⟶ Z) [Mono k]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    {gB : B ⟶ C} {g : Y ⟶ Z} (w' : j ≫ g = gB ≫ k) :
    HrelMap R n i j w ≫ HrelMap R n j k w' =
      HrelMap R n i k (show i ≫ f ≫ g = (fA ≫ gB) ≫ k by
        rw [← Category.assoc,w,Category.assoc,w',Category.assoc]) := by
  rw [HrelMap,HrelMap,HrelMap,← relComplexMap_comp R i j k w w',
    HomologicalComplex.homologyMap_comp]

def relShortComplexMap (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relShortComplex R i ⟶ relShortComplex R j where
  τ₁ := CsingMap R fA
  τ₂ := CsingMap R f
  τ₃ := relComplexMap R i j w
  comm₁₂ := by
    change CsingMap R fA ≫ CsingMap R j = CsingMap R i ≫ CsingMap R f
    rw [← CsingMap_comp,← CsingMap_comp,w]
  comm₂₃ := (relProj_comp_relComplexMap R i j w).symm

theorem relIota_naturality (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relIota R n i ≫ HabsMap R n f = HabsMap R n fA ≫ relIota R n j := by
  rw [← HabsMap_comp,← HabsMap_comp,w]

theorem relJ_naturality (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relJ R n i ≫ HrelMap R n i j w = HabsMap R n f ≫ relJ R n j := by
  change HomologicalComplex.homologyMap (relProj R i) n ≫
      HomologicalComplex.homologyMap (relComplexMap R i j w) n =
    HomologicalComplex.homologyMap (CsingMap R f) n ≫
      HomologicalComplex.homologyMap (relProj R j) n
  rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
    relProj_comp_relComplexMap]

theorem relδ_naturality (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relδ R n i ≫ HabsMap R n fA = HrelMap R (n+1) i j w ≫ relδ R n j :=
  HomologicalComplex.HomologySequence.δ_naturality
    (relShortComplexMap R i j w) (relShortComplex_shortExact R i)
      (relShortComplex_shortExact R j) (n+1) n rfl

theorem isIso_HrelMap_of_isIso (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} [IsIso fA] [IsIso f] (w : i ≫ f = fA ≫ j) :
    IsIso (HrelMap R n i j w) := by
  letI : IsIso (CsingMap R fA) := by unfold CsingMap; infer_instance
  letI : IsIso (CsingMap R f) := by unfold CsingMap; infer_instance
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (relShortComplexMap R i j w) (relShortComplex_shortExact R i)
      (relShortComplex_shortExact R j)
  · change Epi (HomologicalComplex.homologyMap (CsingMap R fA) n)
    infer_instance
  · change IsIso (HomologicalComplex.homologyMap (CsingMap R f) n)
    infer_instance
  · intro k _
    change IsIso (HomologicalComplex.homologyMap (CsingMap R fA) k)
    infer_instance
  · intro k _
    change Mono (HomologicalComplex.homologyMap (CsingMap R f) k)
    infer_instance

end NRR.SingularHomology
