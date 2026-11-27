/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The additive biproduct and exact-sequence arguments are adapted from
Submission/Homology/MayerVietorisLES.lean and MayerVietorisIso.lean in
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
They are generalized to arbitrary ring coefficients and separated from the
still independent small-chain comparison with all singular chains.
-/
import NRR.SingularHomologySmallChains
import NRR.PrimePowerTopologyHomologyZeroConnected

/-! The genuine long exact sequence of the small singular-chain cover,
over an arbitrary ring. No unproved excision statement is used here. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

namespace NRR.SingularHomology

section Biprod
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (Y Z : C) [HasBinaryBiproduct Y Z]
    [HasBinaryBiproduct (F.obj Y) (F.obj Z)]

def additiveBiprodIso : F.obj (Y ⊞ Z) ≅ F.obj Y ⊞ F.obj Z where
  hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp,
      ← F.map_add, biprod.total, F.map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      refine biprod.hom_ext _ _ ?_ ?_ <;> simp [← F.map_comp]

@[reassoc]
theorem map_lift_additiveBiprodIso {W : C} (f : W ⟶ Y) (g : W ⟶ Z) :
    F.map (biprod.lift f g) ≫ (additiveBiprodIso F Y Z).hom =
      biprod.lift (F.map f) (F.map g) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp [additiveBiprodIso, ← F.map_comp]

end Biprod

variable (R : Type) [Ring R]
variable {X : TopCat.{0}} (A B : Set X)

abbrev mvSum (n : ℕ) : ModuleCat R :=
  Habs R n (TopCat.of A) ⊞ Habs R n (TopCat.of B)

def mvSumIso (n : ℕ) : (mvSC (R := R) A B).X₂.homology n ≅ mvSum R A B n :=
  additiveBiprodIso
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n)
    (Csing R (TopCat.of A)) (Csing R (TopCat.of B))

def mvIota (n : ℕ) : Habs R n (TopCat.of (A ∩ B : Set X)) ⟶ mvSum R A B n :=
  biprod.lift (HabsMap R n (mvInclLeft A B)) (HabsMap R n (mvInclRight A B))

theorem homologyMap_mvSC_f (n : ℕ) :
    HomologicalComplex.homologyMap (mvSC (R := R) A B).f n ≫ (mvSumIso R A B n).hom =
      mvIota R A B n :=
  map_lift_additiveBiprodIso
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n)
    (Csing R (TopCat.of A)) (Csing R (TopCat.of B))
    (CsingMap R (mvInclLeft A B)) (CsingMap R (mvInclRight A B))

def mvSmallKappa (n : ℕ) : mvSum R A B n ⟶ (mvSmallComplex (R := R) A B).homology n :=
  (mvSumIso R A B n).inv ≫ HomologicalComplex.homologyMap (mvSC (R := R) A B).g n

def mvSmallDelta (n : ℕ) :
    (mvSmallComplex (R := R) A B).homology (n+1) ⟶
      Habs R n (TopCat.of (A ∩ B : Set X)) :=
  (mvSC_shortExact (R := R) A B).δ (n+1) n rfl

theorem mvSmallDelta_comp_mvIota (n : ℕ) :
    mvSmallDelta R A B n ≫ mvIota R A B n = 0 := by
  rw [← homologyMap_mvSC_f]
  unfold mvSmallDelta
  simp

theorem mvSmallKappa_comp_mvSmallDelta (n : ℕ) :
    mvSmallKappa R A B (n+1) ≫ mvSmallDelta R A B n = 0 := by
  unfold mvSmallKappa mvSmallDelta
  simp

theorem mvSmall_exact_delta_iota (n : ℕ) :
    (ShortComplex.mk (mvSmallDelta R A B n) (mvIota R A B n)
      (mvSmallDelta_comp_mvIota R A B n)).Exact := by
  have hex := (mvSC_shortExact (R := R) A B).homology_exact₁ (n+1) n rfl
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (mvSumIso R A B n) ?_ ?_
  · simp [mvSmallDelta]
  · exact (Category.id_comp _).trans (homologyMap_mvSC_f R A B n).symm

theorem mvSmall_exact_kappa_delta (n : ℕ) :
    (ShortComplex.mk (mvSmallKappa R A B (n+1)) (mvSmallDelta R A B n)
      (mvSmallKappa_comp_mvSmallDelta R A B n)).Exact := by
  have hex := (mvSC_shortExact (R := R) A B).homology_exact₃ (n+1) n rfl
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (mvSumIso R A B (n+1)) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [mvSmallKappa]
  · simp [mvSmallDelta]

private theorem isZero_biprod_of_isZero {C : Type*} [Category C] [Preadditive C]
    {Y Z : C} [HasBinaryBiproduct Y Z] (hY : IsZero Y) (hZ : IsZero Z) :
    IsZero (Y ⊞ Z) := by
  refine (IsZero.iff_id_eq_zero _).mpr (biprod.hom_ext' _ _ ?_ ?_)
  · rw [Category.comp_id, comp_zero]
    exact hY.eq_zero_of_src _
  · rw [Category.comp_id, comp_zero]
    exact hZ.eq_zero_of_src _

theorem isZero_mvSum (n : ℕ)
    (hA : IsZero (Habs R n (TopCat.of A))) (hB : IsZero (Habs R n (TopCat.of B))) :
    IsZero (mvSum R A B n) :=
  isZero_biprod_of_isZero hA hB

theorem isIso_mvSmallDelta (n : ℕ)
    (hA1 : IsZero (Habs R (n+1) (TopCat.of A)))
    (hB1 : IsZero (Habs R (n+1) (TopCat.of B)))
    (hA0 : IsZero (Habs R n (TopCat.of A)))
    (hB0 : IsZero (Habs R n (TopCat.of B))) :
    IsIso (mvSmallDelta R A B n) := by
  have hk : mvSmallKappa R A B (n+1) = 0 :=
    (isZero_mvSum R A B (n+1) hA1 hB1).eq_zero_of_src _
  have hi : mvIota R A B n = 0 := (isZero_mvSum R A B n hA0 hB0).eq_zero_of_tgt _
  letI : Mono (mvSmallDelta R A B n) := (mvSmall_exact_kappa_delta R A B n).mono_g hk
  letI : Epi (mvSmallDelta R A B n) := (mvSmall_exact_delta_iota R A B n).epi_f hi
  exact isIso_of_mono_of_epi _

def mvSmallDeltaIso_of_contractible (n : ℕ) [ContractibleSpace A] [ContractibleSpace B] :
    (mvSmallComplex (R := R) A B).homology (n+2) ≅
      Habs R (n+1) (TopCat.of (A ∩ B : Set X)) := by
  letI := isIso_mvSmallDelta R A B (n+1)
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1+1) (by omega) (TopCat.of A))
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1+1) (by omega) (TopCat.of B))
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega) (TopCat.of A))
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega) (TopCat.of B))
  exact asIso (mvSmallDelta R A B (n+1))

end NRR.SingularHomology
