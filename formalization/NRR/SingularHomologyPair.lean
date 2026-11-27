/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from Submission/Homology/Pair.lean in
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
The coefficient category is generalized from abelian groups to `ModuleCat R`.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Actual relative singular chains and the long exact sequence of a pair,
with arbitrary ring coefficients, in particular `ZMod p`. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

namespace NRR.SingularHomology

variable (R : Type) [Ring R]

abbrev Csing (X : TopCat.{0}) : ChainComplex (ModuleCat R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X

abbrev CsingFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat R) ℕ :=
  (singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)

def CsingMap {X Y : TopCat.{0}} (f : X ⟶ Y) : Csing R X ⟶ Csing R Y :=
  (CsingFunctor R).map f

@[simp] theorem CsingMap_id (X : TopCat.{0}) : CsingMap R (𝟙 X) = 𝟙 (Csing R X) :=
  (CsingFunctor R).map_id X

@[simp] theorem CsingMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CsingMap R (f ≫ g) = CsingMap R f ≫ CsingMap R g :=
  (CsingFunctor R).map_comp f g

abbrev Habs (n : ℕ) (X : TopCat.{0}) : ModuleCat R :=
  (Csing R X).homology n

abbrev HabsMap (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) : Habs R n X ⟶ Habs R n Y :=
  HomologicalComplex.homologyMap (CsingMap R f) n

@[simp] theorem HabsMap_id (n : ℕ) (X : TopCat.{0}) : HabsMap R n (𝟙 X) = 𝟙 _ := by
  simp [HabsMap]

@[simp] theorem HabsMap_comp (n : ℕ) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HabsMap R n (f ≫ g) = HabsMap R n f ≫ HabsMap R n g := by
  simp only [HabsMap,CsingMap_comp,HomologicalComplex.homologyMap_comp]

instance mono_CsingMap {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Mono (CsingMap R i) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of R R)).map ((TopCat.toSSet.map i).app (Opposite.op ⦋n⦌)))
  letI : Mono ((TopCat.toSSet.map i).app (Opposite.op ⦋n⦌)) := by
    rw [CategoryTheory.mono_iff_injective]
    intro s t he
    apply (TopCat.toSSetObjEquiv A _).injective
    ext x
    have h := congrArg (fun z => TopCat.toSSetObjEquiv X _ z x) he
    exact ((TopCat.mono_iff_injective i).mp inferInstance) h
  infer_instance

def relComplex {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : ChainComplex (ModuleCat R) ℕ :=
  cokernel (CsingMap R i)

def Hrel (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : ModuleCat R :=
  (relComplex R i).homology n

def relProj {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Csing R X ⟶ relComplex R i :=
  cokernel.π (CsingMap R i)

def relShortComplex {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (CsingMap R i) (cokernel.π (CsingMap R i)) (by simp)

theorem relShortComplex_shortExact {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (relShortComplex R i).ShortExact where
  exact := ShortComplex.exact_cokernel (CsingMap R i)
  mono_f := mono_CsingMap R i
  epi_g := coequalizer.π_epi

theorem relShortComplex_degreewise_shortExact {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) :
    ((relShortComplex R i).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (relShortComplex_shortExact R i) n

def relδ (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    Hrel R (n+1) i ⟶ Habs R n A :=
  (relShortComplex_shortExact R i).δ (n+1) n rfl

abbrev relIota (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    Habs R n A ⟶ Habs R n X := HabsMap R n i

def relJ (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Habs R n X ⟶ Hrel R n i :=
  HomologicalComplex.homologyMap (relProj R i) n

def pairLES (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    ComposableArrows (ModuleCat R) 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (relShortComplex_shortExact R i) (n+1) n rfl

theorem pairLES_exact (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (pairLES R n i).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact _ _ _ _

theorem pair_exact_δ_iota (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (ShortComplex.mk (relδ R n i) (relIota R n i)
      ((relShortComplex_shortExact R i).δ_comp _ _ _)).Exact :=
  (relShortComplex_shortExact R i).homology_exact₁ (n+1) n rfl

theorem pair_exact_iota_j (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relShortComplex R i).f n)
      (HomologicalComplex.homologyMap (relShortComplex R i).g n)
      (by simp [← HomologicalComplex.homologyMap_comp])).Exact :=
  (relShortComplex_shortExact R i).homology_exact₂ n

theorem pair_exact_j_δ (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (ShortComplex.mk (relJ R (n+1) i) (relδ R n i)
      ((relShortComplex_shortExact R i).comp_δ _ _ _)).Exact :=
  (relShortComplex_shortExact R i).homology_exact₃ (n+1) n rfl

def subIncl {Y : TopCat.{0}} (A : Set Y) : TopCat.of A ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

instance mono_subIncl {Y : TopCat.{0}} (A : Set Y) : Mono (subIncl A) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

abbrev HrelSet (n : ℕ) {Y : TopCat.{0}} (A : Set Y) : ModuleCat R := Hrel R n (subIncl A)

end NRR.SingularHomology
