/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from Submission/Homology/PairHomotopy.lean in
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
Generalized to arbitrary ring coefficients in `ModuleCat R`.
-/
import NRR.SingularHomologyRelMap
import Mathlib.Algebra.Homology.Homotopy

/-! Degreewise descent of an actual compatible chain homotopy to the
relative cokernel complexes. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology

namespace NRR.SingularHomology

variable (R : Type) [Ring R]

section Descent

variable {A X B Y : ChainComplex (ModuleCat R) ℕ}

def cokDesc (i : A ⟶ X) (n : ℕ) {T : ModuleCat R}
    (u : X.X n ⟶ T) (hu : i.f n ≫ u = 0) : (cokernel i).X n ⟶ T :=
  Cofork.IsColimit.desc (isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) i) u
    (by simp only [Limits.zero_comp]; exact hu)

@[reassoc (attr := simp)]
theorem π_cokDesc (i : A ⟶ X) (n : ℕ) {T : ModuleCat R}
    (u : X.X n ⟶ T) (hu : i.f n ≫ u = 0) :
    (cokernel.π i).f n ≫ cokDesc R i n u hu = u :=
  Cofork.IsColimit.π_desc (isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) i)

@[reassoc (attr := simp)]
theorem π_cokernel_map_f (i : A ⟶ X) (j : B ⟶ Y) (fA : A ⟶ B) (f : X ⟶ Y)
    (w : i ≫ f = fA ≫ j) (n : ℕ) :
    (cokernel.π i).f n ≫ (cokernel.map i j fA f w).f n =
      f.f n ≫ (cokernel.π j).f n := by
  rw [← HomologicalComplex.comp_f,cokernel.map,cokernel.π_desc,HomologicalComplex.comp_f]

/-- Descend a chain homotopy whose operators carry the subcomplex into
the subcomplex. The operators on the quotient are constructed degreewise. -/
def descHomotopy (i : A ⟶ X) (j : B ⟶ Y) {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j) (H : Homotopy f g)
    (hH : ∀ p q,i.f p ≫ H.hom p q ≫ (cokernel.π j).f q = 0) :
    Homotopy (cokernel.map i j fA f wf) (cokernel.map i j gA g wg) where
  hom p q := cokDesc R i p (H.hom p q ≫ (cokernel.π j).f q)
    (by rw [← Category.assoc]; exact hH p q)
  zero p q hpq := by
    have hepi : Epi ((cokernel.π i).f p) := inferInstance
    apply hepi.left_cancellation
    simp [H.zero p q hpq]
  comm n := by
    have hepi : Epi ((cokernel.π i).f n) := inferInstance
    apply hepi.left_cancellation
    have hd : ∀ p q,(cokernel.π i).f p ≫ (cokernel i).d p q =
        X.d p q ≫ (cokernel.π i).f q := fun p q => (cokernel.π i).comm p q
    have hd' : ∀ p q,(cokernel.π j).f p ≫ (cokernel j).d p q =
        Y.d p q ≫ (cokernel.π j).f q := fun p q => (cokernel.π j).comm p q
    have e3 : (cokernel.π i).f n ≫ (dNext n) (fun p q => cokDesc R i p
        (H.hom p q ≫ (cokernel.π j).f q) (by rw [← Category.assoc]; exact hH p q)) =
        (dNext n) H.hom ≫ (cokernel.π j).f n := by
      simp only [dNext,AddMonoidHom.mk'_apply]
      rw [← Category.assoc,hd,Category.assoc,π_cokDesc,← Category.assoc]
    have e4 : (cokernel.π i).f n ≫ (prevD n) (fun p q => cokDesc R i p
        (H.hom p q ≫ (cokernel.π j).f q) (by rw [← Category.assoc]; exact hH p q)) =
        (prevD n) H.hom ≫ (cokernel.π j).f n := by
      simp only [prevD,AddMonoidHom.mk'_apply]
      rw [← Category.assoc,π_cokDesc,Category.assoc,hd',← Category.assoc]
    rw [Preadditive.comp_add,Preadditive.comp_add,e3,e4,π_cokernel_map_f,π_cokernel_map_f,
      ← Preadditive.add_comp,← Preadditive.add_comp,← H.comm n]

theorem homologyMap_cokernel_eq_of_compatible_homotopy
    (i : A ⟶ X) (j : B ⟶ Y) {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j) (H : Homotopy f g)
    (hH : ∀ p q,i.f p ≫ H.hom p q ≫ (cokernel.π j).f q = 0) (n : ℕ) :
    HomologicalComplex.homologyMap (cokernel.map i j fA f wf) n =
      HomologicalComplex.homologyMap (cokernel.map i j gA g wg) n :=
  (descHomotopy R i j wf wg H hH).homologyMap_eq n

end Descent
end NRR.SingularHomology
