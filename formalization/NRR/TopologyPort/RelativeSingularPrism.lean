/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The relative descent follows Submission/Homology/PairHomotopy.lean from
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
The actual prism is constructed locally against mathlib 4.24.0 and the
coefficients are generalized to modules over any ring.
-/
import NRR.TopologyPort.SingularPrism
import NRR.SingularHomologyRelHomotopy

/-! Continuous homotopies of actual pairs induce homotopies of the actual
relative singular chain maps, and hence equal maps on relative homology. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology

namespace NRR.SingularHomology

variable (R : Type) [Ring R]
variable {A X B Y : TopCat.{0}}

/-- A pair homotopy is specified by the continuous ambient and subspace
homotopies with their pointwise compatibility at every time. -/
structure ContinuousPairHomotopy (i : A ⟶ X) (j : B ⟶ Y)
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (_wf : i ≫ f = fA ≫ j) (_wg : i ≫ g = gA ≫ j) where
  sub : fA.hom.Homotopy gA.hom
  amb : f.hom.Homotopy g.hom
  compat : ∀ t a,amb (t,i.hom a) = j.hom (sub (t,a))

def relativeSingularChainHomotopy (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j)
    (P : ContinuousPairHomotopy i j wf wg) :
    Homotopy (relComplexMap R i j wf) (relComplexMap R i j wg) := by
  have w₀ : CsingMap R i ≫ CsingMap R f = CsingMap R fA ≫ CsingMap R j := by
    rw [← CsingMap_comp,← CsingMap_comp,wf]
  have w₁ : CsingMap R i ≫ CsingMap R g = CsingMap R gA ≫ CsingMap R j := by
    rw [← CsingMap_comp,← CsingMap_comp,wg]
  let H : Homotopy (CsingMap R f) (CsingMap R g) :=
    NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.amb
  have compatible : ∀ p q,(CsingMap R i).f p ≫ H.hom p q ≫
      (cokernel.π (CsingMap R j)).f q = 0 := by
    intro p q
    have hn := NRR.TopologyPort.singularChainHomotopy_pair_naturality
      (ModuleCat.of R R) i j P.sub P.amb P.compat p q
    change (CsingMap R i).f p ≫ H.hom p q =
      (NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.sub).hom p q ≫
        (CsingMap R j).f q at hn
    rw [← Category.assoc,hn,Category.assoc,← HomologicalComplex.comp_f,
      cokernel.condition,HomologicalComplex.zero_f,comp_zero]
  exact descHomotopy R (CsingMap R i) (CsingMap R j) w₀ w₁ H compatible

theorem HrelMap_eq_of_continuousPairHomotopy (i : A ⟶ X) [Mono i]
    (j : B ⟶ Y) [Mono j] {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j)
    (P : ContinuousPairHomotopy i j wf wg) (k : ℕ) :
    HrelMap R k i j wf = HrelMap R k i j wg :=
  (relativeSingularChainHomotopy R i j wf wg P).homologyMap_eq k

end NRR.SingularHomology
