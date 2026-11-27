import NRR.PrimePowerTopologyTwistedHomotopy
import NRR.TopologyPort.RelativeSingularPrism

/-! Equivariant pair homotopies descend to twisted relative singular chains.
Both the pair quotient and the group coinvariants are the genuine cokernels.
The proof uses naturality of the explicit singular prism, with no averaging. -/

noncomputable section
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

/-- Projection of the actual relative prism is the ambient singular prism
followed by the target relative projection, degree by degree. -/
theorem relProj_relativeSingularChainHomotopy
    {A X B Y : TopCat.{0}} (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j)
    (P : ContinuousPairHomotopy i j wf wg) (p q : ℕ) :
    (relProj R i).f p ≫ (relativeSingularChainHomotopy R i j wf wg P).hom p q =
      (NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.amb).hom p q ≫
        (relProj R j).f q :=
by
  let H := NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.amb
  have compatible : (CsingMap R i).f p ≫ H.hom p q ≫ (cokernel.π (CsingMap R j)).f q = 0 := by
    have hn := NRR.TopologyPort.singularChainHomotopy_pair_naturality
      (ModuleCat.of R R) i j P.sub P.amb P.compat p q
    change (CsingMap R i).f p ≫ H.hom p q =
      (NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.sub).hom p q ≫
        (CsingMap R j).f q at hn
    rw [← Category.assoc,hn,Category.assoc,← HomologicalComplex.comp_f,
      cokernel.condition,HomologicalComplex.zero_f,comp_zero]
  exact π_cokDesc R (CsingMap R i) p _ compatible

section Equivariant
variable {G : Type} [Group G] (χ : G →* Rˣ)
variable {A X B Y : TopCat.{0}} (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
  (αA : G → (A ⟶ A)) (αX : G → (X ⟶ X))
  (βB : G → (B ⟶ B)) (βY : G → (Y ⟶ Y))
  (wi : ∀ a, i ≫ αX a = αA a ≫ i) (wj : ∀ a, j ≫ βY a = βB a ≫ j)

/-- Equivariance of an actual map of pairs implies equivariance after
forming the relative singular-chain cokernels. -/
theorem relativeSingularChainMap_equivariant
    {fA : A ⟶ B} {f : X ⟶ Y} (wf : i ≫ f = fA ≫ j)
    (he : ∀ a, αX a ≫ f = f ≫ βY a) (a : G) :
    relComplexMap R i i (wi a) ≫ relComplexMap R i j wf =
      relComplexMap R i j wf ≫ relComplexMap R j j (wj a) := by
  have hπ : Epi (relProj R i) := coequalizer.π_epi
  apply hπ.left_cancellation
  simp only [relProj_comp_relComplexMap_assoc,relProj_comp_relComplexMap]
  rw [← Category.assoc,← CsingMap_comp,he a,CsingMap_comp,Category.assoc]

/-- The relative prism is equivariant at every degree operator whenever
the ambient continuous homotopy is pointwise equivariant. -/
theorem relativeSingularChainHomotopy_equivariant
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j)
    (P : ContinuousPairHomotopy i j wf wg)
    (he : ∀ a t x, P.amb (t,(αX a).hom x) = (βY a).hom (P.amb (t,x)))
    (a : G) (p q : ℕ) :
    (relComplexMap R i i (wi a)).f p ≫
        (relativeSingularChainHomotopy R i j wf wg P).hom p q =
      (relativeSingularChainHomotopy R i j wf wg P).hom p q ≫
        (relComplexMap R j j (wj a)).f q := by
  have hπ : Epi ((relProj R i).f p) :=
    inferInstanceAs (Epi ((cokernel.π (CsingMap R i)).f p))
  apply hπ.left_cancellation
  have hi := congrArg (fun m => m.f p) (relProj_comp_relComplexMap R i i (wi a))
  have hj := congrArg (fun m => m.f q) (relProj_comp_relComplexMap R j j (wj a))
  simp only [HomologicalComplex.comp_f] at hi hj
  have hn := NRR.TopologyPort.singularChainHomotopy_pair_naturality
    (ModuleCat.of R R) (αX a) (βY a) P.amb P.amb (he a) p q
  change (CsingMap R (αX a)).f p ≫
      (NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.amb).hom p q =
    (NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) P.amb).hom p q ≫
      (CsingMap R (βY a)).f q at hn
  rw [← Category.assoc,hi,Category.assoc,relProj_relativeSingularChainHomotopy,
    ← Category.assoc,hn,
    Category.assoc,← hj,← Category.assoc,← relProj_relativeSingularChainHomotopy,
    Category.assoc]

/-- A continuous equivariant pair homotopy supplies a real chain homotopy
on the twisted relative complexes, in every coefficient characteristic. -/
def twistedRelativeSingularChainHomotopy
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j)
    (P : ContinuousPairHomotopy i j wf wg)
    (hef : ∀ a, αX a ≫ f = f ≫ βY a)
    (heg : ∀ a, αX a ≫ g = g ≫ βY a)
    (he : ∀ a t x, P.amb (t,(αX a).hom x) = (βY a).hom (P.amb (t,x))) :
    Homotopy
      (twistedChainMap R χ (relComplex R i)
        (fun a => relComplexMap R i i (wi a)) (fun a => relComplexMap R j j (wj a))
        (relComplexMap R i j wf)
        (relativeSingularChainMap_equivariant R i j αA αX βB βY wi wj wf hef))
      (twistedChainMap R χ (relComplex R i)
        (fun a => relComplexMap R i i (wi a)) (fun a => relComplexMap R j j (wj a))
        (relComplexMap R i j wg)
        (relativeSingularChainMap_equivariant R i j αA αX βB βY wi wj wg heg)) :=
  twistedChainHomotopy R χ _ _
    (relativeSingularChainMap_equivariant R i j αA αX βB βY wi wj wf hef)
    (relativeSingularChainMap_equivariant R i j αA αX βB βY wi wj wg heg)
    (relativeSingularChainHomotopy R i j wf wg P)
    (relativeSingularChainHomotopy_equivariant R i j αA αX βB βY wi wj wf wg P he)

end Equivariant
end NRR.PrimePowerTopology