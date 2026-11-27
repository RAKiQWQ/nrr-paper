import NRR.SingularHomologyFiniteCellGluing
import NRR.PrimePowerTopologyCompactification

/-! Singular relative homology of genuine finite cell attachments.
The comparison uses the proved good-pair theorem on the canonical
closed-subset collapse, never an assumed quotient-homology principle. -/

noncomputable section
set_option maxHeartbeats 250000
open Set Topology Metric CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePowerTopology

namespace NRR.SingularHomology

section ClosedSubset
variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

def closedSubsetCollapse (A : Set X) (hA : IsClosed A) (hne : A.Nonempty) :
    ClosedCollapse A (∞ : OnePoint (Aᶜ : Set X)) := by
  classical
  letI : LocallyCompactSpace (Aᶜ : Set X) := hA.isOpen_compl.locallyCompactSpace
  let q : C(X,OnePoint (Aᶜ : Set X)) :=
    ⟨openCollapse Aᶜ,continuous_openCollapse Aᶜ hA.isOpen_compl⟩
  have hp (x : X) : q x = ∞ ↔ x ∈ A := by
    by_cases hx : x ∈ A <;> simp [q,openCollapse,hx]
  have hsurj : Function.Surjective q := by
    intro y
    induction y using OnePoint.rec with
    | infty =>
        obtain ⟨a,ha⟩ := hne
        exact ⟨a,(hp a).mpr ha⟩
    | coe y =>
        refine ⟨y.val,?_⟩
        exact openCollapse_of_mem Aᶜ y.property
  refine ⟨q,q.continuous.isClosedMap.isQuotientMap q.continuous hsurj,?_,hp⟩
  intro x y
  constructor
  · intro hxy
    by_cases hx : x ∈ A
    · exact Or.inr ⟨hx,(hp y).mp (hxy.symm.trans ((hp x).mpr hx))⟩
    · have hy : y ∉ A := by
        intro hy
        exact hx ((hp x).mp (hxy.trans ((hp y).mpr hy)))
      left
      have he : (⟨x,hx⟩ : (Aᶜ : Set X)) = ⟨y,hy⟩ := by
        apply Option.some.inj
        simpa only [q,ContinuousMap.coe_mk,openCollapse_of_mem Aᶜ (show x ∈ Aᶜ from hx),
          openCollapse_of_mem Aᶜ (show y ∈ Aᶜ from hy)] using hxy
      exact congrArg Subtype.val he
  · rintro (rfl | ⟨hx,hy⟩)
    · rfl
    · exact ((hp x).mpr hx).trans ((hp y).mpr hy).symm

@[simp] theorem closedSubsetCollapse_map (A : Set X) (hA : IsClosed A)
    (hne : A.Nonempty) (x : X) :
    (closedSubsetCollapse A hA hne).map x = openCollapse Aᶜ x := rfl

end ClosedSubset

namespace FiniteCellAttachment
variable {ι V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Finite ι] {A : Set X} [CompactSpace A]
  (P : FiniteCellAttachment ι V X A)

def collapse (_P : FiniteCellAttachment ι V X A) (hne : A.Nonempty) :
    ClosedCollapse A (∞ : OnePoint (Aᶜ : Set X)) :=
  closedSubsetCollapse A (isCompact_iff_compactSpace.mpr inferInstance).isClosed hne

def relativeCollapseMap (R : Type) [Ring R] (hne : A.Nonempty) (n : ℕ) :
    Hrel R n (subIncl (Y := TopCat.of X) A) ⟶
      Hrel R n (homologyPointIncl (X := TopCat.of (OnePoint (Aᶜ : Set X))) ∞) :=
  HrelMap R n (subIncl (Y := TopCat.of X) A)
    (homologyPointIncl (X := TopCat.of (OnePoint (Aᶜ : Set X))) ∞)
    (show subIncl A ≫ TopCat.ofHom (P.collapse hne).map =
    homologyPointCollapse (TopCat.of A) ≫ homologyPointIncl ∞ by
      ext a
      exact ((P.collapse hne).pointFiber a.val).mpr a.property)

theorem isIso_relativeCollapseMap (R : Type) [Ring R] (hne : A.Nonempty) (n : ℕ) :
    IsIso (P.relativeCollapseMap R hne n) := by
  letI : LocallyCompactSpace (Aᶜ : Set X) :=
    ((isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace A)).isClosed.isOpen_compl).locallyCompactSpace
  exact (P.collapse hne).isIso_relativeMap_of_openNeighborhood
    P.neighborhood P.isOpen_neighborhood P.neighborhoodDeformation R n

def relativeCollapseIso (R : Type) [Ring R] (hne : A.Nonempty) (n : ℕ) :
    Hrel R n (subIncl (Y := TopCat.of X) A) ≅
      Hrel R n (homologyPointIncl (X := TopCat.of (OnePoint (Aᶜ : Set X))) ∞) := by
  letI := P.isIso_relativeCollapseMap R hne n
  exact asIso (P.relativeCollapseMap R hne n)

def relativeCollapsePositiveIso (R : Type) [Ring R] (hne : A.Nonempty) (n : ℕ) :
    Hrel R (n+1) (subIncl (Y := TopCat.of X) A) ≅
      Habs R (n+1) (TopCat.of (OnePoint (Aᶜ : Set X))) :=
  P.relativeCollapseIso R hne (n+1) ≪≫
    (pointRelativePositiveIso R n (X := TopCat.of (OnePoint (Aᶜ : Set X))) ∞).symm

end FiniteCellAttachment
end NRR.SingularHomology
