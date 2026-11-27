import NRR.SingularHomologyBMSuspension

/-! A contractible-arc collapse route to real BM suspension.
The relative comparison is the proved good-neighborhood collapse theorem;
the absolute comparison below includes degree one. Thus an unreduced
suspension model can be used without constructing contractible reduced caps. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.PrimePowerTopology
open scoped OnePoint

namespace NRR.SingularHomology
variable (R : Type) [Ring R]

/-- A contractible subspace is split injective on zeroth homology, even
when the ambient space has other path components. -/
theorem mono_HabsMap_zero_of_contractible {A Z : TopCat.{0}}
    [ContractibleSpace A] (i : A ⟶ Z) : Mono (HabsMap R 0 i) := by
  letI : IsIso (HabsMap R 0 (homologyPointCollapse A)) :=
    (HabsZeroCollapseIso R A).isIso_hom
  exact mono_of_mono_fac (show HabsMap R 0 i ≫
      HabsMap R 0 (homologyPointCollapse Z) =
      HabsMap R 0 (homologyPointCollapse A) by
    rw [← HabsMap_comp, comp_homologyPointCollapse])

/-- Canonical absolute-to-relative comparison for a contractible subspace.
The proof uses split injectivity on H₀ for the first homology case. -/
def contractibleRelativePositiveIso {A Z : TopCat.{0}}
    [ContractibleSpace A] (i : A ⟶ Z) [Mono i] (q : ℕ) :
    Habs R (q+1) Z ≅ Hrel R (q+1) i := by
  have hi : relIota R (q+1) i = 0 :=
    (isZero_Habs_of_contractible R (q+1) (by omega) A).eq_zero_of_src _
  have hd : relδ R q i = 0 := by
    cases q with
    | zero =>
      letI := mono_HabsMap_zero_of_contractible R i
      exact (pair_exact_δ_iota R 0 i).mono_g_iff.mp inferInstance
    | succ q =>
      exact (isZero_Habs_of_contractible R (q+1) (by omega) A).eq_zero_of_tgt _
  letI : Mono (relJ R (q+1) i) := (pair_exact_iota_j R (q+1) i).mono_g hi
  letI : Epi (relJ R (q+1) i) := (pair_exact_j_δ R q i).epi_f hd
  letI : IsIso (relJ R (q+1) i) := isIso_of_mono_of_epi _
  exact asIso (relJ R (q+1) i)

@[simp] theorem contractibleRelativePositiveIso_hom {A Z : TopCat.{0}}
    [ContractibleSpace A] (i : A ⟶ Z) [Mono i] (q : ℕ) :
    (contractibleRelativePositiveIso R i q).hom = relJ R (q+1) i := rfl

namespace ClosedCollapse
variable {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y] [T1Space Y]
variable {A : Set Z} {p : Y} (P : ClosedCollapse A p)

/-- Collapsing a contractible subspace with an actual open deformation
neighborhood is an isomorphism on every positive singular homology group. -/
theorem isIso_positiveMap_of_openNeighborhood [ContractibleSpace A]
    (N : Set Z) (hN : IsOpen N) (H : NeighborhoodDeformation A N) (q : ℕ) :
    IsIso (HabsMap R (q+1) (TopCat.ofHom P.map)) := by
  let i := subIncl (Y := TopCat.of Z) A
  let j := homologyPointIncl (X := TopCat.of Y) p
  have w : i ≫ TopCat.ofHom P.map = homologyPointCollapse (TopCat.of A) ≫ j := by
    ext a
    exact (P.pointFiber a.val).mpr a.property
  letI : IsIso (HrelMap R (q+1) i j w) :=
    P.isIso_relativeMap_of_openNeighborhood N hN H R (q+1)
  have he : HabsMap R (q+1) (TopCat.ofHom P.map) =
      (contractibleRelativePositiveIso R i q).hom ≫ HrelMap R (q+1) i j w ≫
        (pointRelativePositiveIso R q (X := TopCat.of Y) p).inv := by
    rw [contractibleRelativePositiveIso_hom, ← Category.assoc, relJ_naturality]
    change HabsMap R (q+1) (TopCat.ofHom P.map) =
      HabsMap R (q+1) (TopCat.ofHom P.map) ≫ (pointRelativePositiveIso R q (X := TopCat.of Y) p).hom ≫
        (pointRelativePositiveIso R q (X := TopCat.of Y) p).inv
    rw [Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

def positiveIso_of_openNeighborhood [ContractibleSpace A]
    (N : Set Z) (hN : IsOpen N) (H : NeighborhoodDeformation A N) (q : ℕ) :
    Habs R (q+1) (TopCat.of Z) ≅ Habs R (q+1) (TopCat.of Y) := by
  letI := P.isIso_positiveMap_of_openNeighborhood R N hN H q
  exact asIso (HabsMap R (q+1) (TopCat.ofHom P.map))

@[simp] theorem positiveIso_of_openNeighborhood_hom [ContractibleSpace A]
    (N : Set Z) (hN : IsOpen N) (H : NeighborhoodDeformation A N) (q : ℕ) :
    (P.positiveIso_of_openNeighborhood R N hN H q).hom =
      HabsMap R (q+1) (TopCat.ofHom P.map) := rfl

end ClosedCollapse

/-- An unreduced suspension with a genuine good contractible arc whose
collapse is the actual compactification of `X × ℝ`. The deformation field
uses the existing `NeighborhoodDeformation` interface. To construct this
from a well-pointed `OnePoint X`, geometry must supply the cylinder quotient,
its cap cover, and the induced deformation of the arc over infinity. -/
structure CollapsedBMSuspension (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] where
  presentation : SuspensionCover Z (OnePoint X)
  arc : Set Z
  arc_contractible : ContractibleSpace arc
  collapse : ClosedCollapse arc (∞ : OnePoint (X × ℝ))
  neighborhood : Set Z
  neighborhood_open : IsOpen neighborhood
  deformation : NeighborhoodDeformation arc neighborhood

namespace CollapsedBMSuspension
variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] [T2Space X]
variable (S : CollapsedBMSuspension X Z)

def collapseIso (q : ℕ) : Habs R (q+1) (TopCat.of Z) ≅
    Habs R (q+1) (TopCat.of (OnePoint (X × ℝ))) := by
  letI : ContractibleSpace S.arc := S.arc_contractible
  exact S.collapse.positiveIso_of_openNeighborhood R S.neighborhood
    S.neighborhood_open S.deformation q

@[simp] theorem collapseIso_hom (q : ℕ) :
    (S.collapseIso R q).hom = HabsMap R (q+1) (TopCat.ofHom S.collapse.map) := rfl

/-- The actual BM suspension isomorphism obtained by collapsing the good
arc in an unreduced suspension. -/
def shiftIso (q : ℕ) (hq : 0 < q) :
    Habs R (q+1) (TopCat.of (OnePoint (X × ℝ))) ≅
      Habs R q (TopCat.of (OnePoint X)) :=
  (S.collapseIso R q).symm ≪≫ S.presentation.shiftIso R q hq

@[reassoc]
theorem collapse_comp_shift (q : ℕ) (hq : 0 < q) :
    HabsMap R (q+1) (TopCat.ofHom S.collapse.map) ≫ (S.shiftIso R q hq).hom =
      S.presentation.shift R q := by
  change (S.collapseIso R q).hom ≫
      ((S.collapseIso R q).inv ≫ (S.presentation.shiftIso R q hq).hom) = _
  rw [Iso.hom_inv_id_assoc, SuspensionCover.shiftIso_hom]

include S in
/-- Low-degree vanishing survives the good arc collapse. -/
theorem isZero_one [PathConnectedSpace (OnePoint X)] :
    IsZero (Habs R 1 (TopCat.of (OnePoint (X × ℝ)))) :=
  IsZero.of_iso (S.presentation.isZero_one R) (S.collapseIso R 0).symm

section Naturality
variable {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W] [T2Space Y]
variable (T : CollapsedBMSuspension Y W)

/-- Naturality for maps of unreduced models descending through the arc
collapse. It applies to actual compactified proper maps and stratum maps. -/
@[reassoc]
theorem shift_naturality (F : S.presentation.Map T.presentation)
    (f : TopCat.of (OnePoint (X × ℝ)) ⟶ TopCat.of (OnePoint (Y × ℝ)))
    (comm : F.total ≫ TopCat.ofHom T.collapse.map = TopCat.ofHom S.collapse.map ≫ f)
    (q : ℕ) (hq : 0 < q) :
    (S.shiftIso R q hq).hom ≫ HabsMap R q F.base =
      HabsMap R (q+1) f ≫ (T.shiftIso R q hq).hom := by
  apply (cancel_epi (S.collapseIso R q).hom).mp
  rw [← Category.assoc, collapseIso_hom, S.collapse_comp_shift R,
    S.presentation.shift_naturality T.presentation R F q]
  rw [← Category.assoc, ← HabsMap_comp, ← comm, HabsMap_comp,
    Category.assoc, T.collapse_comp_shift R]

/-- Signed naturality for reflection, after the actual good arc collapse. -/
@[reassoc]
theorem shift_reversing_naturality (F : S.presentation.ReversingMap T.presentation)
    (f : TopCat.of (OnePoint (X × ℝ)) ⟶ TopCat.of (OnePoint (Y × ℝ)))
    (comm : F.total ≫ TopCat.ofHom T.collapse.map = TopCat.ofHom S.collapse.map ≫ f)
    (q : ℕ) (hq : 0 < q) :
    (S.shiftIso R q hq).hom ≫ HabsMap R q F.base =
      -(HabsMap R (q+1) f ≫ (T.shiftIso R q hq).hom) := by
  apply (cancel_epi (S.collapseIso R q).hom).mp
  rw [← Category.assoc, collapseIso_hom, S.collapse_comp_shift R,
    S.presentation.shift_reversing_naturality T.presentation R F q]
  rw [Preadditive.comp_neg, ← Category.assoc,
    ← HabsMap_comp, ← comm, HabsMap_comp, Category.assoc, T.collapse_comp_shift R]

end Naturality

/-- The actual reflected compactification action is minus the identity
whenever its unreduced lift exchanges caps and covers the identity base. -/
theorem reflection_eq_neg (F : S.presentation.ReversingMap S.presentation)
    (f : TopCat.of (OnePoint (X × ℝ)) ⟶ TopCat.of (OnePoint (X × ℝ)))
    (comm : F.total ≫ TopCat.ofHom S.collapse.map = TopCat.ofHom S.collapse.map ≫ f)
    (hbase : F.base = 𝟙 _) (q : ℕ) (hq : 0 < q) :
    HabsMap R (q+1) f = -𝟙 _ := by
  apply (cancel_mono (S.shiftIso R q hq).hom).mp
  have h := shift_reversing_naturality R S S F f comm q hq
  rw [hbase, HabsMap_id, Category.comp_id] at h
  have h' := congrArg Neg.neg h
  simpa only [neg_neg, Preadditive.neg_comp, Category.id_comp] using h'.symm

end CollapsedBMSuspension
end NRR.SingularHomology
