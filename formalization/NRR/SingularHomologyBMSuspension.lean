import NRR.SingularHomologyBMSuspensionSwap
import NRR.SingularHomologyClosedCollapse
import Mathlib.Topology.Maps.Proper.Basic

/-! Suspension on actual singular homology, with its orientation and
naturality. `SuspensionCover` contains only topological data: a cover by
contractible pieces and a homotopy equivalence of their intersection.
`BMSuspensionCover` specializes its ambient space to the actual one-point
compactification of a real stabilization.

The construction of such a cover from a neighborhood deformation of infinity
is a separate topological obligation. Local compactness and Hausdorffness
alone are not claimed to imply it. In particular this file does not replace
ordinary singular homology of a compactification by a different BM theory. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.PrimePowerTopology
open scoped OnePoint

namespace NRR.SingularHomology

/-- Topological data presenting a space as a homological suspension.
There are no homology-isomorphism fields in this structure. -/
structure SuspensionCover (Z K : Type) [TopologicalSpace Z] [TopologicalSpace K] where
  lower : Set Z
  upper : Set Z
  cover : interior lower ∪ interior upper = univ
  lower_contractible : ContractibleSpace lower
  upper_contractible : ContractibleSpace upper
  overlap : ContinuousMap.HomotopyEquiv (lower ∩ upper : Set Z) K

namespace SuspensionCover
variable {Z K W L : Type} [TopologicalSpace Z] [TopologicalSpace K]
  [TopologicalSpace W] [TopologicalSpace L]
variable (S : SuspensionCover Z K) (T : SuspensionCover W L)
variable (R : Type) [Ring R]

/-- The canonical signed connecting morphism followed by the overlap map. -/
def shift (q : ℕ) : Habs R (q+1) (TopCat.of Z) ⟶ Habs R q (TopCat.of K) :=
  mvDelta R (X := TopCat.of Z) S.lower S.upper S.cover q ≫
    HabsMap R q (TopCat.ofHom S.overlap.toFun)

/-- Actual suspension isomorphism in every positive degree, over every ring. -/
def shiftIso (q : ℕ) (hq : 0 < q) :
    Habs R (q+1) (TopCat.of Z) ≅ Habs R q (TopCat.of K) := by
  letI : ContractibleSpace S.lower := S.lower_contractible
  letI : ContractibleSpace S.upper := S.upper_contractible
  letI := isIso_mvDelta R (X := TopCat.of Z) S.lower S.upper S.cover q
    (isZero_Habs_of_contractible R (q+1) (by omega) (TopCat.of S.lower))
    (isZero_Habs_of_contractible R (q+1) (by omega) (TopCat.of S.upper))
    (isZero_Habs_of_contractible R q (by omega) (TopCat.of S.lower))
    (isZero_Habs_of_contractible R q (by omega) (TopCat.of S.upper))
  exact asIso (mvDelta R (X := TopCat.of Z) S.lower S.upper S.cover q) ≪≫
    HabsIsoOfHomotopyEquiv R q S.overlap

@[simp] theorem shiftIso_hom (q : ℕ) (hq : 0 < q) :
    (S.shiftIso R q hq).hom = S.shift R q := rfl

/-- An ordered map of suspension presentations. This allows arbitrary
continuous maps; proper maps and closed-stratum inclusions enter after
extending them to the actual compactifications. -/
structure Map where
  total : TopCat.of Z ⟶ TopCat.of W
  base : TopCat.of K ⟶ TopCat.of L
  lower : Set.MapsTo total S.lower T.lower
  upper : Set.MapsTo total S.upper T.upper
  overlap :
    mvIntersectionMap (X := TopCat.of Z) (Y := TopCat.of W) S.lower S.upper T.lower T.upper total lower upper ≫
        TopCat.ofHom T.overlap.toFun =
      TopCat.ofHom S.overlap.toFun ≫ base

/-- Naturality, including inclusions whenever their compactified maps
preserve the chosen presentations. -/
@[reassoc]
theorem shift_naturality (F : S.Map T) (q : ℕ) :
    S.shift R q ≫ HabsMap R q F.base =
      HabsMap R (q+1) F.total ≫ T.shift R q := by
  unfold shift
  rw [Category.assoc, ← HabsMap_comp, ← F.overlap, HabsMap_comp,
    ← Category.assoc, mvDelta_naturality, Category.assoc]

/-- A map reversing the suspension coordinate exchanges the ordered pieces. -/
structure ReversingMap where
  total : TopCat.of Z ⟶ TopCat.of W
  base : TopCat.of K ⟶ TopCat.of L
  lower : Set.MapsTo total S.lower T.upper
  upper : Set.MapsTo total S.upper T.lower
  overlap :
    mvSwappedIntersectionMap (X := TopCat.of Z) (Y := TopCat.of W) S.lower S.upper T.lower T.upper total lower upper ≫
        TopCat.ofHom T.overlap.toFun =
      TopCat.ofHom S.overlap.toFun ≫ base

/-- Reflection contributes precisely one minus sign. -/
@[reassoc]
theorem shift_reversing_naturality (F : S.ReversingMap T) (q : ℕ) :
    S.shift R q ≫ HabsMap R q F.base =
      -(HabsMap R (q+1) F.total ≫ T.shift R q) := by
  unfold shift
  rw [Category.assoc, ← HabsMap_comp, ← F.overlap, HabsMap_comp,
    ← Category.assoc, mvDelta_swapped_naturality, Preadditive.neg_comp, Category.assoc]

/-- Reflection covering the identity acts as minus the identity on actual
positive suspension homology, with no restriction on the coefficient ring. -/
theorem reflection_eq_neg (F : S.ReversingMap S) (hbase : F.base = 𝟙 _)
    (q : ℕ) (hq : 0 < q) : HabsMap R (q+1) F.total = -𝟙 _ := by
  letI : IsIso (S.shift R q) := by
    change IsIso (S.shiftIso R q hq).hom
    infer_instance
  apply (cancel_mono (S.shift R q)).mp
  have h := S.shift_reversing_naturality S R F q
  rw [hbase, HabsMap_id, Category.comp_id] at h
  have h' := congrArg Neg.neg h
  simpa only [neg_neg, Preadditive.neg_comp, Category.id_comp] using h'.symm

include S in
/-- A suspension presentation with nonempty base is path connected. -/
theorem pathConnectedSpace [Nonempty K] : PathConnectedSpace Z := by
  letI : ContractibleSpace S.lower := S.lower_contractible
  letI : ContractibleSpace S.upper := S.upper_contractible
  have hp : IsPathConnected S.lower := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hq : IsPathConnected S.upper := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hn : (S.lower ∩ S.upper).Nonempty := by
    let x := S.overlap.invFun (Classical.choice (inferInstance : Nonempty K))
    exact ⟨x.val,x.property⟩
  have hu : S.lower ∪ S.upper = univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ interior S.lower ∪ interior S.upper := S.cover ▸ Set.mem_univ z
    exact hz.elim (fun h => Or.inl (interior_subset h)) (fun h => Or.inr (interior_subset h))
  exact pathConnectedSpace_iff_univ.mpr (hu ▸ hp.union hq hn)

include S in
/-- The first homology of the suspension vanishes when the base is path
connected. Degree zero of the pieces is handled by its actual collapse
isomorphism, never by an erroneous vanishing assertion. -/
theorem isZero_one [PathConnectedSpace K] : IsZero (Habs R 1 (TopCat.of Z)) := by
  letI : ContractibleSpace S.lower := S.lower_contractible
  letI : ContractibleSpace S.upper := S.upper_contractible
  let E := HabsIsoOfHomotopyEquiv R 0 S.overlap
  have hc : E.hom ≫ (HabsZeroCollapseIso R (TopCat.of K)).hom =
      HabsMap R 0 (homologyPointCollapse (TopCat.of (S.lower ∩ S.upper : Set Z))) := by
    change HabsMap R 0 (TopCat.ofHom S.overlap.toFun) ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of K)) = _
    rw [← HabsMap_comp, comp_homologyPointCollapse]
  letI : IsIso (HabsMap R 0
      (homologyPointCollapse (TopCat.of (S.lower ∩ S.upper : Set Z)))) := by
    rw [← hc]
    infer_instance
  letI : Mono (mvIota R (X := TopCat.of Z) S.lower S.upper 0) :=
    mono_of_mono_fac (show mvIota R (X := TopCat.of Z) S.lower S.upper 0 ≫ biprod.fst ≫
        HabsMap R 0 (homologyPointCollapse (TopCat.of S.lower)) =
      HabsMap R 0
        (homologyPointCollapse (TopCat.of (S.lower ∩ S.upper : Set Z))) by
      simp only [mvIota, biprod.lift_fst_assoc, ← HabsMap_comp,
        comp_homologyPointCollapse])
  have hd : mvDelta R (X := TopCat.of Z) S.lower S.upper S.cover 0 = 0 :=
    (mv_exact_delta_iota R (X := TopCat.of Z) S.lower S.upper S.cover 0).mono_g_iff.mp inferInstance
  letI := mono_mvDelta R (X := TopCat.of Z) S.lower S.upper S.cover 0
    (isZero_Habs_of_contractible R 1 (by omega) (TopCat.of S.lower))
    (isZero_Habs_of_contractible R 1 (by omega) (TopCat.of S.upper))
  exact IsZero.of_mono_eq_zero _ hd

end SuspensionCover

/-- A suspension presentation on the genuine one-point compactification
of `X × ℝ`, with base the genuine pointed compactification of `X`. -/
abbrev BMSuspensionCover (X : Type) [TopologicalSpace X] :=
  SuspensionCover (OnePoint (X × ℝ)) (OnePoint X)

variable (R : Type) [Ring R] {X : Type} [TopologicalSpace X]

/-- Ordinary reduced/BM homology is represented by the actual singular
pair with the point at infinity, also in degree zero. -/
abbrev Hbm (q : ℕ) (X : Type) [TopologicalSpace X] :=
  Hrel R q (homologyPointIncl (X := TopCat.of (OnePoint X)) ∞)

/-- The requested actual compactification suspension isomorphism. -/
def bmSuspensionIso (S : BMSuspensionCover X) (q : ℕ) (hq : 0 < q) :
    Habs R (q+1) (TopCat.of (OnePoint (X × ℝ))) ≅
      Habs R q (TopCat.of (OnePoint X)) := S.shiftIso R q hq

/-- The same isomorphism in the point-relative model of reduced homology. -/
def bmReducedSuspensionIso (S : BMSuspensionCover X) (q : ℕ) (hq : 0 < q) :
    Hbm R (q+1) (X × ℝ) ≅ Hbm R q X := by
  cases q with
  | zero => omega
  | succ q =>
    exact (pointRelativePositiveIso R (q+1) (X := TopCat.of (OnePoint (X × ℝ))) ∞).symm ≪≫
      bmSuspensionIso R S (q+1) hq ≪≫ pointRelativePositiveIso R q (X := TopCat.of (OnePoint X)) ∞

end NRR.SingularHomology
