import NRR.SingularHomologyGoodPair
import NRR.PrimePowerTopologyOnePointHomology
import Mathlib.Topology.CompactOpen

/-! A good-pair collapse comparison. Its topological input is an actual
neighborhood deformation, and its homological conclusion concerns the
canonical map of singular relative complexes, with no quotient axiom. -/

noncomputable section
set_option maxHeartbeats 250000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.PrimePowerTopology

namespace NRR.SingularHomology

section Topology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def intersectionSubtypeHomeomorph (S T : Set X) :
    (S ∩ T : Set X) ≃ₜ {x : S // x.val ∈ T} where
  toFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  invFun x := ⟨x.val.val,x.val.property,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def homeomorphOfBijectiveQuotient (f : X → Y) (hq : IsQuotientMap f)
    (hb : Function.Bijective f) : X ≃ₜ Y where
  toEquiv := Equiv.ofBijective f hb
  continuous_toFun := hq.continuous
  continuous_invFun := hq.continuous_iff.mpr (by
    change Continuous (fun x => (Equiv.ofBijective f hb).symm ((Equiv.ofBijective f hb) x))
    simpa only [Equiv.symm_apply_apply] using (continuous_id : Continuous (id : X → X)))

/-- A genuine quotient which identifies exactly one closed subspace. -/
structure ClosedCollapse (A : Set X) (p : Y) where
  map : C(X,Y)
  quotient : IsQuotientMap map
  fiber : ∀ x y, map x = map y ↔ x = y ∨ x ∈ A ∧ y ∈ A
  pointFiber : ∀ x, map x = p ↔ x ∈ A

namespace ClosedCollapse
variable {A : Set X} {p : Y} (P : ClosedCollapse A p)

def restrict (M : Set Y) : C(P.map ⁻¹' M,M) :=
  ⟨M.restrictPreimage P.map,
    (P.map.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem quotient_restrict (M : Set Y) (hM : IsOpen M) :
    IsQuotientMap (P.restrict M) := P.quotient.restrictPreimage_isOpen hM

/-- Off the collapsed point the quotient is an actual homeomorphism. -/
def complementHomeomorph [T1Space Y] : ↥(Aᶜ : Set X) ≃ₜ ↥({p}ᶜ : Set Y) := by
  have he : Aᶜ = P.map ⁻¹' ({p}ᶜ : Set Y) := by
    ext x
    exact (not_congr (P.pointFiber x)).symm
  let e := Homeomorph.setCongr he
  have hq := P.quotient_restrict ({p}ᶜ) isClosed_singleton.isOpen_compl
  have hinj : Function.Injective (P.restrict ({p}ᶜ : Set Y)) := by
    intro x y hxy
    apply Subtype.ext
    rcases (P.fiber x.val y.val).mp (congrArg Subtype.val hxy) with he | ⟨hx,_⟩
    · exact he
    · exact False.elim (x.property ((P.pointFiber x.val).mpr hx))
  exact e.trans (homeomorphOfBijectiveQuotient _ hq ⟨hinj,hq.surjective⟩)

@[simp] theorem complementHomeomorph_val [T1Space Y] (x : ↥(Aᶜ : Set X)) :
    (P.complementHomeomorph x).val = P.map x.val := rfl

include P in
theorem isClosed_subspace [T1Space Y] : IsClosed A := by
  have he : A = P.map ⁻¹' {p} := by
    ext x
    exact (P.pointFiber x).symm
  rw [he]
  exact isClosed_singleton.preimage P.map.continuous

def overlapHomeomorph [T1Space Y] (M : Set Y) :
    ↥(Aᶜ ∩ P.map ⁻¹' M : Set X) ≃ₜ ↥({p}ᶜ ∩ M : Set Y) :=
  (intersectionSubtypeHomeomorph Aᶜ (P.map ⁻¹' M)).trans
    ((P.complementHomeomorph.subtype (fun _ => Iff.rfl)).trans
      (intersectionSubtypeHomeomorph ({p}ᶜ) M).symm)

end ClosedCollapse

/-- A strong neighborhood deformation, expressed with actual maps and a
jointly continuous homotopy. Preservation of the whole subspace is what
allows descent through a collapse quotient. -/
structure NeighborhoodDeformation (A N : Set X) where
  subset : A ⊆ N
  retract : C(N,A)
  retraction : ∀ a : A, retract ⟨a.val,subset a.property⟩ = a
  homotopy :
    ((⟨fun a : A => (⟨a.val,subset a.property⟩ : N),
      continuous_subtype_val.subtype_mk _⟩ : C(A,N)).comp retract).Homotopy (ContinuousMap.id N)
  preserve : ∀ (t : unitInterval) (a : A),
    (homotopy (t,⟨a.val,subset a.property⟩)).val ∈ A

namespace NeighborhoodDeformation
variable {A N : Set X} (H : NeighborhoodDeformation A N)

def inclusion : C(A,N) :=
  ⟨fun a => ⟨a.val,H.subset a.property⟩,continuous_subtype_val.subtype_mk _⟩

def homotopyEquiv : ContinuousMap.HomotopyEquiv A N where
  toFun := H.inclusion
  invFun := H.retract
  left_inv := by
    have he : H.retract.comp H.inclusion = ContinuousMap.id A := by
      ext a
      exact congrArg Subtype.val (H.retraction a)
    rw [he]
  right_inv := ⟨H.homotopy⟩

end NeighborhoodDeformation

namespace ClosedCollapse
variable {A : Set X} {p : Y} (P : ClosedCollapse A p)
variable (M : Set Y) (hM : IsOpen M) (hp : p ∈ M)
variable (H : NeighborhoodDeformation A (P.map ⁻¹' M))

private def neighborhoodLift : M → P.map ⁻¹' M :=
  Function.surjInv (P.quotient_restrict M hM).surjective

private theorem restrict_neighborhoodLift (y : M) :
    P.restrict M (P.neighborhoodLift M hM y) = y :=
  Function.surjInv_eq (P.quotient_restrict M hM).surjective y

private theorem homotopy_fiber (t : unitInterval) (x y : P.map ⁻¹' M)
    (hxy : P.restrict M x = P.restrict M y) :
    P.restrict M (H.homotopy (t,x)) = P.restrict M (H.homotopy (t,y)) := by
  apply Subtype.ext
  rcases (P.fiber x.val y.val).mp (congrArg Subtype.val hxy) with he | ⟨hx,hy⟩
  · have he' : x = y := Subtype.ext he
    rw [he']
  · exact ((P.pointFiber _).mpr (H.preserve t ⟨x.val,hx⟩)).trans
      ((P.pointFiber _).mpr (H.preserve t ⟨y.val,hy⟩)).symm

/-- The neighborhood deformation descends through the actual quotient.
Local compactness of the time interval supplies joint continuity. -/
def neighborhoodContraction :
    (ContinuousMap.const M (⟨p,hp⟩ : M)).Homotopy (ContinuousMap.id M) where
  toFun z := P.restrict M (H.homotopy (z.1,P.neighborhoodLift M hM z.2))
  continuous_toFun := by
    apply (P.quotient_restrict M hM).continuous_lift_prod_right
    have he : (fun z : unitInterval × (P.map ⁻¹' M) =>
        P.restrict M (H.homotopy (z.1,
          P.neighborhoodLift M hM (P.restrict M z.2)))) =
        fun z => P.restrict M (H.homotopy z) := by
      funext z
      exact P.homotopy_fiber M H z.1 _ _ (P.restrict_neighborhoodLift M hM _)
    rw [he]
    exact (P.restrict M).continuous.comp H.homotopy.continuous
  map_zero_left y := by
    apply Subtype.ext
    change P.map (H.homotopy (0,P.neighborhoodLift M hM y)).val = p
    have he := congrArg (fun x : P.map ⁻¹' M => P.map x.val)
      (H.homotopy.map_zero_left (P.neighborhoodLift M hM y))
    exact he.trans ((P.pointFiber _).mpr (H.retract (P.neighborhoodLift M hM y)).property)
  map_one_left y := by
    change P.restrict M (H.homotopy (1,P.neighborhoodLift M hM y)) = y
    exact (congrArg (P.restrict M)
      (H.homotopy.map_one_left (P.neighborhoodLift M hM y))).trans
        (P.restrict_neighborhoodLift M hM y)

include P hM hp H in
theorem contractible_neighborhood : ContractibleSpace M :=
  (contractible_iff_id_nullhomotopic M).mpr
    ⟨⟨p,hp⟩,⟨(P.neighborhoodContraction M hM hp H).symm⟩⟩

def neighborhoodPointEquiv : ContinuousMap.HomotopyEquiv Unit M where
  toFun := ContinuousMap.const _ ⟨p,hp⟩
  invFun := ContinuousMap.const _ ()
  left_inv := by
    have he : (ContinuousMap.const M ()).comp (ContinuousMap.const Unit (⟨p,hp⟩ : M)) =
        ContinuousMap.id Unit := by ext u
    rw [he]
  right_inv := ⟨P.neighborhoodContraction M hM hp H⟩

include P M hM hp H in
/-- The canonical map of the actual singular pairs is a homology
isomorphism for a genuine neighborhood deformation pair. -/
theorem isIso_relativeMap [T1Space Y] (R : Type) [Ring R] (n : ℕ) :
    IsIso (HrelMap R n (subIncl (Y := TopCat.of X) A)
      (homologyPointIncl (X := TopCat.of Y) p)
      (show subIncl A ≫ TopCat.ofHom P.map =
          homologyPointCollapse (TopCat.of A) ≫ homologyPointIncl p by
        ext a
        exact (P.pointFiber a.val).mpr a.property)) := by
  let N : Set X := P.map ⁻¹' M
  let U : Set X := Aᶜ
  let V : Set Y := {p}ᶜ
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom P.map
  let i : TopCat.of A ⟶ TopCat.of X := subIncl (Y := TopCat.of X) A
  let j : TopCat.of Unit ⟶ TopCat.of Y := homologyPointIncl p
  let iN : TopCat.of N ⟶ TopCat.of X := subIncl (Y := TopCat.of X) N
  let jM : TopCat.of M ⟶ TopCat.of Y := subIncl (Y := TopCat.of Y) M
  let a : TopCat.of A ⟶ TopCat.of N := TopCat.ofHom H.inclusion
  let b : TopCat.of Unit ⟶ TopCat.of M := homologyPointIncl ⟨p,hp⟩
  let fA : TopCat.of A ⟶ TopCat.of Unit := homologyPointCollapse _
  let hN : Set.MapsTo f N M := fun _ hx => hx
  let fN : TopCat.of N ⟶ TopCat.of M := mvRestrictMap N M f hN
  letI : Mono i := by dsimp [i]; infer_instance
  letI : Mono j := by dsimp [j]; infer_instance
  letI : Mono iN := by dsimp [iN]; infer_instance
  letI : Mono jM := by dsimp [jM]; infer_instance
  have w : i ≫ f = fA ≫ j := by
    ext a
    exact (P.pointFiber a.val).mpr a.property
  have wN : iN ≫ f = fN ≫ jM := rfl
  have ha : ∀ k, IsIso (HabsMap R k a) := by
    intro k
    change IsIso (HabsIsoOfHomotopyEquiv R k H.homotopyEquiv).hom
    infer_instance
  have hb : ∀ k, IsIso (HabsMap R k b) := by
    intro k
    change IsIso (HabsIsoOfHomotopyEquiv R k (P.neighborhoodPointEquiv M hM hp H)).hom
    infer_instance
  have hn : ∀ k, IsIso (HrelMap R k iN jM wN) := by
    intro k
    have hU : Set.MapsTo f U V := fun x hx hy => hx ((P.pointFiber x).mp hy)
    have hopenN : IsOpen N := hM.preimage P.map.continuous
    have hopenU : IsOpen U := P.isClosed_subspace.isOpen_compl
    have hopenV : IsOpen V := isClosed_singleton.isOpen_compl
    have coverX : interior U ∪ interior N = Set.univ := by
      rw [hopenU.interior_eq,hopenN.interior_eq]
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ A
      · exact Or.inr (H.subset hx)
      · exact Or.inl hx
    have coverY : interior V ∪ interior M = Set.univ := by
      rw [hopenV.interior_eq,hM.interior_eq]
      apply Set.eq_univ_of_forall
      intro y
      by_cases hy : y = p
      · exact Or.inr (hy ▸ hp)
      · exact Or.inl hy
    letI : IsIso (mvRestrictMap U V f hU) :=
      (TopCat.isIso_iff_isHomeomorph _).mpr P.complementHomeomorph.isHomeomorph
    letI : IsIso (mvIntersectionMap U N V M f hU hN) :=
      (TopCat.isIso_iff_isHomeomorph _).mpr (P.overlapHomeomorph M).isHomeomorph
    change IsIso (HrelMap R k (subIncl (Y := TopCat.of X) N) (subIncl (Y := TopCat.of Y) M)
      (mvRestrictMap_subIncl N M f hN).symm)
    exact isIso_HrelMap_of_excisionComparison (X := TopCat.of X) (Y := TopCat.of Y)
      R U N V M f hU hN coverX coverY k
  exact isIso_HrelMap_of_goodNeighborhoods R i j iN jM a b rfl rfl w wN ha hb hn n

include P in
/-- The image of a saturated deformation neighborhood supplies the
target neighborhood automatically. -/
theorem isIso_relativeMap_of_openNeighborhood [T1Space Y]
    (N : Set X) (hN : IsOpen N) (H : NeighborhoodDeformation A N)
    (R : Type) [Ring R] (n : ℕ) :
    IsIso (HrelMap R n (subIncl (Y := TopCat.of X) A)
      (homologyPointIncl (X := TopCat.of Y) p)
      (show subIncl A ≫ TopCat.ofHom P.map =
          homologyPointCollapse (TopCat.of A) ≫ homologyPointIncl p by
        ext a
        exact (P.pointFiber a.val).mpr a.property)) := by
  let M : Set Y := P.map '' N
  have he : P.map ⁻¹' M = N := by
    ext x
    constructor
    · rintro ⟨y,hy,hyx⟩
      rcases (P.fiber y x).mp hyx with h | ⟨_,hx⟩
      · exact h ▸ hy
      · exact H.subset hx
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hM : IsOpen M := P.quotient.isOpen_preimage.mp (he.symm ▸ hN)
  have hp : p ∈ M := by
    obtain ⟨a,ha⟩ := P.quotient.surjective p
    exact ⟨a,H.subset ((P.pointFiber a).mp ha),ha⟩
  have H' : NeighborhoodDeformation A (P.map ⁻¹' M) := by
    rw [he]
    exact H
  exact P.isIso_relativeMap M hM hp H' R n

end ClosedCollapse
end Topology

end NRR.SingularHomology

