import NRR.SingularHomologyFiniteCellHomology
import NRR.PrimePowerTopologyMinimalGeneration
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.LocalAtTarget

/-! Relative singular homology of a finite attachment of disks of common dimension.
After collapsing the lower subspace, the actual characteristic maps give a finite
wedge of one-point compactified open disks. -/

noncomputable section

open Set Topology Metric Filter CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePowerTopology NRR.SphereGeometry

namespace NRR.SingularHomology.FiniteCellAttachment

variable {ι V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X] {A : Set X}
  (P : FiniteCellAttachment ι V X A)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T2Space X] in
private theorem mem_characteristic_complement (i : ι) (q : CellDisk V) :
    P.characteristic i q ∈ Aᶜ ↔ ‖q.val‖ < 1 := by
  change P.characteristic i q ∉ A ↔ _
  rw [P.boundary]
  exact ⟨lt_of_le_of_ne (mem_closedBall_zero_iff.mp q.property), ne_of_lt⟩

/-- The radial open-ball chart on the preimage of the complement. -/
def characteristicInteriorChart (i : ι) : V ≃ₜ (P.characteristic i ⁻¹' Aᶜ) :=
  Homeomorph.unitBall.trans {
    toFun := fun x => ⟨⟨x.val, ball_subset_closedBall x.property⟩,
      (P.mem_characteristic_complement i _).mpr (mem_ball_zero_iff.mp x.property)⟩
    invFun := fun x => ⟨x.val.val, mem_ball_zero_iff.mpr
      ((P.mem_characteristic_complement i _).mp x.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }

/-- Each open disk is a closed branch in the complement of the lower subspace. -/
def interiorBranch (i : ι) : C(V, (Aᶜ : Set X)) :=
  ⟨Aᶜ.restrictPreimage (P.characteristic i) ∘ P.characteristicInteriorChart i,
    ((P.characteristic i).continuous.comp continuous_subtype_val).subtype_mk _ |>.comp
      (P.characteristicInteriorChart i).continuous⟩

theorem interiorBranch_unique (i j : ι) (v w : V)
    (he : P.interiorBranch i v = P.interiorBranch j w) : i = j ∧ v = w := by
  have hu := P.interior_unique i j (P.characteristicInteriorChart i v).val
    (P.characteristicInteriorChart j w).val
    ((P.mem_characteristic_complement i _).mp (P.characteristicInteriorChart i v).property)
    (congrArg Subtype.val he)
  obtain ⟨rfl, hq⟩ := hu
  exact ⟨rfl, (P.characteristicInteriorChart i).injective (Subtype.ext hq)⟩

theorem isClosedEmbedding_interiorBranch (i : ι) : IsClosedEmbedding (P.interiorBranch i) :=
  .of_continuous_injective_isClosedMap (P.interiorBranch i).continuous
    (fun _ _ he => (P.interiorBranch_unique i i _ _ he).2)
    (((P.characteristic i).continuous.isClosedMap.restrictPreimage Aᶜ).comp
      (P.characteristicInteriorChart i).isClosedMap)

def compactifiedBranch (i : ι) : C(OnePoint V, OnePoint (Aᶜ : Set X)) := by
  refine ⟨OnePoint.map (P.interiorBranch i), OnePoint.continuous_map
    (P.interiorBranch i).continuous ?_⟩
  rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
  exact (P.isClosedEmbedding_interiorBranch i).tendsto_cocompact

def wedgeProjection : C((Σ _ : ι, OnePoint V), OnePoint (Aᶜ : Set X)) :=
  ⟨fun z => P.compactifiedBranch z.1 z.2, continuous_sigma fun i =>
    (P.compactifiedBranch i).continuous⟩

theorem wedgeProjection_surjective [Nonempty ι] : Function.Surjective P.wedgeProjection := by
  intro y
  induction y using OnePoint.rec with
  | infty => exact ⟨⟨Classical.arbitrary ι, ∞⟩, rfl⟩
  | coe y =>
    obtain hy | ⟨i,q,hq⟩ := P.cover y.val
    · exact (y.property hy).elim
    · let u : P.characteristic i ⁻¹' Aᶜ := ⟨q, by
        change P.characteristic i q ∈ Aᶜ
        rw [hq]
        exact y.property⟩
      refine ⟨⟨i, ↑((P.characteristicInteriorChart i).symm u)⟩, ?_⟩
      apply congrArg (fun x : (Aᶜ : Set X) => (x : OnePoint (Aᶜ : Set X)))
      apply Subtype.ext
      change P.characteristic i ((P.characteristicInteriorChart i)
        ((P.characteristicInteriorChart i).symm u)).val = y.val
      rw [Homeomorph.apply_symm_apply]
      exact hq

theorem wedgeProjection_fiber (p q : Σ _ : ι, OnePoint V) :
    P.wedgeProjection p = P.wedgeProjection q ↔ p = q ∨ p.2 = ∞ ∧ q.2 = ∞ := by
  rcases p with ⟨i,p⟩
  rcases q with ⟨j,q⟩
  constructor
  · intro he
    cases p with
    | infty =>
      cases q with
      | infty => exact Or.inr ⟨rfl,rfl⟩
      | coe w => exact (Option.noConfusion he)
    | coe v =>
      cases q with
      | infty => exact (Option.noConfusion he)
      | coe w =>
        obtain ⟨rfl,rfl⟩ := P.interiorBranch_unique i j v w (Option.some.inj he)
        exact Or.inl rfl
  · rintro (h | ⟨hp,hq⟩)
    · exact congrArg P.wedgeProjection h
    · change p = ∞ at hp
      change q = ∞ at hq
      subst p
      subst q
      rfl

variable [Finite ι] [CompactSpace A] [CompactSpace X]

def wedgePresentation [Nonempty ι] :
    FiniteWedgePresentation ι (OnePoint V) (OnePoint (Aᶜ : Set X)) := by
  letI : LocallyCompactSpace (Aᶜ : Set X) :=
    ((isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace A)).isClosed.isOpen_compl).locallyCompactSpace
  exact {
    projection := P.wedgeProjection
    base := ∞
    point := ∞
    at_base := fun _ => rfl
    quotient := P.wedgeProjection.continuous.isClosedMap.isQuotientMap
      P.wedgeProjection.continuous P.wedgeProjection_surjective
    fiber := P.wedgeProjection_fiber }

variable (R : Type) [Ring R]

/-- In positive degree, the relative group is the direct sum of the actual
compactified branch homologies. The branch maps are induced by the disk charts. -/
def relativeCellEquiv [Nonempty ι] (hne : A.Nonempty) (k : ℕ) :
    Hrel R (k+1) (subIncl (Y := TopCat.of X) A) ≃ₗ[R]
      (ι → Habs R (k+1) (TopCat.of (OnePoint V))) := by
  classical
  letI := Fintype.ofFinite ι
  letI : LocallyCompactSpace (Aᶜ : Set X) :=
    ((isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace A)).isClosed.isOpen_compl).locallyCompactSpace
  let m := Module.finrank ℝ V
  let e := vectorOnePointSphere V m rfl
  let c := e.symm (-(e ∞))
  have hc : c ≠ ∞ := by
    intro h
    have hh := congrArg e h
    simp only [c, Homeomorph.apply_symm_apply] at hh
    exact (ne_neg_of_mem_unit_sphere ℝ (e ∞)) hh.symm
  let chart : {x : OnePoint V // x ≠ c} ≃ₜ EuclideanSpace ℝ (Fin m) :=
    (puncturedHomeomorph e c).trans ((Homeomorph.setCongr (by
      simp [c])).trans (puncturedSphereChart m (e ∞)))
  exact (P.relativeCollapsePositiveIso R hne k).toLinearEquiv.trans
    ((P.wedgePresentation).homologyEquiv R c hc (contractionOfVectorChart chart _) k).symm

/-- One copy of the coefficient ring per attached disk in the top degree. -/
def relativeTopEquiv [Nonempty ι] (hne : A.Nonempty) (q : ℕ)
    (hdim : Module.finrank ℝ V = q+1) :
    Hrel R (q+1) (subIncl (Y := TopCat.of X) A) ≃ₗ[R] (ι → R) :=
  (P.relativeCellEquiv R hne q).trans (LinearEquiv.piCongrRight fun _ =>
    (vectorOnePointTopHomologyIso R V (q+1) hdim (Nat.zero_lt_succ q)).toLinearEquiv)

include P in
theorem isZero_relative_off_top [Nonempty ι] (hne : A.Nonempty) (k : ℕ)
    (hoff : k+1 ≠ Module.finrank ℝ V) :
    IsZero (Hrel R (k+1) (subIncl (Y := TopCat.of X) A)) := by
  letI : Subsingleton (Habs R (k+1) (TopCat.of (OnePoint V))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (isZero_vectorOnePoint_off_top R V _ (k+1) rfl (by omega) hoff)
  exact ModuleCat.isZero_iff_subsingleton.mpr (P.relativeCellEquiv R hne k).injective.subsingleton


include P in
/-- The wedge is path connected for positive-dimensional cells, including
circles. Every point joins the shared point within one compactified branch. -/
theorem pathConnected_collapsed [Nonempty ι] (q : ℕ) (hdim : Module.finrank ℝ V = q+1) :
    PathConnectedSpace (OnePoint (Aᶜ : Set X)) := by
  let e := vectorOnePointSphere V (q+1) hdim
  letI : PathConnectedSpace (Sph (q+1)) := pathConnectedSpace_positiveSphere q
  letI : PathConnectedSpace (OnePoint V) := e.symm.surjective.pathConnectedSpace e.symm.continuous
  have joinBase (x : OnePoint (Aᶜ : Set X)) : Joined ∞ x := by
    obtain ⟨⟨i,z⟩,rfl⟩ := P.wedgeProjection_surjective x
    exact ⟨(PathConnectedSpace.somePath ∞ z).map (P.compactifiedBranch i).continuous⟩
  exact ⟨⟨∞⟩, fun x y => (joinBase x).symm.trans (joinBase y)⟩

include P in
theorem isZero_relative_zero [Nonempty ι] (hne : A.Nonempty) (q : ℕ)
    (hdim : Module.finrank ℝ V = q+1) :
    IsZero (Hrel R 0 (subIncl (Y := TopCat.of X) A)) := by
  let Y := TopCat.of (OnePoint (Aᶜ : Set X))
  let i := homologyPointIncl (X := Y) (∞ : OnePoint (Aᶜ : Set X))
  letI : PathConnectedSpace Y := P.pathConnected_collapsed q hdim
  letI : IsIso (HabsMap R 0 i) := isIso_HabsMap_zero_of_pathConnected R i
  have hj : relJ R 0 i = 0 :=
    (pair_exact_iota_j R 0 i).epi_f_iff.mp (by change Epi (HabsMap R 0 i); infer_instance)
  letI : Epi ((relProj R i).f 0) := (relShortComplex_degreewise_shortExact R i 0).epi_g
  letI : Epi (relJ R 0 i) := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (relProj R i) 0 (by intro j; simp)
  apply IsZero.of_iso _ (P.relativeCollapseIso R hne 0)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (relJ R 0 i)).mp
  rw [hj, zero_comp, zero_comp]


include P in
/-- With no attached disks, the lower inclusion is a homeomorphism and its
relative complex is zero, even in degree zero. -/
theorem isZero_relative_of_empty [IsEmpty ι] (k : ℕ) :
    IsZero (Hrel R k (subIncl (Y := TopCat.of X) A)) := by
  let i := subIncl (Y := TopCat.of X) A
  have hs : Function.Surjective i := by
    intro x
    rcases P.cover x with hx | ⟨j,_,_⟩
    · exact ⟨⟨x,hx⟩,rfl⟩
    · exact isEmptyElim j
  letI : IsIso i := (TopCat.isIso_iff_isHomeomorph _).mpr
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨IsEmbedding.subtypeVal, hs⟩)
  letI : IsIso (CsingMap R i) := by unfold CsingMap; infer_instance
  exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k).map_isZero
    (isZero_cokernel_of_epi (CsingMap R i))

/-- Top-degree coordinates also cover an empty family, where the function
module on the empty index set is zero. -/
def relativeTopCoordinates (hne : A.Nonempty) (q : ℕ) (hdim : Module.finrank ℝ V = q+1) :
    Hrel R (q+1) (subIncl (Y := TopCat.of X) A) ≃ₗ[R] (ι → R) := by
  classical
  by_cases h : Nonempty ι
  · exact P.relativeTopEquiv R hne q hdim
  · letI : IsEmpty ι := not_nonempty_iff.mp h
    letI := ModuleCat.isZero_iff_subsingleton.mp (P.isZero_relative_of_empty R (q+1))
    exact LinearEquiv.ofSubsingleton _ _

include P in
/-- All off-dimension groups of a positive-dimensional finite disk attachment,
with the empty attachment and degree zero included. -/
theorem isZero_relative_off_dimension (hne : A.Nonempty) (q k : ℕ)
    (hdim : Module.finrank ℝ V = q+1) (hoff : k ≠ q+1) :
    IsZero (Hrel R k (subIncl (Y := TopCat.of X) A)) := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact P.isZero_relative_of_empty R k
  | inr h =>
    cases k with
    | zero => exact P.isZero_relative_zero R hne q hdim
    | succ k => exact P.isZero_relative_off_top R hne k (by rwa [hdim])

end NRR.SingularHomology.FiniteCellAttachment
