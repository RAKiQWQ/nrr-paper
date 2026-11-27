import NRR.SingularHomologyMayerVietorisCover
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.LocalAtTarget

/-! Actual positive singular homology of finite wedges.  The open sets used
below are punctured in the other branches; closed branches are never treated
as an excisive cover. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.SphereGeometry

namespace NRR.SingularHomology

variable (R : Type) [Ring R]

def sigmaSetHomeomorph {ι T : Type} [TopologicalSpace T]
    (S : Set (Σ _ : ι,T)) : (Σ i : ι, {x : T // (⟨i,x⟩ : Σ _ : ι,T) ∈ S}) ≃ₜ S := by
  let e : (Σ i : ι, {x : T // (⟨i,x⟩ : Σ _ : ι,T) ∈ S}) ≃ S := {
    toFun := fun p => ⟨⟨p.1,p.2.val⟩,p.2.property⟩
    invFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine e.toHomeomorphOfContinuousOpen ?_ ?_
  · apply continuous_sigma
    intro i
    change Continuous (fun a : {x : T // (⟨i,x⟩ : Σ _ : ι,T) ∈ S} =>
      (⟨⟨i,a.val⟩,a.property⟩ : S))
    have h : Continuous (fun a : {x : T // (⟨i,x⟩ : Σ _ : ι,T) ∈ S} =>
        (⟨i,a.val⟩ : Σ _ : ι,T)) := continuous_sigmaMk.comp continuous_subtype_val
    exact h.subtype_mk _
  · exact isOpenMap_sigma.mpr fun i =>
      (IsOpenEmbedding.sigmaMk.restrictPreimage S).isOpenMap

/-- A contractible intersection makes the signed Mayer--Vietoris sum map
an isomorphism in every positive degree, including degree one. -/
theorem isIso_mvKappa_of_contractible_intersection {X : TopCat.{0}}
    (A B : Set X) (cover : interior A ∪ interior B = Set.univ)
    [ContractibleSpace (A ∩ B : Set X)] (n : ℕ) :
    IsIso (mvKappa R A B (n+1)) := by
  have hi : mvIota R A B (n+1) = 0 :=
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega)
      (TopCat.of (A ∩ B : Set X))).eq_zero_of_src _
  have hd : mvDelta R A B cover n = 0 := by
    cases n with
    | zero =>
      let p : mvSum R A B 0 ⟶ Habs R 0 (TopCat.of Unit) :=
        biprod.fst ≫ HabsMap R 0
          (NRR.PrimePowerTopology.homologyPointCollapse (TopCat.of A))
      have hp : mvIota R A B 0 ≫ p = HabsMap R 0
          (NRR.PrimePowerTopology.homologyPointCollapse (TopCat.of (A ∩ B : Set X))) := by
        simp only [p, mvIota, biprod.lift_fst_assoc, ← HabsMap_comp]
        rfl
      letI : IsIso (mvIota R A B 0 ≫ p) := by
        rw [hp]
        exact NRR.PrimePowerTopology.isIso_HabsMap_zero_of_pathConnected R _
      letI : Mono (mvIota R A B 0) := mono_of_mono (mvIota R A B 0) p
      exact (mv_exact_delta_iota R A B cover 0).mono_g_iff.mp inferInstance
    | succ n =>
      exact (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega)
        (TopCat.of (A ∩ B : Set X))).eq_zero_of_tgt _
  letI : Mono (mvKappa R A B (n+1)) := (mv_exact_iota_kappa R A B cover (n+1)).mono_g hi
  letI : Epi (mvKappa R A B (n+1)) := (mv_exact_kappa_delta R A B cover n).epi_f hd
  exact isIso_of_mono_of_epi _

def subsetPreimageHomeomorph {X : Type} [TopologicalSpace X]
    (U V : Set X) (h : U ⊆ V) : U ≃ₜ ((Subtype.val : V → X) ⁻¹' U) where
  toFun x := ⟨⟨x.val,h x.property⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Images of positive homology classes on an excisive union are generated
by the two images whenever the intersection is contractible. -/
theorem homology_range_union_le {X : TopCat.{0}} (A B : Set X)
    (hAo : IsOpen A) (hBo : IsOpen B) [ContractibleSpace (A ∩ B : Set X)]
    (n : ℕ) (M : Submodule R (Habs R (n+1) X))
    (hA : LinearMap.range (HabsMap R (n+1) (subIncl A)).hom ≤ M)
    (hB : LinearMap.range (HabsMap R (n+1) (subIncl B)).hom ≤ M) :
    LinearMap.range (HabsMap R (n+1) (subIncl (A ∪ B))).hom ≤ M := by
  let Y := TopCat.of (A ∪ B : Set X)
  let A' : Set Y := Subtype.val ⁻¹' A
  let B' : Set Y := Subtype.val ⁻¹' B
  let e : (A ∩ B : Set X) ≃ₜ (A' ∩ B' : Set Y) :=
    subsetPreimageHomeomorph (A ∩ B) (A ∪ B)
      (fun _ h => Or.inl h.1)
  letI : ContractibleSpace (A' ∩ B' : Set Y) := e.symm.contractibleSpace
  have hoA : IsOpen A' := hAo.preimage continuous_subtype_val
  have hoB : IsOpen B' := hBo.preimage continuous_subtype_val
  have cover : interior A' ∪ interior B' = Set.univ := by
    rw [hoA.interior_eq,hoB.interior_eq]
    ext y
    exact iff_true_intro y.property
  letI := isIso_mvKappa_of_contractible_intersection R A' B' cover n
  let q : Habs R (n+1) X ⟶ ModuleCat.of R ((Habs R (n+1) X) ⧸ M) :=
    ModuleCat.ofHom M.mkQ
  have ha : HabsMap R (n+1) (subIncl A) ≫ q = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero M).mpr (hA ⟨x,rfl⟩)
  have hb : HabsMap R (n+1) (subIncl B) ≫ q = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero M).mpr (hB ⟨x,rfl⟩)
  let lA : TopCat.of A' ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x => ⟨x.val.val,x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let lB : TopCat.of B' ⟶ TopCat.of B := TopCat.ofHom
    ⟨fun x => ⟨x.val.val,x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hz : HabsMap R (n+1) (subIncl (A ∪ B)) ≫ q = 0 := by
    apply (cancel_epi (mvKappa R A' B' (n+1))).mp
    rw [comp_zero]
    apply biprod.hom_ext'
    · simp only [mvKappa_eq_desc, biprod.inl_desc_assoc, comp_zero]
      rw [← Category.assoc, ← HabsMap_comp]
      change HabsMap R (n+1) (lA ≫ subIncl A) ≫ q = 0
      rw [HabsMap_comp,Category.assoc,ha,comp_zero]
    · simp only [mvKappa_eq_desc, biprod.inr_desc_assoc, comp_zero,
        Preadditive.neg_comp, neg_eq_zero]
      rw [← Category.assoc, ← HabsMap_comp]
      change HabsMap R (n+1) (lB ≫ subIncl B) ≫ q = 0
      rw [HabsMap_comp,Category.assoc,hb,comp_zero]
  rintro z ⟨x,rfl⟩
  apply (Submodule.Quotient.mk_eq_zero M).mp
  exact congrArg (fun f => f x) hz

/-- A finite wedge is specified by its actual topological quotient, with
only the chosen basepoints identified. -/
structure FiniteWedgePresentation (ι T W : Type) [TopologicalSpace T]
    [TopologicalSpace W] where
  projection : C((Σ _ : ι, T), W)
  base : T
  point : W
  at_base : ∀ i, projection ⟨i,base⟩ = point
  quotient : IsQuotientMap projection
  fiber : ∀ p q, projection p = projection q ↔
    p = q ∨ p.2 = base ∧ q.2 = base

namespace FiniteWedgePresentation
variable {ι T W : Type} [TopologicalSpace T] [TopologicalSpace W]
variable (P : FiniteWedgePresentation ι T W)

def inclusion (i : ι) : C(T,W) :=
  ⟨fun x => P.projection ⟨i,x⟩, P.projection.continuous.comp continuous_sigmaMk⟩

@[simp] theorem inclusion_base (i : ι) : P.inclusion i P.base = P.point := P.at_base i

theorem inclusion_injective (i : ι) : Function.Injective (P.inclusion i) := by
  intro x y h
  rcases (P.fiber ⟨i,x⟩ ⟨i,y⟩).mp h with h | ⟨hx,hy⟩
  · exact congrArg Sigma.snd h
  · exact hx.trans hy.symm

def pinchOnSum (i : ι) : C((Σ _ : ι,T),T) := by
  classical
  refine ⟨fun p => if p.1 = i then p.2 else P.base, continuous_sigma fun j => ?_⟩
  by_cases h : j = i
  · simpa only [if_pos h] using (continuous_id : Continuous (fun x : T => x))
  · simpa only [if_neg h] using (continuous_const : Continuous (fun _ : T => P.base))

theorem pinchOnSum_factors (i : ι) :
    Function.FactorsThrough (P.pinchOnSum i) P.projection := by
  classical
  intro p q h
  rcases (P.fiber p q).mp h with rfl | ⟨hp,hq⟩
  · rfl
  · simp [pinchOnSum, hp, hq]

def pinch (i : ι) : C(W,T) := P.quotient.lift (P.pinchOnSum i) (P.pinchOnSum_factors i)

@[simp] theorem pinch_projection (i : ι) (p : Σ _ : ι,T) :
    P.pinch i (P.projection p) = P.pinchOnSum i p := by
  exact congrArg (fun f : C((Σ _ : ι,T),T) => f p)
    (P.quotient.lift_comp (P.pinchOnSum i) (P.pinchOnSum_factors i))

@[simp] theorem pinch_same (i : ι) (x : T) : P.pinch i (P.inclusion i x) = x := by
  classical
  change P.pinch i (P.projection ⟨i,x⟩) = x
  simp [pinchOnSum]

@[simp] theorem pinch_other (i j : ι) (h : j ≠ i) (x : T) :
    P.pinch i (P.inclusion j x) = P.base := by
  classical
  change P.pinch i (P.projection ⟨j,x⟩) = P.base
  simp [pinchOnSum, h]

variable [Fintype ι] [DecidableEq ι] [T1Space W]
variable (c : T) (hc : c ≠ P.base)

/-- All branches indexed by `s` are retained, and each other branch is
punctured at its marked non-basepoint. -/
def region (s : Finset ι) : Set W :=
  {x | ∀ i, i ∉ s → x ≠ P.inclusion i c}

theorem isOpen_region (s : Finset ι) : IsOpen (P.region c s) := by
  have he : P.region c s = ⋂ i : ι, ⋂ (_ : i ∉ s), ({P.inclusion i c} : Set W)ᶜ := by
    ext x
    simp [region]
  rw [he]
  exact isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ =>
    isClosed_singleton.isOpen_compl

include hc

@[simp] theorem point_mem_region (s : Finset ι) : P.point ∈ P.region c s := by
  intro i _ h
  have h' : P.inclusion i P.base = P.inclusion i c := (P.inclusion_base i).trans h
  exact hc ((P.inclusion_injective i h').symm)

theorem marks_injective : Function.Injective (fun i => P.inclusion i c) := by
  intro i j h
  rcases (P.fiber ⟨i,c⟩ ⟨j,c⟩).mp h with h | h
  · exact congrArg Sigma.fst h
  · exact False.elim (hc h.1)

@[simp] theorem inclusion_mem_region (s : Finset ι) (i : ι) (x : T) :
    P.inclusion i x ∈ P.region c s ↔ i ∈ s ∨ x ≠ c := by
  constructor
  · intro h
    by_cases hi : i ∈ s
    · exact Or.inl hi
    · exact Or.inr fun hx => h i hi (hx ▸ rfl)
  · rintro (hi | hx) j hj he
    · rcases (P.fiber ⟨i,x⟩ ⟨j,c⟩).mp he with he | he
      · have hij : i = j := congrArg Sigma.fst he
        exact hj (hij ▸ hi)
      · exact hc he.2
    · rcases (P.fiber ⟨i,x⟩ ⟨j,c⟩).mp he with he | he
      · exact hx (congrArg Sigma.snd he)
      · exact hc he.2

omit hc in
@[simp] theorem region_univ : P.region c Finset.univ = Set.univ := by ext x; simp [region]

omit hc in
theorem region_mono {s t : Finset ι} (h : s ⊆ t) : P.region c s ⊆ P.region c t := by
  intro x hx i hi
  exact hx i (fun his => hi (h his))

omit hc in
theorem region_inter (s t : Finset ι) :
    P.region c s ∩ P.region c t = P.region c (s ∩ t) := by
  ext x
  simp only [region, mem_setOf_eq, mem_inter_iff, Finset.mem_inter]
  constructor
  · rintro ⟨hs,ht⟩ i hi
    by_cases his : i ∈ s
    · exact ht i (fun hit => hi ⟨his,hit⟩)
    · exact hs i his
  · intro h
    exact ⟨fun i hi => h i (fun his => hi his.1),
      fun i hi => h i (fun hit => hi hit.2)⟩

theorem region_union (s t : Finset ι) :
    P.region c s ∪ P.region c t = P.region c (s ∪ t) := by
  ext x
  constructor
  · rintro (h | h) i hi
    · exact h i (fun his => hi (Finset.mem_union_left _ his))
    · exact h i (fun hit => hi (Finset.mem_union_right _ hit))
  · intro h
    by_contra hn
    simp only [mem_union, not_or, region, mem_setOf_eq, not_forall, _root_.not_imp, not_not] at hn
    obtain ⟨⟨i,hi,hxi⟩,j,hj,hxj⟩ := hn
    have hij := P.marks_injective c hc (hxi.symm.trans hxj)
    subst j
    exact h i (by simpa using And.intro hi hj) hxi

omit hc in
def regionProjection (s : Finset ι) :
    C((Σ i : ι, {x : T // P.inclusion i x ∈ P.region c s}), P.region c s) :=
  (P.projection.restrictPreimage (P.region c s)).comp
    ⟨sigmaSetHomeomorph (P.projection ⁻¹' P.region c s),
      (sigmaSetHomeomorph (P.projection ⁻¹' P.region c s)).continuous⟩

omit hc in
@[simp] theorem regionProjection_apply (s : Finset ι)
    (p : Σ i : ι, {x : T // P.inclusion i x ∈ P.region c s}) :
    (P.regionProjection c s p).val = P.inclusion p.1 p.2.val := rfl

theorem quotient_regionProjection (s : Finset ι) :
    IsQuotientMap (P.regionProjection c s) :=
  (P.quotient.restrictPreimage_isOpen (P.isOpen_region c s)).comp
    (sigmaSetHomeomorph (P.projection ⁻¹' P.region c s)).isQuotientMap

variable (H : ContractionData {x : T // x ≠ c} ⟨P.base, Ne.symm hc⟩)
open unitInterval

def localPath (s : Finset ι) (i : ι) :
    C(I × {x : T // P.inclusion i x ∈ P.region c s}, T) := by
  refine ⟨fun p => if hi : i ∈ s then p.2.val else
    (H.curve (⟨p.2.val, ((P.inclusion_mem_region c hc s i p.2.val).mp
      p.2.property).resolve_left hi⟩,p.1)).val, ?_⟩
  by_cases hi : i ∈ s
  · simpa only [dif_pos hi] using continuous_subtype_val.comp continuous_snd
  · simpa only [dif_neg hi] using continuous_subtype_val.comp
      (H.curve.continuous.comp
        (((continuous_subtype_val.comp continuous_snd).subtype_mk _).prodMk continuous_fst))

@[simp] theorem localPath_one (s : Finset ι) (i : ι)
    (x : {x : T // P.inclusion i x ∈ P.region c s}) :
    P.localPath c hc H s i (1,x) = x.val := by
  by_cases hi : i ∈ s <;> simp [localPath, hi]

theorem localPath_base (s : Finset ι) (i : ι)
    (x : {x : T // P.inclusion i x ∈ P.region c s})
    (hx : x.val = P.base) (t : I) : P.localPath c hc H s i (t,x) = P.base := by
  by_cases hi : i ∈ s
  · simp [localPath, hi, hx]
  · simp only [localPath, ContinuousMap.coe_mk, dif_neg hi]
    have hxe : (⟨x.val, ((P.inclusion_mem_region c hc s i x.val).mp
        x.property).resolve_left hi⟩ : {x : T // x ≠ c}) = ⟨P.base,Ne.symm hc⟩ :=
      Subtype.ext hx
    rw [hxe, ContractionData.curve_base]

theorem localPath_mem_region (s : Finset ι) (i : ι)
    (p : I × {x : T // P.inclusion i x ∈ P.region c s}) :
    P.inclusion i (P.localPath c hc H s i p) ∈ P.region c s := by
  apply (P.inclusion_mem_region c hc s i _).mpr
  by_cases hi : i ∈ s
  · exact Or.inl hi
  · right
    simpa only [localPath, ContinuousMap.coe_mk, dif_neg hi] using
      (H.curve (⟨p.2.val, ((P.inclusion_mem_region c hc s i p.2.val).mp
        p.2.property).resolve_left hi⟩,p.1)).property

def branchDeform (s : Finset ι) (i : ι) :
    C(I × {x : T // P.inclusion i x ∈ P.region c s}, P.region c s) :=
  ⟨fun p => ⟨P.inclusion i (P.localPath c hc H s i p),
      P.localPath_mem_region c hc H s i p⟩,
    ((P.inclusion i).continuous.comp (P.localPath c hc H s i).continuous).subtype_mk _⟩

def branchDeformCurry (s : Finset ι) (i : ι) :
    C({x : T // P.inclusion i x ∈ P.region c s}, C(I,P.region c s)) :=
  ContinuousMap.curry ⟨fun p => P.branchDeform c hc H s i (p.2,p.1),
    (P.branchDeform c hc H s i).continuous.comp continuous_swap⟩

def sumDeform (s : Finset ι) :
    C((Σ i : ι, {x : T // P.inclusion i x ∈ P.region c s}), C(I,P.region c s)) :=
  ⟨fun p => P.branchDeformCurry c hc H s p.1 p.2,
    continuous_sigma fun i => (P.branchDeformCurry c hc H s i).continuous⟩

theorem sumDeform_factors (s : Finset ι) :
    Function.FactorsThrough (P.sumDeform c hc H s) (P.regionProjection c s) := by
  intro p q h
  have he : P.projection ⟨p.1,p.2.val⟩ = P.projection ⟨q.1,q.2.val⟩ :=
    congrArg Subtype.val h
  rcases (P.fiber _ _).mp he with he | ⟨hp,hq⟩
  · have hpq : p = q := by
      apply (sigmaSetHomeomorph (P.projection ⁻¹' P.region c s)).injective
      exact Subtype.ext he
    rw [hpq]
  · apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change P.inclusion p.1 (P.localPath c hc H s p.1 (t,p.2)) =
      P.inclusion q.1 (P.localPath c hc H s q.1 (t,q.2))
    rw [P.localPath_base c hc H s p.1 p.2 hp t,
      P.localPath_base c hc H s q.1 q.2 hq t, P.inclusion_base, P.inclusion_base]

def deform (s : Finset ι) : C(I × P.region c s, P.region c s) := by
  let lifted := (P.quotient_regionProjection c hc s).lift (P.sumDeform c hc H s)
    (P.sumDeform_factors c hc H s)
  exact ⟨fun p => lifted p.2 p.1,
    (ContinuousMap.continuous_uncurry_of_continuous lifted).comp continuous_swap⟩

@[simp] theorem deform_projection (s : Finset ι) (t : I)
    (p : Σ i : ι, {x : T // P.inclusion i x ∈ P.region c s}) :
    P.deform c hc H s (t,P.regionProjection c s p) =
      P.branchDeform c hc H s p.1 (t,p.2) := by
  exact congrArg (fun f : C((Σ i : ι, {x : T // P.inclusion i x ∈ P.region c s}),
    C(I,P.region c s)) => f p t)
      ((P.quotient_regionProjection c hc s).lift_comp (P.sumDeform c hc H s)
        (P.sumDeform_factors c hc H s))

@[simp] theorem deform_one (s : Finset ι) (x : P.region c s) :
    P.deform c hc H s (1,x) = x := by
  obtain ⟨p,rfl⟩ := (P.quotient_regionProjection c hc s).surjective x
  apply Subtype.ext
  simp [branchDeform]

@[simp] theorem deform_empty_zero (x : P.region c ∅) :
    P.deform c hc H ∅ (0,x) = ⟨P.point,P.point_mem_region c hc ∅⟩ := by
  obtain ⟨p,rfl⟩ := (P.quotient_regionProjection c hc ∅).surjective x
  apply Subtype.ext
  simp [branchDeform, localPath]

include H

/-- All punctured branches contract simultaneously at the common point;
joint continuity follows from the actual quotient and compact-open currying. -/
theorem contractible_region_empty : ContractibleSpace (P.region c ∅) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨P.point,P.point_mem_region c hc ∅⟩, ⟨?_⟩⟩
  exact (show (ContinuousMap.const (P.region c ∅) ⟨P.point,P.point_mem_region c hc ∅⟩).Homotopy
    (ContinuousMap.id _) from
    ⟨P.deform c hc H ∅, P.deform_empty_zero c hc H, P.deform_one c hc H ∅⟩).symm

theorem deform_singleton_zero_val (i : ι) (x : P.region c {i}) :
    (P.deform c hc H {i} (0,x)).val = P.inclusion i (P.pinch i x.val) := by
  classical
  obtain ⟨⟨j,x⟩,rfl⟩ := (P.quotient_regionProjection c hc {i}).surjective x
  rw [deform_projection]
  change P.inclusion j (P.localPath c hc H {i} j (0,x)) =
    P.inclusion i (P.pinch i (P.projection ⟨j,x.val⟩))
  by_cases h : j = i
  · subst j
    simp [localPath, pinchOnSum]
  · simp [localPath, pinchOnSum, h]

def singletonHomotopy (i : ι) :
    ((P.inclusion i).comp ((P.pinch i).comp
      ⟨Subtype.val,continuous_subtype_val⟩)).Homotopy
      (⟨Subtype.val,continuous_subtype_val⟩ : C(P.region c {i},W)) where
  toContinuousMap := ⟨fun p => (P.deform c hc H {i} p).val,
    continuous_subtype_val.comp (P.deform c hc H {i}).continuous⟩
  map_zero_left x := P.deform_singleton_zero_val c hc H i x
  map_one_left x := congrArg Subtype.val (P.deform_one c hc H {i} x)

/-- Every actual positive homology class of a finite wedge is generated
by its genuine branch inclusion maps. -/
theorem iSup_range_homologyInclusion_eq_top (n : ℕ) :
    (⨆ i : ι, LinearMap.range
      (HabsMap R (n+1) (TopCat.ofHom (P.inclusion i))).hom) = ⊤ := by
  let M : Submodule R (Habs R (n+1) (TopCat.of W)) :=
    ⨆ i : ι, LinearMap.range (HabsMap R (n+1) (TopCat.ofHom (P.inclusion i))).hom
  have hsingle (i : ι) :
      LinearMap.range (HabsMap R (n+1) (subIncl (Y := TopCat.of W) (P.region c {i}))).hom ≤ M := by
    let r : TopCat.of (P.region c {i}) ⟶ TopCat.of T :=
      TopCat.ofHom ((P.pinch i).comp ⟨Subtype.val,continuous_subtype_val⟩)
    have he : HabsMap R (n+1) (r ≫ TopCat.ofHom (P.inclusion i)) =
        HabsMap R (n+1) (subIncl (Y := TopCat.of W) (P.region c {i})) :=
      NRR.PrimePowerTopology.HabsMap_eq_of_homotopy R (n+1) (P.singletonHomotopy c hc H i)
    rw [HabsMap_comp] at he
    rintro z ⟨x,rfl⟩
    rw [← he]
    exact (le_iSup (fun i => LinearMap.range
      (HabsMap R (n+1) (TopCat.ofHom (P.inclusion i))).hom) i)
      ⟨HabsMap R (n+1) r x,rfl⟩
  have hall (s : Finset ι) :
      LinearMap.range (HabsMap R (n+1) (subIncl (Y := TopCat.of W) (P.region c s))).hom ≤ M := by
    induction s using Finset.induction_on with
    | empty =>
      letI := P.contractible_region_empty c hc H
      have hz := NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega)
        (TopCat.of (P.region c ∅))
      rintro z ⟨x,rfl⟩
      have hx : x = 0 := by
        exact congrArg (fun f : Habs R (n+1) (TopCat.of (P.region c ∅)) ⟶
          Habs R (n+1) (TopCat.of (P.region c ∅)) => f x) (hz.eq_zero_of_src (𝟙 _))
      rw [hx,map_zero]
      exact M.zero_mem
    | @insert i s hi ih =>
      have hinter : P.region c s ∩ P.region c {i} = P.region c ∅ := by
        rw [P.region_inter c]
        congr 1
        ext j
        simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
        rintro ⟨hj,rfl⟩
        exact hi hj
      letI : ContractibleSpace (P.region c s ∩ P.region c {i} : Set W) := by
        letI := P.contractible_region_empty c hc H
        exact (Homeomorph.setCongr hinter).contractibleSpace
      have hu : P.region c (insert i s) = P.region c s ∪ P.region c {i} := by
        simpa only [Finset.union_singleton] using (P.region_union c hc s {i}).symm
      rw [hu]
      exact homology_range_union_le R (X := TopCat.of W) (P.region c s) (P.region c {i})
        (P.isOpen_region c s) (P.isOpen_region c {i}) n M ih (hsingle i)
  have htop := hall Finset.univ
  rw [P.region_univ c] at htop
  let j : TopCat.of W ⟶ TopCat.of (Set.univ : Set W) :=
    TopCat.ofHom ⟨fun x => ⟨x,Set.mem_univ _⟩, continuous_id.subtype_mk _⟩
  have hj : HabsMap R (n+1) j ≫
      HabsMap R (n+1) (subIncl (Y := TopCat.of W) (Set.univ : Set W)) = 𝟙 _ := by
    rw [← HabsMap_comp]
    convert HabsMap_id R (n+1) (TopCat.of W) using 1
  apply top_unique
  intro z _
  have hz : HabsMap R (n+1) (subIncl (Y := TopCat.of W) (Set.univ : Set W))
      (HabsMap R (n+1) j z) = z :=
    congrArg (fun f => f z) hj
  exact htop ⟨HabsMap R (n+1) j z,hz⟩

omit c hc H in
theorem homology_inclusion_pinch (n : ℕ) (i j : ι) :
    HabsMap R (n+1) (TopCat.ofHom (P.inclusion i)) ≫
      HabsMap R (n+1) (TopCat.ofHom (P.pinch j)) =
      if i = j then 𝟙 _ else 0 := by
  rw [← HabsMap_comp]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    have he : TopCat.ofHom (P.inclusion i) ≫ TopCat.ofHom (P.pinch i) =
        𝟙 (TopCat.of T) := by ext x; exact P.pinch_same i x
    rw [he,HabsMap_id]
  · rw [if_neg h]
    have he : TopCat.ofHom (P.inclusion i) ≫ TopCat.ofHom (P.pinch j) =
        TopCat.ofHom (ContinuousMap.const T P.base) := by
      ext x
      exact P.pinch_other j i h x
    rw [he]
    exact NRR.PrimePowerTopology.HabsMap_const_eq_zero R (n+1) (by omega)
      (X := TopCat.of T) (Y := TopCat.of T) P.base

/-- Sum of the genuine branch maps on the finite direct sum (represented
as a finite product of modules). -/
def homologySumLinear (n : ℕ) :
    (ι → Habs R (n+1) (TopCat.of T)) →ₗ[R] Habs R (n+1) (TopCat.of W) :=
  ∑ i : ι, (HabsMap R (n+1) (TopCat.ofHom (P.inclusion i))).hom.comp (LinearMap.proj i)

omit c hc H in
@[simp] theorem homologySumLinear_apply (n : ℕ) (x : ι → Habs R (n+1) (TopCat.of T)) :
    P.homologySumLinear R n x =
      ∑ i : ι, HabsMap R (n+1) (TopCat.ofHom (P.inclusion i)) (x i) := by
  simp [homologySumLinear]

omit c hc H in
@[simp] theorem homologySumLinear_single (n : ℕ) (i : ι) (x : Habs R (n+1) (TopCat.of T)) :
    P.homologySumLinear R n (Pi.single i x) =
      HabsMap R (n+1) (TopCat.ofHom (P.inclusion i)) x := by
  rw [homologySumLinear_apply]
  simp_rw [Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

omit c hc H in
theorem homologyPinch_sum (n : ℕ) (x : ι → Habs R (n+1) (TopCat.of T)) (i : ι) :
    HabsMap R (n+1) (TopCat.ofHom (P.pinch i)) (P.homologySumLinear R n x) = x i := by
  rw [homologySumLinear_apply,map_sum]
  have ht (j : ι) : HabsMap R (n+1) (TopCat.ofHom (P.pinch i))
      (HabsMap R (n+1) (TopCat.ofHom (P.inclusion j)) (x j)) =
        if j = i then x j else 0 := by
    have hh := congrArg (fun f : Habs R (n+1) (TopCat.of T) ⟶
      Habs R (n+1) (TopCat.of T) => f (x j)) (P.homology_inclusion_pinch R n j i)
    by_cases h : j = i <;> simpa [h] using hh
  simp only [ht,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem surjective_homologySumLinear (n : ℕ) : Function.Surjective (P.homologySumLinear R n) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← P.iSup_range_homologyInclusion_eq_top R c hc H n]
  apply iSup_le
  intro i z hz
  obtain ⟨x,rfl⟩ := hz
  exact ⟨Pi.single i x, P.homologySumLinear_single R n i x⟩

/-- The positive homology of an actual finite wedge is the direct sum of
the positive homologies of its branches. The inverse is the sum of the
actual inclusion maps; coefficients are the actual pinch maps. -/
def homologyEquiv (n : ℕ) :
    (ι → Habs R (n+1) (TopCat.of T)) ≃ₗ[R] Habs R (n+1) (TopCat.of W) :=
  LinearEquiv.ofBijective (P.homologySumLinear R n) ⟨by
    intro x y h
    funext i
    rw [← P.homologyPinch_sum R n x i,← P.homologyPinch_sum R n y i,h],
    P.surjective_homologySumLinear R c hc H n⟩

end FiniteWedgePresentation
end NRR.SingularHomology
