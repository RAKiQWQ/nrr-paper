import NRR.SingularHomologyBMSuspensionUnreduced
import Mathlib.Order.Interval.Set.IsoIoo

/-! The actual compactification obtained by collapsing the infinity arc. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
open Set Topology CategoryTheory Limits AlgebraicTopology unitInterval
open NRR.PrimePowerTopology NRR.SuspensionGeometry
open scoped OnePoint

namespace NRR.SingularHomology
namespace RealSuspension

section OpenEmbeddingCollapse
variable {S Z : Type} [TopologicalSpace S] [TopologicalSpace Z]
variable (i : S → Z) (hi : IsOpenEmbedding i)

private def embeddingCollapseFun (z : Z) : OnePoint S :=
  if h : z ∈ range i then ((Classical.choose h : S) : OnePoint S) else ∞

include hi in
@[simp] private theorem embeddingCollapseFun_image (x : S) :
    embeddingCollapseFun i (i x) = (x : OnePoint S) := by
  unfold embeddingCollapseFun
  rw [dif_pos (mem_range_self x)]
  exact congrArg (fun x : S => (x : OnePoint S))
    (hi.injective (Classical.choose_spec (mem_range_self x)))

private theorem embeddingCollapseFun_eq_infty (z : Z) :
    embeddingCollapseFun i z = ∞ ↔ z ∉ range i := by
  unfold embeddingCollapseFun
  split_ifs with h <;> simp [h]

include hi in
private theorem embeddingCollapseFun_coe_iff (z : Z) (x : S) :
    embeddingCollapseFun i z = (x : OnePoint S) ↔ z = i x := by
  constructor
  · intro h
    by_cases hz : z ∈ range i
    · obtain ⟨y,rfl⟩ := hz
      rw [embeddingCollapseFun_image i hi] at h
      exact congrArg i (OnePoint.coe_injective h)
    · have hn := (embeddingCollapseFun_eq_infty i z).mpr hz
      exact (OnePoint.coe_ne_infty x (h.symm.trans hn)).elim
  · rintro rfl
    exact embeddingCollapseFun_image i hi x

include hi in
private theorem embeddingCollapseFun_continuous [T2Space Z] :
    Continuous (embeddingCollapseFun i) := by
  apply continuous_def.mpr
  intro U hU
  by_cases hp : (∞ : OnePoint S) ∈ U
  · have he : embeddingCollapseFun i ⁻¹' U =
        (i '' (((↑) : S → OnePoint S) ⁻¹' U)ᶜ)ᶜ := by
      ext z
      constructor
      · intro hz ⟨x,hx,he⟩
        subst z
        exact hx (by simpa only [mem_preimage,embeddingCollapseFun_image i hi] using hz)
      · intro hz
        by_cases hr : z ∈ range i
        · obtain ⟨x,rfl⟩ := hr
          change embeddingCollapseFun i (i x) ∈ U
          rw [embeddingCollapseFun_image i hi]
          exact by_contra fun hx => hz ⟨x,hx,rfl⟩
        · change embeddingCollapseFun i z ∈ U
          rw [(embeddingCollapseFun_eq_infty i z).mpr hr]
          exact hp
    rw [he]
    exact (((OnePoint.isOpen_def.mp hU).1 hp).image hi.continuous).isClosed.isOpen_compl
  · have he : embeddingCollapseFun i ⁻¹' U =
        i '' (((↑) : S → OnePoint S) ⁻¹' U) := by
      ext z
      constructor
      · intro hz
        by_cases hr : z ∈ range i
        · obtain ⟨x,rfl⟩ := hr
          exact ⟨x,by simpa only [mem_preimage,embeddingCollapseFun_image i hi] using hz,rfl⟩
        · exact (hp (by simpa [(embeddingCollapseFun_eq_infty i z).mpr hr] using hz)).elim
      · rintro ⟨x,hx,rfl⟩
        simpa only [mem_preimage,embeddingCollapseFun_image i hi] using hx
    rw [he]
    exact hi.isOpenMap _ (OnePoint.isOpen_def.mp hU).2

/-- A compact Hausdorff space with a specified open complement collapses
to the genuine one-point compactification of that complement. -/
def openEmbeddingCollapse [T2Space Z] [CompactSpace Z] [T2Space S]
    [LocallyCompactSpace S] (z₀ : Z) (hz₀ : z₀ ∉ range i) :
    ClosedCollapse ((range i)ᶜ) (∞ : OnePoint S) where
  map := ⟨embeddingCollapseFun i,embeddingCollapseFun_continuous i hi⟩
  quotient := (embeddingCollapseFun_continuous i hi).isClosedMap.isQuotientMap
    (embeddingCollapseFun_continuous i hi) (by
      intro y
      induction y using OnePoint.rec with
      | infty => exact ⟨z₀,(embeddingCollapseFun_eq_infty i z₀).mpr hz₀⟩
      | coe x => exact ⟨i x,embeddingCollapseFun_image i hi x⟩)
  pointFiber := embeddingCollapseFun_eq_infty i
  fiber := by
    intro z w
    constructor
    · intro h
      change embeddingCollapseFun i z = embeddingCollapseFun i w at h
      by_cases hz : z ∈ range i
      · obtain ⟨x,rfl⟩ := hz
        rw [embeddingCollapseFun_image i hi] at h
        exact Or.inl ((embeddingCollapseFun_coe_iff i hi w x).mp h.symm).symm
      · right
        refine ⟨hz,?_⟩
        apply (embeddingCollapseFun_eq_infty i w).mp
        rw [← h]
        exact (embeddingCollapseFun_eq_infty i z).mpr hz
    · rintro (rfl | ⟨hz,hw⟩)
      · rfl
      · exact ((embeddingCollapseFun_eq_infty i z).mpr hz).trans
          ((embeddingCollapseFun_eq_infty i w).mpr hw).symm

include hi in
@[simp] theorem openEmbeddingCollapse_image [T2Space Z] [CompactSpace Z] [T2Space S]
    [LocallyCompactSpace S] (z₀ : Z) (hz₀ : z₀ ∉ range i) (x : S) :
    (openEmbeddingCollapse i hi z₀ hz₀).map (i x) = (x : OnePoint S) :=
  embeddingCollapseFun_image i hi x

end OpenEmbeddingCollapse

/-- Affine identification of `(-1,1)` with the interior suspension levels. -/
def affineLevel : Ioo (-1 : ℝ) 1 ≃ₜ interiorLevels where
  toFun t := ⟨⟨(t.val+1)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩,by
    change 0 < (t.val+1)/2 ∧ (t.val+1)/2 < 1
    constructor <;> linarith [t.property.1,t.property.2]⟩
  invFun t := ⟨2*(t.val : ℝ)-1,by
    have h0 : (0:ℝ) < t.val := t.property.1
    have h1 : (t.val:ℝ) < 1 := t.property.2
    constructor <;> linarith⟩
  left_inv t := by apply Subtype.ext; change 2*((t.val+1)/2)-1=t.val; ring
  right_inv t := by apply Subtype.ext; apply Subtype.ext; change (2*(t.val:ℝ)-1+1)/2=t.val; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def realLevel : ℝ ≃ₜ interiorLevels :=
  (orderIsoIooNegOneOne ℝ).toHomeomorph.trans affineLevel

@[simp] theorem realLevel_coe (r : ℝ) :
    ((realLevel r).val : ℝ) = (r/(1+|r|)+1)/2 := by
  unfold realLevel orderIsoIooNegOneOne
  rfl

theorem realLevel_neg (r : ℝ) : (realLevel (-r)).val = σ (realLevel r).val := by
  apply Subtype.ext
  change ((realLevel (-r)).val : ℝ) = 1-((realLevel r).val : ℝ)
  rw [realLevel_coe,realLevel_coe,abs_neg,neg_div]
  ring

variable {K : Type} [TopologicalSpace K]

def interiorEmbedding : interiorLevels × K → Susp K := fun z =>
  ((Susp.bandCoordinates interiorLevels interiorLevels_open zero_not_interiorLevels
    one_not_interiorLevels).symm z).val

@[simp] theorem interiorEmbedding_apply (z : interiorLevels × K) :
    interiorEmbedding z = Susp.mk (z.1.val,z.2) := rfl

theorem interiorEmbedding_open : IsOpenEmbedding (interiorEmbedding (K := K)) :=
  (interiorLevels_open.preimage Susp.height.continuous).isOpenEmbedding_subtypeVal.comp
    (Susp.bandCoordinates interiorLevels interiorLevels_open zero_not_interiorLevels
      one_not_interiorLevels).symm.isOpenEmbedding

variable {X : Type} [TopologicalSpace X]

/-- The standard open cylinder of the unreduced suspension, omitting the infinity arc. -/
def realEmbedding : X × ℝ → Susp (OnePoint X) := fun z =>
  interiorEmbedding (realLevel z.2,(z.1 : OnePoint X))

@[simp] theorem realEmbedding_apply (z : X × ℝ) :
    realEmbedding z = Susp.mk ((realLevel z.2).val,(z.1 : OnePoint X)) := rfl

theorem realEmbedding_open : IsOpenEmbedding (realEmbedding (X := X)) :=
  interiorEmbedding_open.comp
    ((realLevel.isOpenEmbedding.prodMap OnePoint.isOpenEmbedding_coe).comp
      (Homeomorph.prodComm X ℝ).isOpenEmbedding)

theorem range_realEmbedding : range (realEmbedding (X := X)) = (Susp.arc (∞ : OnePoint X))ᶜ := by
  ext z
  constructor
  · rintro ⟨⟨x,r⟩,rfl⟩
    change Susp.mk ((realLevel r).val,(x : OnePoint X)) ∉ Susp.arc (∞ : OnePoint X)
    rw [Susp.mem_arc_mk]
    rintro (ht | ht | hx)
    · exact zero_not_interiorLevels (ht ▸ (realLevel r).property)
    · exact one_not_interiorLevels (ht ▸ (realLevel r).property)
    · exact OnePoint.coe_ne_infty x hx
  · intro hz
    obtain ⟨⟨t,x⟩,rfl⟩ := Susp.mk_surjective z
    have hh := (Susp.mem_arc_mk (∞ : OnePoint X) x t).not.mp hz
    have ht0 : t ≠ 0 := fun h => hh (Or.inl h)
    have ht1 : t ≠ 1 := fun h => hh (Or.inr (Or.inl h))
    have hxinfty : x ≠ ∞ := fun h => hh (Or.inr (Or.inr h))
    induction x using OnePoint.rec with
    | infty => exact (hxinfty rfl).elim
    | coe x =>
      let u : interiorLevels := ⟨t,unitInterval.pos_iff_ne_zero.mpr ht0,
        unitInterval.lt_one_iff_ne_one.mpr ht1⟩
      refine ⟨(x,realLevel.symm u),?_⟩
      change Susp.mk ((realLevel (realLevel.symm u)).val,(x : OnePoint X)) =
        Susp.mk (t,(x : OnePoint X))
      rw [realLevel.apply_symm_apply]

theorem south_not_range_realEmbedding :
    Susp.mk (0,(∞ : OnePoint X)) ∉ range (realEmbedding (X := X)) := by
  rw [range_realEmbedding]
  exact not_not.mpr ⟨0,rfl⟩

variable [T2Space X] [LocallyCompactSpace X]

private def cylinderCollapse :
    ClosedCollapse ((range (realEmbedding (X := X)))ᶜ) (∞ : OnePoint (X × ℝ)) :=
  openEmbeddingCollapse realEmbedding realEmbedding_open (Susp.mk (0,∞))
    south_not_range_realEmbedding

/-- The quotient identifies exactly the arc above infinity, and the complement is `X × ℝ`. -/
def collapse : ClosedCollapse (Susp.arc (∞ : OnePoint X)) (∞ : OnePoint (X × ℝ)) where
  map := cylinderCollapse.map
  quotient := cylinderCollapse.quotient
  pointFiber z := by
    rw [cylinderCollapse.pointFiber,range_realEmbedding,compl_compl]
  fiber z w := by
    rw [cylinderCollapse.fiber,range_realEmbedding,compl_compl]

@[simp] theorem collapse_realEmbedding (z : X × ℝ) :
    (collapse (X := X)).map (realEmbedding z) = (z : OnePoint (X × ℝ)) :=
  openEmbeddingCollapse_image realEmbedding realEmbedding_open (Susp.mk (0,∞))
    south_not_range_realEmbedding z

@[simp] theorem collapse_arc (t : I) :
    (collapse (X := X)).map (Susp.mk (t,∞)) = ∞ :=
  (collapse.pointFiber _).mpr ⟨t,rfl⟩

/-- Geometric real suspension, constructed from the actual good neighborhood of infinity. -/
def model (G : PointGoodNeighborhood (OnePoint X) ∞) :
    CollapsedBMSuspension X (Susp (OnePoint X)) where
  presentation := cover
  arc := Susp.arc ∞
  arc_contractible := Susp.arc_contractible ∞
  collapse := collapse
  neighborhood := SuspensionArc.neighborhood G.neighborhood
  neighborhood_open := SuspensionArc.neighborhood_open _ G.isOpen
  deformation := SuspensionArc.deformation G

end RealSuspension
end NRR.SingularHomology
