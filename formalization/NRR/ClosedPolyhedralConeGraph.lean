import NRR.ClosedPolyhedralCone
import Mathlib.Topology.Order.Lattice

/-! A graph chart for the finite boundary of a polyhedral cone. Projection
along a strictly positive direction fixes every boundary point in the
chosen transverse hyperplane. -/

noncomputable section
open Set Topology Filter
open scoped OnePoint

namespace NRR.ClosedPolyhedralCone

variable {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] [Nonempty J]
variable (L : J → E →L[ℝ] ℝ) (v : E)

def finiteBoundary : Set E := {x | x ∈ carrier L ∧ x ∉ strict L}

def graphThreshold (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => -L j x / L j v)

theorem continuous_graphThreshold : Continuous (graphThreshold L v) := by
  apply Continuous.finset_sup'_apply
  intro j _
  exact (L j).continuous.neg.div_const _

variable {v}

theorem graphThreshold_mem_finiteBoundary (hv : ∀ j, 0 < L j v) (x : E) :
    x + graphThreshold L v x • v ∈ finiteBoundary L := by
  constructor
  · intro j
    have h := Finset.le_sup' (f := fun j => -L j x / L j v)
      (Finset.mem_univ j)
    change -L j x / L j v ≤ graphThreshold L v x at h
    have hm := (div_le_iff₀ (hv j)).mp h
    simp only [map_add, map_smul, smul_eq_mul]
    linarith
  · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => -L j x / L j v)
    intro hs
    have he : graphThreshold L v x * L j v = -L j x := by
      rw [graphThreshold, hj]
      exact div_mul_cancel₀ _ (hv j).ne'
    have hp := hs j
    simp only [map_add, map_smul, smul_eq_mul] at hp
    linarith

theorem graphThreshold_of_finiteBoundary (hv : ∀ j, 0 < L j v) (x : E) (t : ℝ)
    (hx : x+t • v ∈ finiteBoundary L) : graphThreshold L v x = t := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    apply (div_le_iff₀ (hv j)).mpr
    have h := hx.1 j
    simp only [map_add, map_smul, smul_eq_mul] at h
    linarith
  · obtain ⟨j,hj⟩ := not_forall.mp hx.2
    have h := Finset.le_sup' (f := fun j => -L j x / L j v)
      (Finset.mem_univ j)
    change -L j x / L j v ≤ graphThreshold L v x at h
    apply le_trans _ h
    apply (le_div_iff₀ (hv j)).mpr
    simp only [map_add, map_smul, smul_eq_mul, not_lt] at hj
    linarith

/-- Projection of the polyhedral boundary onto a transverse hyperplane.
The inverse is the graph of the finite maximum of its linear inequalities. -/
def finiteBoundaryGraphHomeomorph (hv : ∀ j, 0 < L j v)
    (K : E →L[ℝ] ℝ) (hKv : K v = 1) :
    LinearMap.ker K ≃ₜ finiteBoundary L := by
  have hker (y : finiteBoundary L) : K (y.val-K y.val • v) = 0 := by
    change K (y.val-K y.val • v) = 0
    simp only [map_sub, map_smul, hKv, smul_eq_mul, mul_one, sub_self]
  refine {
    toFun := fun x => ⟨x.val+graphThreshold L v x.val • v,
      graphThreshold_mem_finiteBoundary L hv x.val⟩
    invFun := fun y => ⟨y.val-K y.val • v,hker y⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    have hx : K x.val = 0 := x.property
    simp only [map_add, map_smul, hx, hKv, smul_eq_mul, mul_one, zero_add]
    exact add_sub_cancel_right _ _
  · intro y
    apply Subtype.ext
    have he : (y.val-K y.val • v)+K y.val • v = y.val := sub_add_cancel _ _
    have ht := graphThreshold_of_finiteBoundary L hv
      (y.val-K y.val • v) (K y.val) (he.symm ▸ y.property)
    change (y.val-K y.val • v)+graphThreshold L v (y.val-K y.val • v) • v = y.val
    rw [ht]
    exact he
  · exact (continuous_subtype_val.add
    (((continuous_graphThreshold L v).comp continuous_subtype_val).smul
      continuous_const)).subtype_mk _
  · exact (continuous_subtype_val.sub
    (((K.continuous).comp continuous_subtype_val).smul continuous_const)).subtype_mk _

@[simp] theorem finiteBoundaryGraphHomeomorph_symm_apply
    (hv : ∀ j, 0 < L j v)
    (K : E →L[ℝ] ℝ) (hKv : K v = 1) (y : finiteBoundary L) :
    ((finiteBoundaryGraphHomeomorph L hv K hKv).symm y).val =
      y.val-K y.val • v := rfl

theorem finiteBoundaryGraphHomeomorph_apply_of_boundary
    (hv : ∀ j, 0 < L j v)
    (K : E →L[ℝ] ℝ) (hKv : K v = 1) (x : LinearMap.ker K)
    (hx : x.val ∈ finiteBoundary L) :
    ((finiteBoundaryGraphHomeomorph L hv K hKv) x).val = x.val := by
  have ht := graphThreshold_of_finiteBoundary L hv x.val 0 (by simpa using hx)
  change x.val+graphThreshold L v x.val • v = x.val
  rw [ht, zero_smul, add_zero]

theorem isClosed_finiteBoundary : IsClosed (finiteBoundary L) :=
  (isClosed_carrier L).inter (by
    change IsClosed (strict L)ᶜ
    apply IsOpen.isClosed_compl
    simp only [strict, setOf_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (L j).continuous)

def finiteBoundaryInCarrier : finiteBoundary L → carrier L :=
  fun x => ⟨x.val,x.property.1⟩

theorem isClosedEmbedding_finiteBoundaryInCarrier :
    IsClosedEmbedding (finiteBoundaryInCarrier L) := by
  apply ((isClosed_carrier L).isClosedEmbedding_subtypeVal.of_comp_iff).mp
  exact (isClosed_finiteBoundary L).isClosedEmbedding_subtypeVal

theorem finiteBoundaryCompactification_mem (x : OnePoint (finiteBoundary L)) :
    OnePoint.map (finiteBoundaryInCarrier L) x ∈ compactifiedBoundary L := by
  induction x using OnePoint.rec with
  | infty => exact infty_mem_compactifiedBoundary L
  | coe x => exact (coe_mem_compactifiedBoundary_iff L _).mpr x.property.2

def finiteBoundaryCompactificationMap :
    C(OnePoint (finiteBoundary L), compactifiedBoundary L) := by
  refine ⟨fun x => ⟨OnePoint.map (finiteBoundaryInCarrier L) x,
    finiteBoundaryCompactification_mem L x⟩, ?_⟩
  apply Continuous.subtype_mk
  apply OnePoint.continuous_map (isClosedEmbedding_finiteBoundaryInCarrier L).continuous
  rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
  exact (isClosedEmbedding_finiteBoundaryInCarrier L).tendsto_cocompact

theorem injective_finiteBoundaryCompactificationMap :
    Function.Injective (finiteBoundaryCompactificationMap L) := by
  intro x y h
  apply Option.map_injective _ (congrArg Subtype.val h)
  intro a b hab
  exact (isClosedEmbedding_finiteBoundaryInCarrier L).injective hab

theorem surjective_finiteBoundaryCompactificationMap :
    Function.Surjective (finiteBoundaryCompactificationMap L) := by
  rintro ⟨x,hx⟩
  induction x using OnePoint.rec with
  | infty => exact ⟨∞,rfl⟩
  | coe x =>
      have hn := (coe_mem_compactifiedBoundary_iff L x).mp hx
      exact ⟨((⟨x.val,x.property,hn⟩ : finiteBoundary L) : OnePoint (finiteBoundary L)),rfl⟩

/-- The compactified finite graph is exactly the actual compactified
polyhedral boundary, including its original point at infinity. -/
def finiteBoundaryCompactificationHomeomorph [FiniteDimensional ℝ E] :
    OnePoint (finiteBoundary L) ≃ₜ compactifiedBoundary L := by
  letI : LocallyCompactSpace (carrier L) := (isClosed_carrier L).locallyCompactSpace
  exact ((finiteBoundaryCompactificationMap L).continuous.isClosedEmbedding
    (injective_finiteBoundaryCompactificationMap L)).isEmbedding.toHomeomorphOfSurjective
      (surjective_finiteBoundaryCompactificationMap L)

@[simp] theorem finiteBoundaryCompactificationHomeomorph_apply
    [FiniteDimensional ℝ E] (x : OnePoint (finiteBoundary L)) :
    finiteBoundaryCompactificationHomeomorph L x = finiteBoundaryCompactificationMap L x := rfl

end NRR.ClosedPolyhedralCone
