import NRR.SingularHomologyClosedCollapse
import NRR.SingularHomologyFiniteWedge

/-! Neighborhood deformations for genuine finite disk attachments.
The collar is obtained by removing compact half-radius cell cores and
descending the radial deformation on the remaining annuli. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology Metric CategoryTheory Limits

namespace NRR.SingularHomology

abbrev CellDisk (V : Type) [NormedAddCommGroup V] := closedBall (0 : V) 1
abbrev CellAnnulus (V : Type) [NormedAddCommGroup V] :=
  {q : CellDisk V // (1/2 : ℝ) < ‖q.val‖}

def sumSetHomeomorph {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    (S : Set (Z ⊕ W)) :
    (Sum.inl ⁻¹' S : Set Z) ⊕ (Sum.inr ⁻¹' S : Set W) ≃ₜ S := by
  let e : (Sum.inl ⁻¹' S : Set Z) ⊕ (Sum.inr ⁻¹' S : Set W) ≃ S := {
    toFun := Sum.elim (fun a => ⟨Sum.inl a.val,a.property⟩)
      (fun b => ⟨Sum.inr b.val,b.property⟩)
    invFun := fun c => match c with
      | ⟨Sum.inl a,ha⟩ => Sum.inl ⟨a,ha⟩
      | ⟨Sum.inr b,hb⟩ => Sum.inr ⟨b,hb⟩
    left_inv := by rintro (a | b) <;> rfl
    right_inv := by rintro ⟨a | b,h⟩ <;> rfl }
  exact e.toHomeomorphOfContinuousOpen
    (((continuous_inl.comp continuous_subtype_val).subtype_mk _).sumElim
      ((continuous_inr.comp continuous_subtype_val).subtype_mk _))
    ((IsOpenEmbedding.inl.restrictPreimage S).isOpenMap.sumElim
      (IsOpenEmbedding.inr.restrictPreimage S).isOpenMap)

def sigmaCongrRightHomeomorph {J : Type} {Z W : J → Type}
    [∀ j,TopologicalSpace (Z j)] [∀ j,TopologicalSpace (W j)]
    (e : ∀ j,Z j ≃ₜ W j) : (Σ j,Z j) ≃ₜ (Σ j,W j) where
  toEquiv := Equiv.sigmaCongrRight fun j => (e j).toEquiv
  continuous_toFun := continuous_sigma fun j => continuous_sigmaMk.comp (e j).continuous
  continuous_invFun := continuous_sigma fun j => continuous_sigmaMk.comp (e j).symm.continuous

def quotientCylinderDesc {S T Z : Type} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace Z] (q : C(S,T)) (hq : IsQuotientMap q)
    (F : C(unitInterval × S,Z))
    (hf : ∀ t x y, q x = q y → F (t,x) = F (t,y)) : C(unitInterval × T,Z) where
  toFun z := F (z.1,Function.surjInv hq.surjective z.2)
  continuous_toFun := by
    apply hq.continuous_lift_prod_right
    have he : (fun z : unitInterval × S =>
        F (z.1,Function.surjInv hq.surjective (q z.2))) = F := by
      funext z
      exact hf z.1 _ _ (Function.surjInv_eq hq.surjective _)
    rw [he]
    exact F.continuous

@[simp] theorem quotientCylinderDesc_apply {S T Z : Type}
    [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace Z]
    (q : C(S,T)) (hq : IsQuotientMap q) (F : C(unitInterval × S,Z))
    (hf : ∀ t x y, q x = q y → F (t,x) = F (t,y)) (t : unitInterval) (x : S) :
    quotientCylinderDesc q hq F hf (t,q x) = F (t,x) :=
  hf t _ _ (Function.surjInv_eq hq.surjective _)

section Radial
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def annularRadialValue (t : unitInterval) (q : CellAnnulus V) : V :=
  (((1-(t : ℝ))/‖q.val.val‖)+(t : ℝ)) • q.val.val

theorem norm_annularRadialValue (t : unitInterval) (q : CellAnnulus V) :
    ‖annularRadialValue t q‖ = 1-(t : ℝ)+(t : ℝ)*‖q.val.val‖ := by
  have hpos : 0 < ‖q.val.val‖ := lt_trans (by norm_num) q.property
  have hcoef : 0 ≤ ((1-(t : ℝ))/‖q.val.val‖)+(t : ℝ) :=
    add_nonneg (div_nonneg (sub_nonneg.mpr t.property.2) (norm_nonneg _)) t.property.1
  rw [annularRadialValue,norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoef,add_mul,
    div_mul_cancel₀ _ hpos.ne']

def annularRadial : C(unitInterval × CellAnnulus V,CellAnnulus V) where
  toFun z := ⟨⟨annularRadialValue z.1 z.2,by
    rw [mem_closedBall_zero_iff,norm_annularRadialValue]
    have hnorm := mem_closedBall_zero_iff.mp z.2.val.property
    nlinarith [mul_nonneg z.1.property.1 (sub_nonneg.mpr hnorm)]⟩,by
    rw [norm_annularRadialValue]
    have hnorm := mem_closedBall_zero_iff.mp z.2.val.property
    have hprod := mul_nonneg (sub_nonneg.mpr z.1.property.2) (sub_nonneg.mpr hnorm)
    linarith [z.2.property]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have ht : Continuous (fun z : unitInterval × CellAnnulus V => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hq : Continuous (fun z : unitInterval × CellAnnulus V => z.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact (((continuous_const.sub ht).div hq.norm (fun z =>
      (lt_trans (by norm_num) z.2.property).ne')).add ht).smul hq

@[simp] theorem annularRadial_one (q : CellAnnulus V) : annularRadial (1,q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  simp [annularRadial,annularRadialValue]

theorem annularRadial_boundary (t : unitInterval) (q : CellAnnulus V)
    (hq : ‖q.val.val‖ = 1) : annularRadial (t,q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [annularRadial,ContinuousMap.coe_mk,annularRadialValue,hq,div_one,
    sub_add_cancel,one_smul]

@[simp] theorem annularRadial_zero_norm (q : CellAnnulus V) :
    ‖(annularRadial (0,q)).val.val‖ = 1 := by
  change ‖annularRadialValue 0 q‖ = 1
  rw [norm_annularRadialValue]
  simp

end Radial

section Topology
variable {ι V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
  [Finite ι] {A : Set X} [CompactSpace A]

/-- A finite family of actual disk characteristic maps. The interior
uniqueness is a geometric input, and all boundary identifications take
place in the given lower subspace. -/
structure FiniteCellAttachment (ι V X : Type) [NormedAddCommGroup V]
    [TopologicalSpace X] (A : Set X) where
  characteristic : ι → C(CellDisk V,X)
  boundary : ∀ i q, characteristic i q ∈ A ↔ ‖q.val‖ = 1
  interior_unique : ∀ i j q r, ‖q.val‖ < 1 → characteristic i q = characteristic j r →
    i = j ∧ q = r
  cover : ∀ x : X, x ∈ A ∨ ∃ i q, characteristic i q = x

namespace FiniteCellAttachment
variable (P : FiniteCellAttachment ι V X A)

def projection : C(A ⊕ (Σ _ : ι,CellDisk V),X) :=
  ⟨Sum.elim Subtype.val (fun z => P.characteristic z.1 z.2),
    continuous_subtype_val.sumElim (continuous_sigma fun i => (P.characteristic i).continuous)⟩

theorem projection_surjective : Function.Surjective P.projection := by
  intro x
  rcases P.cover x with hx | ⟨i,q,hq⟩
  · exact ⟨Sum.inl ⟨x,hx⟩,rfl⟩
  · exact ⟨Sum.inr ⟨i,q⟩,hq⟩

theorem quotient_projection : IsQuotientMap P.projection :=
  P.projection.continuous.isClosedMap.isQuotientMap P.projection.continuous P.projection_surjective

def corePoint (_P : FiniteCellAttachment ι V X A)
    (q : closedBall (0 : V) (1/2)) : CellDisk V :=
  ⟨q.val,closedBall_subset_closedBall (by norm_num) q.property⟩

def coreMap : C((Σ _ : ι,closedBall (0 : V) (1/2)),X) :=
  ⟨fun z => P.characteristic z.1 (P.corePoint z.2),continuous_sigma fun i =>
    (P.characteristic i).continuous.comp (continuous_subtype_val.subtype_mk _)⟩

def neighborhood : Set X := (range P.coreMap)ᶜ

theorem isOpen_neighborhood : IsOpen P.neighborhood :=
  (isCompact_range P.coreMap.continuous).isClosed.isOpen_compl

theorem subset_neighborhood : A ⊆ P.neighborhood := by
  intro x hx ⟨⟨i,q⟩,hq⟩
  have he : ‖q.val‖ = 1 := (P.boundary i (P.corePoint q)).mp (hq.symm ▸ hx)
  have hl : ‖q.val‖ ≤ (1/2 : ℝ) := mem_closedBall_zero_iff.mp q.property
  linarith

theorem characteristic_mem_neighborhood (i : ι) (q : CellDisk V) :
    P.characteristic i q ∈ P.neighborhood ↔ (1/2 : ℝ) < ‖q.val‖ := by
  constructor
  · intro hq
    by_contra hn
    have hp : q.val ∈ closedBall (0 : V) (1/2) :=
      mem_closedBall_zero_iff.mpr (le_of_not_gt hn)
    exact hq ⟨⟨i,⟨q.val,hp⟩⟩,rfl⟩
  · intro hq ⟨⟨j,r⟩,he⟩
    have hr : ‖r.val‖ ≤ (1/2 : ℝ) := mem_closedBall_zero_iff.mp r.property
    have ht : ‖(P.corePoint r).val‖ < 1 := by change ‖r.val‖ < 1; linarith
    have hh := (P.interior_unique j i (P.corePoint r) q ht he).2
    have hn := congrArg (fun a : CellDisk V => ‖a.val‖) hh
    change ‖r.val‖ = ‖q.val‖ at hn
    linarith

def neighborhoodProjection : C(A ⊕ (Σ _ : ι,CellAnnulus V),P.neighborhood) :=
  ⟨Sum.elim (fun a => ⟨a.val,P.subset_neighborhood a.property⟩)
    (fun z => ⟨P.characteristic z.1 z.2.val,
      (P.characteristic_mem_neighborhood z.1 z.2.val).mpr z.2.property⟩),
    (continuous_subtype_val.subtype_mk _).sumElim (continuous_sigma fun i =>
      ((P.characteristic i).continuous.comp continuous_subtype_val).subtype_mk _)⟩

def neighborhoodBaseHomeomorph : A ≃ₜ
    (Sum.inl ⁻¹' (P.projection ⁻¹' P.neighborhood) : Set A) where
  toFun a := ⟨a,P.subset_neighborhood a.property⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

def neighborhoodSourceHomeomorph :
    (A ⊕ (Σ _ : ι,CellAnnulus V)) ≃ₜ (P.projection ⁻¹' P.neighborhood) := by
  let e : (Σ _ : ι,CellAnnulus V) ≃ₜ
      (Sum.inr ⁻¹' (P.projection ⁻¹' P.neighborhood) : Set (Σ _ : ι,CellDisk V)) :=
    (sigmaCongrRightHomeomorph fun i => Homeomorph.setCongr (by
      ext q
      exact (P.characteristic_mem_neighborhood i q).symm)).trans
        (sigmaSetHomeomorph (Sum.inr ⁻¹' (P.projection ⁻¹' P.neighborhood)))
  exact (P.neighborhoodBaseHomeomorph.sumCongr e).trans
    (sumSetHomeomorph (P.projection ⁻¹' P.neighborhood))

theorem quotient_neighborhoodProjection : IsQuotientMap P.neighborhoodProjection := by
  have he : P.neighborhoodProjection =
      (P.neighborhood.restrictPreimage P.projection) ∘ P.neighborhoodSourceHomeomorph := by
    funext z
    rcases z with a | ⟨i,q⟩ <;> rfl
  rw [he]
  exact (P.quotient_projection.restrictPreimage_isOpen P.isOpen_neighborhood).comp
    P.neighborhoodSourceHomeomorph.isQuotientMap

def cellAnnularHomotopy (i : ι) : C(unitInterval × CellAnnulus V,P.neighborhood) :=
  ⟨fun z => ⟨P.characteristic i (annularRadial z).val,
      (P.characteristic_mem_neighborhood i _).mpr (annularRadial z).property⟩,
    ((P.characteristic i).continuous.comp
      (continuous_subtype_val.comp annularRadial.continuous)).subtype_mk _⟩

def sigmaAnnularHomotopy : C(unitInterval × (Σ _ : ι,CellAnnulus V),P.neighborhood) :=
  (⟨fun z : (Σ _ : ι,CellAnnulus V × unitInterval) =>
      P.cellAnnularHomotopy z.1 (z.2.2,z.2.1),
    continuous_sigma fun i => (P.cellAnnularHomotopy i).continuous.comp continuous_swap⟩ :
      C((Σ _ : ι,CellAnnulus V × unitInterval),P.neighborhood)).comp
    ⟨(Homeomorph.prodComm unitInterval (Σ _ : ι,CellAnnulus V)).trans
        (Homeomorph.sigmaProdDistrib (X := fun _ : ι => CellAnnulus V) (Y := unitInterval)),
      ((Homeomorph.prodComm unitInterval (Σ _ : ι,CellAnnulus V)).trans
        (Homeomorph.sigmaProdDistrib (X := fun _ : ι => CellAnnulus V) (Y := unitInterval))).continuous⟩

def sourceNeighborhoodHomotopy :
    C(unitInterval × (A ⊕ (Σ _ : ι,CellAnnulus V)),P.neighborhood) :=
  (⟨Sum.elim (fun z : unitInterval × A => ⟨z.2.val,P.subset_neighborhood z.2.property⟩)
      P.sigmaAnnularHomotopy,
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _).sumElim
      P.sigmaAnnularHomotopy.continuous⟩ :
    C((unitInterval × A) ⊕ (unitInterval × (Σ _ : ι,CellAnnulus V)),P.neighborhood)).comp
      ⟨Homeomorph.prodSumDistrib (X := unitInterval) (Y := A) (Z := Σ _ : ι,CellAnnulus V),
        (Homeomorph.prodSumDistrib (X := unitInterval) (Y := A)
          (Z := Σ _ : ι,CellAnnulus V)).continuous⟩

@[simp] theorem sourceNeighborhoodHomotopy_base (t : unitInterval) (a : A) :
    P.sourceNeighborhoodHomotopy (t,Sum.inl a) =
      (⟨a.val,P.subset_neighborhood a.property⟩ : P.neighborhood) := rfl

@[simp] theorem sourceNeighborhoodHomotopy_cell (t : unitInterval) (i : ι) (q : CellAnnulus V) :
    P.sourceNeighborhoodHomotopy (t,Sum.inr ⟨i,q⟩) = P.cellAnnularHomotopy i (t,q) := rfl

theorem sourceNeighborhoodHomotopy_fiber (t : unitInterval)
    (x y : A ⊕ (Σ _ : ι,CellAnnulus V))
    (hxy : P.neighborhoodProjection x = P.neighborhoodProjection y) :
    P.sourceNeighborhoodHomotopy (t,x) = P.sourceNeighborhoodHomotopy (t,y) := by
  have he := congrArg Subtype.val hxy
  rcases x with a | ⟨i,q⟩ <;> rcases y with b | ⟨j,r⟩
  · exact Subtype.ext he
  · change a.val = P.characteristic j r.val at he
    have hb : ‖r.val.val‖ = 1 := (P.boundary j r.val).mp (he ▸ a.property)
    apply Subtype.ext
    change a.val = P.characteristic j (annularRadial (t,r)).val
    rw [annularRadial_boundary t r hb]
    exact he
  · change P.characteristic i q.val = b.val at he
    have ha : ‖q.val.val‖ = 1 := (P.boundary i q.val).mp (he.symm ▸ b.property)
    apply Subtype.ext
    change P.characteristic i (annularRadial (t,q)).val = b.val
    rw [annularRadial_boundary t q ha]
    exact he
  · change P.characteristic i q.val = P.characteristic j r.val at he
    by_cases hq : ‖q.val.val‖ < 1
    · obtain ⟨hij,hqr⟩ := P.interior_unique i j q.val r.val hq he
      subst j
      have hqr' : q = r := Subtype.ext hqr
      subst r
      rfl
    · have hq' : ‖q.val.val‖ = 1 :=
        le_antisymm (mem_closedBall_zero_iff.mp q.val.property) (le_of_not_gt hq)
      have hr' : ‖r.val.val‖ = 1 := (P.boundary j r.val).mp
        (he ▸ (P.boundary i q.val).mpr hq')
      apply Subtype.ext
      change P.characteristic i (annularRadial (t,q)).val =
        P.characteristic j (annularRadial (t,r)).val
      rw [annularRadial_boundary t q hq',annularRadial_boundary t r hr']
      exact he

def neighborhoodHomotopy : C(unitInterval × P.neighborhood,P.neighborhood) :=
  quotientCylinderDesc P.neighborhoodProjection P.quotient_neighborhoodProjection
    P.sourceNeighborhoodHomotopy P.sourceNeighborhoodHomotopy_fiber

@[simp] theorem neighborhoodHomotopy_lift (t : unitInterval)
    (x : A ⊕ (Σ _ : ι,CellAnnulus V)) :
    P.neighborhoodHomotopy (t,P.neighborhoodProjection x) =
      P.sourceNeighborhoodHomotopy (t,x) :=
  quotientCylinderDesc_apply _ _ _ _ _ _

theorem neighborhoodHomotopy_zero_mem (x : P.neighborhood) :
    (P.neighborhoodHomotopy (0,x)).val ∈ A := by
  obtain ⟨a,rfl⟩ := P.quotient_neighborhoodProjection.surjective x
  rw [P.neighborhoodHomotopy_lift]
  rcases a with a | ⟨i,q⟩
  · exact a.property
  · exact (P.boundary i _).mpr (annularRadial_zero_norm q)

@[simp] theorem neighborhoodHomotopy_one (x : P.neighborhood) :
    P.neighborhoodHomotopy (1,x) = x := by
  obtain ⟨a,rfl⟩ := P.quotient_neighborhoodProjection.surjective x
  rw [P.neighborhoodHomotopy_lift]
  rcases a with a | ⟨i,q⟩
  · rfl
  · apply Subtype.ext
    change P.characteristic i (annularRadial (1,q)).val = P.characteristic i q.val
    rw [annularRadial_one]

/-- Finite compact disk attachments are good pairs by an explicit
neighborhood deformation which is jointly continuous at every attached
boundary point. -/
def neighborhoodDeformation : NeighborhoodDeformation A P.neighborhood where
  subset := P.subset_neighborhood
  retract := ⟨fun x => ⟨(P.neighborhoodHomotopy (0,x)).val,
      P.neighborhoodHomotopy_zero_mem x⟩,
    (continuous_subtype_val.comp (P.neighborhoodHomotopy.continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  retraction a := by
    exact Subtype.ext (congrArg (fun x : P.neighborhood => x.val)
      (P.neighborhoodHomotopy_lift 0 (Sum.inl a)))
  homotopy := {
    toFun := P.neighborhoodHomotopy
    continuous_toFun := P.neighborhoodHomotopy.continuous
    map_zero_left _ := rfl
    map_one_left := P.neighborhoodHomotopy_one }
  preserve t a := by
    change (P.neighborhoodHomotopy (t,P.neighborhoodProjection (Sum.inl a))).val ∈ A
    rw [P.neighborhoodHomotopy_lift]
    exact a.property

end FiniteCellAttachment
end Topology

end NRR.SingularHomology
