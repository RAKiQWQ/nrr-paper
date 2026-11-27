import NRR.PrimePowerTopologyNextStratum
import NRR.PrimePowerTopologyTwoColumnCells

/-! Each actual two-column chart is an open cell in the first nonminimal
Fuks level. Its openness follows from strict column separation inside the
proved two-valued stratum, rather than an assumed cell decomposition. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

def twoColumnCondition {d n : ℕ} (S : Finset (Fin n)) : Set (Configuration (d+2) n) :=
  {x | (∀ i j, i ∈ S → j ∉ S → nextFuksColumn x i < nextFuksColumn x j) ∧
    (fun i => (horizontalHeight (d+1) (x.val i)).2) ∈ twoColumnHeights S}

theorem continuous_nextFuksColumn {d n : ℕ} (i : Fin n) :
    Continuous (fun x : Configuration (d+2) n => nextFuksColumn x i) := by
  unfold nextFuksColumn
  exact (PiLp.continuous_apply 2 (fun _ : Fin (d+1) => ℝ) (Fin.last d)).comp
    (continuous_fst.comp ((horizontalHeight (d+1)).continuous.comp
      ((continuous_apply i).comp continuous_subtype_val)))

theorem isOpen_twoColumnCondition {d n : ℕ} (S : Finset (Fin n)) :
    IsOpen (twoColumnCondition (d := d) S) := by
  have repr : twoColumnCondition (d := d) S =
      (⋂ i : Fin n, ⋂ j : Fin n,
        {x | i ∈ S ∧ j ∉ S → nextFuksColumn x i < nextFuksColumn x j}) ∩
      (fun x : Configuration (d+2) n =>
        fun i => (horizontalHeight (d+1) (x.val i)).2) ⁻¹' twoColumnHeights S := by
    ext x
    simp only [twoColumnCondition, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage]
    aesop
  rw [repr]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    by_cases h : i ∈ S ∧ j ∉ S
    · simpa only [h.1, h.2, not_false_eq_true, and_self, true_implies] using
        isOpen_lt (continuous_nextFuksColumn i) (continuous_nextFuksColumn j)
    · simp [h]
  · apply (isOpen_twoColumnHeights S).preimage
    apply continuous_pi
    intro i
    exact continuous_snd.comp ((horizontalHeight (d+1)).continuous.comp
      ((continuous_apply i).comp continuous_subtype_val))

theorem twoColumnMap_mem_condition {d n : ℕ} (S : Finset (Fin n))
    (p : twoColumnDomain (d := d) S) : twoColumnMap S p ∈ twoColumnCondition S := by
  refine ⟨?_, ?_⟩
  · intro i j hi hj
    rw [twoColumnMap_column, twoColumnMap_column, if_pos hi, if_neg hj]
    linarith [p.property.1]
  · simpa only [twoColumnMap, twoColumnAmbient, ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply] using p.property.2

private theorem exists_notMem_of_proper {n : ℕ} (S : Finset (Fin n))
    (hproper : S ≠ Finset.univ) : ∃ j : Fin n, j ∉ S := by
  classical
  by_contra! hall
  exact hproper (Finset.eq_univ_of_forall hall)

theorem twoColumnCondition_not_vertical {d n : ℕ} (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (x : Configuration (d+2) n) (hx : x ∈ twoColumnCondition S) :
    x ∉ verticalSet (d+1) n := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨j, hj⟩ := exists_notMem_of_proper S hproper
  intro hv
  have he := congrArg (fun v : Space (d+1) => v (Fin.last d)) (hv i j)
  exact (hx.1 i j hi hj).ne he

/-- In the true next level, strict ordered column inequalities are exactly
the image of the given chart, with the original labels unchanged. -/
theorem exists_twoColumnMap_eq_of_condition {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (x : Configuration (d+2) n) (hx : x ∈ fuksLevel (d+1) n (d+2))
    (hcond : x ∈ twoColumnCondition S) :
    ∃ p : twoColumnDomain (d := d) S, twoColumnMap S p = x := by
  classical
  obtain ⟨iL, hiL⟩ := hne
  obtain ⟨iR, hiR⟩ := exists_notMem_of_proper S hproper
  obtain ⟨a, b, hab, hvalues⟩ := nextFuks_two_column_values x hx
    (twoColumnCondition_not_vertical S ⟨iL, hiL⟩ hproper x hcond)
  have values (i : Fin n) : nextFuksColumn x i = a ∨ nextFuksColumn x i = b := by
    have hm : nextFuksColumn x i ∈ Finset.univ.image (nextFuksColumn x) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa only [hvalues, Finset.mem_insert, Finset.mem_singleton] using hm
  have left (i : Fin n) (hi : i ∈ S) : nextFuksColumn x i = a := by
    rcases values i with hi' | hi'
    · exact hi'
    · have hlt := hcond.1 i iR hi hiR
      rcases values iR with hr | hr <;> linarith
  have right (i : Fin n) (hi : i ∉ S) : nextFuksColumn x i = b := by
    rcases values i with hi' | hi'
    · have hlt := hcond.1 iL i hiL hi
      rcases values iL with hl | hl <;> linarith
    · exact hi'
  let v : Space d := (horizontalHeight d ((horizontalHeight (d+1) (x.val 0)).1)).1
  let p : TwoColumnAmbientParameters d n :=
    (((v, a), fun i => (horizontalHeight (d+1) (x.val i)).2), b-a)
  have hp : p ∈ twoColumnDomain S := ⟨sub_pos.mpr hab, hcond.2⟩
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  funext i
  apply (horizontalHeight (d+1)).injective
  simp only [twoColumnMap, twoColumnAmbient, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply]
  change ((horizontalHeight d).symm
    (v, if i ∈ S then a else a+(b-a)), (horizontalHeight (d+1) (x.val i)).2) = _
  apply Prod.ext
  swap
  · rfl
  apply (horizontalHeight d).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · apply PiLp.ext
    intro l
    change (horizontalHeight (d+1) (x.val 0)).1 l.castSucc =
      (horizontalHeight (d+1) (x.val i)).1 l.castSucc
    exact nextFuks_initial_coordinates_eq x hx l 0 i
  · change (if i ∈ S then a else a+(b-a)) = nextFuksColumn x i
    by_cases hi : i ∈ S
    · simpa only [if_pos hi] using (left i hi).symm
    · simp only [if_neg hi]
      linarith [right i hi]

def twoColumnIntoLevel {d n : ℕ} [NeZero n] (S : Finset (Fin n)) :
    C(twoColumnDomain (d := d) S, fuksLevel (d+1) n (d+2)) :=
  ⟨fun p => ⟨twoColumnMap S p, twoColumnMap_mem_nextFuks S p⟩,
    (twoColumnMap S).continuous.subtype_mk _⟩

theorem range_twoColumnIntoLevel {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    range (twoColumnIntoLevel (d := d) S) =
      {x : fuksLevel (d+1) n (d+2) | x.val ∈ twoColumnCondition S} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact twoColumnMap_mem_condition S p
  · intro hx
    obtain ⟨p, hp⟩ := exists_twoColumnMap_eq_of_condition S hne hproper x.val x.property hx
    exact ⟨p, Subtype.ext hp⟩

theorem isEmbedding_twoColumnIntoLevel {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hiL : iL ∈ S) (hiR : iR ∉ S) :
    IsEmbedding (twoColumnIntoLevel (d := d) S) :=
  IsEmbedding.of_comp (twoColumnIntoLevel S).continuous continuous_subtype_val
    (isEmbedding_twoColumnMap S iL iR hiL hiR)

/-- The image is open in the actual first nonminimal filtration level. -/
theorem isOpenEmbedding_twoColumnIntoLevel {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    IsOpenEmbedding (twoColumnIntoLevel (d := d) S) := by
  obtain ⟨iL, hiL⟩ := hne
  obtain ⟨iR, hiR⟩ := exists_notMem_of_proper S hproper
  refine ⟨isEmbedding_twoColumnIntoLevel S iL iR hiL hiR, ?_⟩
  rw [range_twoColumnIntoLevel S ⟨iL, hiL⟩ hproper]
  exact (isOpen_twoColumnCondition S).preimage continuous_subtype_val

def twoColumnOpenCellHomeomorph {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    twoColumnDomain (d := d) S ≃ₜ
      {x : fuksLevel (d+1) n (d+2) | x.val ∈ twoColumnCondition S} :=
  (isOpenEmbedding_twoColumnIntoLevel S hne hproper).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_twoColumnIntoLevel S hne hproper))

end NRR.PrimePowerTopology
