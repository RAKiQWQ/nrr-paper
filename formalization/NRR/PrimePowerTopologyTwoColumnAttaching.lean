import NRR.PrimePowerTopologyCellCollapse

/-! Compact characteristic maps for the actual two-column strata. The
closed parameter cone includes all collision faces; these and the point
at infinity are sent to the true lower compactified filtration level. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology Filter CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

def compactifiedConfigurationCollapse (d n : ℕ) :
    C(OnePoint (Fin n → Space d), OnePoint (Configuration d n)) :=
  onePointOpenEmbeddingCollapse (Subtype.val : Configuration d n → (Fin n → Space d))
    (isOpen_injectiveSites d n).isOpenEmbedding_subtypeVal

@[simp] theorem compactifiedConfigurationCollapse_infty (d n : ℕ) :
    compactifiedConfigurationCollapse d n ∞ = ∞ :=
  onePointOpenEmbeddingCollapse_infty _ _

@[simp] theorem compactifiedConfigurationCollapse_coe {d n : ℕ}
    (x : Fin n → Space d) :
    compactifiedConfigurationCollapse d n (x : OnePoint (Fin n → Space d)) =
      configurationCollapse d n x := by
  by_cases hx : Function.Injective x
  · rw [configurationCollapse_injective x hx]
    exact onePointOpenEmbeddingCollapse_coe _ _ (⟨x,hx⟩ : Configuration d n)
  · rw [configurationCollapse_collision x hx]
    apply onePointOpenEmbeddingCollapse_outside
    rintro ⟨y,hy⟩
    exact hx (Option.some.inj hy ▸ y.property)

@[simp] theorem twoColumnRecovery_ambient {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (p : TwoColumnAmbientParameters d n) :
    twoColumnRecovery iL iR (twoColumnAmbient S p) = p := by
  simp [twoColumnRecovery,twoColumnAmbient,hL,hR]

/-- Properness holds on all ambient parameters, not only on the open cell. -/
theorem isClosedEmbedding_twoColumnAmbient {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    IsClosedEmbedding (twoColumnAmbient (d := d) S) := by
  have hleft : Function.LeftInverse (twoColumnRecovery (d := d) iL iR)
      (twoColumnAmbient (d := d) S) :=
    twoColumnRecovery_ambient S iL iR hL hR
  refine ⟨hleft.isEmbedding (twoColumnRecovery iL iR).continuous
    (twoColumnAmbient S).continuous, ?_⟩
  have he : range (twoColumnAmbient (d := d) S) =
      {x | twoColumnAmbient S (twoColumnRecovery iL iR x) = x} := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      change twoColumnAmbient S (twoColumnRecovery iL iR (twoColumnAmbient S p)) = _
      rw [hleft p]
    · intro hx
      exact ⟨twoColumnRecovery iL iR x,hx⟩
  rw [he]
  exact isClosed_eq ((twoColumnAmbient S).continuous.comp
    (twoColumnRecovery iL iR).continuous) continuous_id

def closedTwoColumnDomain {d n : ℕ} (S : Finset (Fin n)) :
    Set (TwoColumnAmbientParameters d n) :=
  {p | 0 ≤ p.2 ∧ ∀ i j, i < j → (i ∈ S ↔ j ∈ S) → p.1.2 i ≤ p.1.2 j}

theorem isClosed_closedTwoColumnDomain {d n : ℕ} (S : Finset (Fin n)) :
    IsClosed (closedTwoColumnDomain (d := d) S) := by
  have he : closedTwoColumnDomain (d := d) S =
      {p | 0 ≤ p.2} ∩ ⋂ i : Fin n, ⋂ j : Fin n,
        {p | i < j ∧ (i ∈ S ↔ j ∈ S) → p.1.2 i ≤ p.1.2 j} := by
    ext p
    simp only [closedTwoColumnDomain,mem_setOf_eq,mem_inter_iff,mem_iInter,and_imp]
  rw [he]
  apply (isClosed_le continuous_const continuous_snd).inter
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  by_cases h : i < j ∧ (i ∈ S ↔ j ∈ S)
  · simpa only [h.1,h.2,and_self,true_implies] using
      isClosed_le ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
        ((continuous_apply j).comp (continuous_snd.comp continuous_fst))
  · simp only [h,false_implies,setOf_true,isClosed_univ]

instance locallyCompact_closedTwoColumnDomain {d n : ℕ} (S : Finset (Fin n)) :
    LocallyCompactSpace (closedTwoColumnDomain (d := d) S) :=
  (isClosed_closedTwoColumnDomain S).locallyCompactSpace

theorem twoColumnDomain_subset_closed {d n : ℕ} (S : Finset (Fin n)) :
    twoColumnDomain (d := d) S ⊆ closedTwoColumnDomain S :=
  fun _ hp => ⟨hp.1.le,fun i j hij hs => (hp.2 i j hij hs).le⟩

def closedTwoColumnIntoAmbient {d n : ℕ} (S : Finset (Fin n)) :
    C(closedTwoColumnDomain (d := d) S, Fin n → Space (d+2)) :=
  (twoColumnAmbient S).comp ⟨Subtype.val,continuous_subtype_val⟩

theorem isClosedEmbedding_closedTwoColumnIntoAmbient {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    IsClosedEmbedding (closedTwoColumnIntoAmbient (d := d) S) :=
  (isClosedEmbedding_twoColumnAmbient S iL iR hL hR).comp
    (isClosed_closedTwoColumnDomain S).isClosedEmbedding_subtypeVal

def compactTwoColumnAttaching {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    C(OnePoint (closedTwoColumnDomain (d := d) S), OnePoint (Configuration (d+2) n)) :=
  (compactifiedConfigurationCollapse (d+2) n).comp
    ⟨OnePoint.map (closedTwoColumnIntoAmbient S),
      OnePoint.continuous_map (closedTwoColumnIntoAmbient S).continuous (by
        rw [coclosedCompact_eq_cocompact,coclosedCompact_eq_cocompact]
        exact (isClosedEmbedding_closedTwoColumnIntoAmbient S iL iR hL hR).tendsto_cocompact)⟩

@[simp] theorem compactTwoColumnAttaching_infty {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    compactTwoColumnAttaching (d := d) S iL iR hL hR ∞ = ∞ :=
  compactifiedConfigurationCollapse_infty _ _

@[simp] theorem compactTwoColumnAttaching_coe {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (p : closedTwoColumnDomain (d := d) S) :
    compactTwoColumnAttaching S iL iR hL hR (p : OnePoint (closedTwoColumnDomain S)) =
      twoColumnAttaching S p.val :=
  compactifiedConfigurationCollapse_coe _

/-- At a collision-free point of the closed parameter cone all
within-column height inequalities are necessarily strict. -/
theorem twoColumnHeights_of_closed_injective {d n : ℕ} (S : Finset (Fin n))
    (p : closedTwoColumnDomain (d := d) S)
    (hinj : Function.Injective (twoColumnAmbient S p.val)) :
    p.val.1.2 ∈ twoColumnHeights S := by
  classical
  intro i j hij hs
  refine lt_of_le_of_ne (p.property.2 i j hij hs) ?_
  intro he
  apply hij.ne
  apply hinj
  simp only [twoColumnAmbient,ContinuousMap.coe_mk]
  apply congrArg ((horizontalHeight (d+1)).symm)
  apply Prod.ext
  · apply congrArg ((horizontalHeight d).symm)
    simp only [Prod.mk.injEq,true_and]
    by_cases hi : i ∈ S
    · simp only [hi,(hs.mp hi),if_true]
    · simp only [hi,(mt hs.mpr hi),if_false]
  · exact he

theorem twoColumnAttaching_closed_mem_next {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (p : closedTwoColumnDomain (d := d) S) :
    twoColumnAttaching S p.val ∈ compactifiedFuksLevel (d+1) n (d+2) := by
  classical
  by_cases hinj : Function.Injective (twoColumnAmbient S p.val)
  · by_cases hg : 0 < p.val.2
    · have hp : p.val ∈ twoColumnDomain S :=
        ⟨hg,twoColumnHeights_of_closed_injective S p hinj⟩
      rw [twoColumnAttaching_interior S ⟨p.val,hp⟩]
      exact Or.inr ⟨twoColumnMap S ⟨p.val,hp⟩,twoColumnMap_mem_nextFuks S _,rfl⟩
    · have he : p.val.2 = 0 := le_antisymm (le_of_not_gt hg) p.property.1
      have hp : p.val = ((p.val.1.1,p.val.1.2),0) := by
        exact Prod.ext rfl he
      have ht : Function.Injective p.val.1.2 := by
        apply (twoColumnAmbient_injective_zero S p.val.1.1 p.val.1.2).mp
        simpa only [← hp] using hinj
      rw [hp,twoColumnAttaching_zero_vertical S 0 _ ⟨_,ht⟩]
      refine Or.inr ⟨_,fuksLevel_mono (d+1) n (show d+1 ≤ d+2 by omega) ?_,rfl⟩
      rw [fuksLevel_minimal]
      exact ((verticalCoordinates (d := d+1) 0).symm _).property
  · change configurationCollapse (d+2) n _ ∈ _
    rw [configurationCollapse_collision _ hinj]
    exact Or.inl rfl

def compactTwoColumnCharacteristic {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    C(OnePoint (closedTwoColumnDomain (d := d) S), compactifiedFuksLevel (d+1) n (d+2)) := by
  refine ⟨fun p => ⟨compactTwoColumnAttaching S iL iR hL hR p,?_⟩,
    (compactTwoColumnAttaching S iL iR hL hR).continuous.subtype_mk _⟩
  induction p using OnePoint.rec with
  | infty =>
      rw [compactTwoColumnAttaching_infty]
      exact Or.inl rfl
  | coe p =>
      rw [compactTwoColumnAttaching_coe]
      exact twoColumnAttaching_closed_mem_next S p

theorem compactTwoColumnAttaching_boundary {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (p : closedTwoColumnDomain (d := d) S) (hp : p.val ∉ twoColumnDomain S) :
    compactTwoColumnAttaching S iL iR hL hR (p : OnePoint (closedTwoColumnDomain S)) ∈
      compactifiedFuksLevel (d+1) n (d+1) := by
  classical
  rw [compactTwoColumnAttaching_coe]
  by_cases hinj : Function.Injective (twoColumnAmbient S p.val)
  · have hg : p.val.2 = 0 := by
      have hng : ¬ 0 < p.val.2 := fun h => hp
        ⟨h,twoColumnHeights_of_closed_injective S p hinj⟩
      exact le_antisymm (le_of_not_gt hng) p.property.1
    have he : p.val = ((p.val.1.1,p.val.1.2),0) := Prod.ext rfl hg
    have ht : Function.Injective p.val.1.2 := by
      apply (twoColumnAmbient_injective_zero S p.val.1.1 p.val.1.2).mp
      simpa only [← he] using hinj
    rw [he,twoColumnAttaching_zero_vertical S 0 _ ⟨_,ht⟩]
    refine Or.inr ⟨_,?_,rfl⟩
    rw [fuksLevel_minimal]
    exact ((verticalCoordinates (d := d+1) 0).symm _).property
  · change configurationCollapse (d+2) n _ ∈ _
    rw [configurationCollapse_collision _ hinj]
    exact Or.inl rfl

def twoColumnClosedInterior {d n : ℕ} (S : Finset (Fin n)) :
    C(twoColumnDomain (d := d) S,closedTwoColumnDomain (d := d) S) :=
  ⟨fun p => ⟨p.val,twoColumnDomain_subset_closed S p.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem isOpenEmbedding_twoColumnClosedInterior {d n : ℕ} (S : Finset (Fin n)) :
    IsOpenEmbedding (twoColumnClosedInterior (d := d) S) := by
  have he : IsEmbedding (twoColumnClosedInterior (d := d) S) :=
    IsEmbedding.of_comp (twoColumnClosedInterior S).continuous continuous_subtype_val
      IsEmbedding.subtypeVal
  refine ⟨he,?_⟩
  have hr : range (twoColumnClosedInterior (d := d) S) =
      Subtype.val ⁻¹' twoColumnDomain S := by
    ext p
    exact ⟨by rintro ⟨q,rfl⟩; exact q.property,
      fun hp => ⟨⟨p.val,hp⟩,Subtype.ext rfl⟩⟩
  rw [hr]
  exact (isOpen_twoColumnDomain S).preimage continuous_subtype_val

/-- The actual compact parameter boundary, including infinity. -/
def twoColumnCharacteristicBoundary {d n : ℕ} (S : Finset (Fin n)) :
    Set (OnePoint (closedTwoColumnDomain (d := d) S)) :=
  (range (fun p : twoColumnDomain (d := d) S =>
    ((twoColumnClosedInterior S p) : OnePoint (closedTwoColumnDomain S))))ᶜ

theorem isClosed_twoColumnCharacteristicBoundary {d n : ℕ} (S : Finset (Fin n)) :
    IsClosed (twoColumnCharacteristicBoundary (d := d) S) :=
  (OnePoint.isOpenEmbedding_coe.comp (isOpenEmbedding_twoColumnClosedInterior S)).isOpen_range.isClosed_compl

@[simp] theorem mem_twoColumnCharacteristicBoundary_coe {d n : ℕ}
    (S : Finset (Fin n)) (p : closedTwoColumnDomain (d := d) S) :
    (p : OnePoint (closedTwoColumnDomain (d := d) S)) ∈ twoColumnCharacteristicBoundary S ↔
      p.val ∉ twoColumnDomain S := by
  constructor
  · intro hp hi
    exact hp ⟨⟨p.val,hi⟩,rfl⟩
  · intro hp ⟨q,hq⟩
    have he : q.val = p.val := congrArg Subtype.val (Option.some.inj hq)
    exact hp (he ▸ q.property)

theorem compactTwoColumnAttaching_boundary_mem_lower {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (p : twoColumnCharacteristicBoundary (d := d) S) :
    compactTwoColumnAttaching S iL iR hL hR p.val ∈
      compactifiedFuksLevel (d+1) n (d+1) := by
  rcases p with ⟨p,hp⟩
  induction p using OnePoint.rec with
  | infty =>
      rw [compactTwoColumnAttaching_infty]
      exact Or.inl rfl
  | coe p =>
      exact compactTwoColumnAttaching_boundary S iL iR hL hR p
        ((mem_twoColumnCharacteristicBoundary_coe S p).mp hp)

def twoColumnCharacteristicBoundaryMap {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    C(twoColumnCharacteristicBoundary (d := d) S,
      compactifiedFuksLevel (d+1) n (d+1)) :=
  ⟨fun p => ⟨compactTwoColumnAttaching S iL iR hL hR p.val,
      compactTwoColumnAttaching_boundary_mem_lower S iL iR hL hR p⟩,
    ((compactTwoColumnAttaching S iL iR hL hR).continuous.comp
      continuous_subtype_val).subtype_mk _⟩

/-- The characteristic map is a continuous map of the real compact pairs. -/
theorem twoColumnCharacteristic_pair_comm {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    NRR.SingularHomology.subIncl (Y := TopCat.of (OnePoint (closedTwoColumnDomain (d := d) S)))
        (twoColumnCharacteristicBoundary S) ≫
      TopCat.ofHom (compactTwoColumnCharacteristic S iL iR hL hR) =
    TopCat.ofHom (twoColumnCharacteristicBoundaryMap S iL iR hL hR) ≫
      NRR.PrimePowerTopology.compactifiedFuksInclusion (d := d+1) (n := n)
        (show d+1 ≤ d+2 by omega) := rfl

abbrev TwoColumnOrderPair {n : ℕ} (S : Finset (Fin n)) :=
  {ij : Fin n × Fin n // ij.1 < ij.2 ∧ (ij.1 ∈ S ↔ ij.2 ∈ S)}

abbrev TwoColumnConeIndex {n : ℕ} (S : Finset (Fin n)) := Option (TwoColumnOrderPair S)

/-- The actual face inequalities, including the column-gap face. -/
def twoColumnConeFunctional {d n : ℕ} (S : Finset (Fin n)) :
    TwoColumnConeIndex S → TwoColumnAmbientParameters d n →L[ℝ] ℝ
  | none => {
      toFun := fun p => p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_snd }
  | some ij => {
      toFun := fun p => p.1.2 ij.val.2 - p.1.2 ij.val.1
      map_add' := by intro p q; simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply]; ring
      map_smul' := by intro r p; simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,
        smul_eq_mul,RingHom.id_apply]; ring
      cont := ((continuous_apply ij.val.2).comp (continuous_snd.comp continuous_fst)).sub
        ((continuous_apply ij.val.1).comp (continuous_snd.comp continuous_fst)) }

theorem closedTwoColumnDomain_iff_cone {d n : ℕ} (S : Finset (Fin n))
    (p : TwoColumnAmbientParameters d n) :
    p ∈ closedTwoColumnDomain S ↔ ∀ a, 0 ≤ twoColumnConeFunctional S a p := by
  constructor
  · intro hp a
    cases a with
    | none => exact hp.1
    | some ij => exact sub_nonneg.mpr (hp.2 _ _ ij.property.1 ij.property.2)
  · intro hp
    refine ⟨hp none,?_⟩
    intro i j hij hs
    exact sub_nonneg.mp (hp (some ⟨(i,j),hij,hs⟩))

theorem twoColumnDomain_iff_strictCone {d n : ℕ} (S : Finset (Fin n))
    (p : TwoColumnAmbientParameters d n) :
    p ∈ twoColumnDomain S ↔ ∀ a, 0 < twoColumnConeFunctional S a p := by
  constructor
  · intro hp a
    cases a with
    | none => exact hp.1
    | some ij => exact sub_pos.mpr (hp.2 _ _ ij.property.1 ij.property.2)
  · intro hp
    refine ⟨hp none,?_⟩
    intro i j hij hs
    exact sub_pos.mp (hp (some ⟨(i,j),hij,hs⟩))

def twoColumnConeDirection (d n : ℕ) : TwoColumnAmbientParameters d n :=
  (((0,0),fun i => (i.val : ℝ)),1)

theorem twoColumnConeDirection_positive {d n : ℕ} (S : Finset (Fin n))
    (a : TwoColumnConeIndex S) :
    0 < twoColumnConeFunctional S a (twoColumnConeDirection d n) := by
  cases a with
  | none => exact zero_lt_one
  | some ij =>
      change 0 < (ij.val.2.val : ℝ) - (ij.val.1.val : ℝ)
      exact sub_pos.mpr (Nat.cast_lt.mpr ij.property.1)

end NRR.PrimePowerTopology
