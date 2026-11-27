import NRR.PrimePowerTopologyGeneralCellCones
import NRR.PrimePowerTopologyTwoColumnAttaching

/-! The boundary of a genuine closed Fox--Neuwirth cone lowers the actual
prefix-count complexity. Collisions and the point at infinity are included
in the resulting compact characteristic map. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology Metric Filter
open scoped OnePoint
open NRR.PrimePower

namespace NRR.PrimePowerTopology

/-- The actual Fuks degree of the open chart specified by a word. -/
def generalCellFuksDegree {d m : ℕ} (a : Fin m → Fin (d+1)) : ℕ :=
  d + ∑ i : Fin m, (d - (a i).val)

private theorem card_image_le_adjacent_changes {α : Type*} [DecidableEq α]
    {m : ℕ} (f : Fin (m+1) → α) :
    (Finset.univ.image f).card ≤
      1 + ∑ i : Fin m, if f i.castSucc = f i.succ then 0 else 1 := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      let g : Fin (m+1) → α := fun i => f i.castSucc
      have repr : Finset.univ.image f =
          insert (f (Fin.last (m+1))) (Finset.univ.image g) := by
        ext y
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨i, rfl⟩
          induction i using Fin.lastCases with
          | last => exact Or.inl rfl
          | cast i => exact Or.inr ⟨i, rfl⟩
        · rintro (rfl | ⟨i, rfl⟩)
          · exact ⟨Fin.last (m+1), rfl⟩
          · exact ⟨i.castSucc, rfl⟩
      rw [repr, Fin.sum_univ_castSucc]
      have hi := ih g
      by_cases he : f (Fin.last m).castSucc = f (Fin.last m).succ
      · have hmem : f (Fin.last (m+1)) ∈ Finset.univ.image g :=
          Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, he⟩
        rw [Finset.card_insert_of_mem hmem]
        simpa only [he, if_true, add_zero, g] using hi
      · have hcard := Finset.card_insert_le (f (Fin.last (m+1))) (Finset.univ.image g)
        simp only [he, if_false]
        have hi' : (Finset.univ.image g).card ≤
            1 + ∑ i : Fin m,
              if f i.castSucc.castSucc = f i.succ.castSucc then 0 else 1 := hi
        simpa only [Fin.castSucc_succ] using hcard.trans (Nat.add_le_add_right hi' 1)

theorem generalCellClosed_fuksProjection_step_eq {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellLinearSpace a)
    (hinj : Function.Injective x.val) (k : Fin d) (i : Fin m)
    (hk : k.castSucc < a i) :
    fuksProjection ⟨x.val, hinj⟩ k i.castSucc =
      fuksProjection ⟨x.val, hinj⟩ k i.succ := by
  funext l
  change (if l ≤ k then x.val i.castSucc l.castSucc else 0) =
    (if l ≤ k then x.val i.succ l.castSucc else 0)
  by_cases hl : l ≤ k
  · simp only [hl, if_true]
    exact x.property i l.castSucc
      ((Fin.strictMono_castSucc.monotone hl).trans_lt hk)
  · simp only [hl, if_false]

private theorem generalCell_changes_le {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellLinearSpace a)
    (hinj : Function.Injective x.val) (k : Fin d) (i : Fin m) :
    (if fuksProjection ⟨x.val, hinj⟩ k i.castSucc =
        fuksProjection ⟨x.val, hinj⟩ k i.succ then 0 else 1) ≤
      (if a i ≤ k.castSucc then 1 else 0) := by
  classical
  by_cases hk : a i ≤ k.castSucc
  · simp only [hk, if_true]
    split_ifs <;> omega
  · simp only [hk, if_false,
      generalCellClosed_fuksProjection_step_eq a x hinj k i (lt_of_not_ge hk), if_true,
      le_refl]

/-- Prefixes can merge on the closed cone, but their number cannot exceed
the number of prefix groups prescribed by the word. -/
theorem card_fuksProjection_generalCellClosed_le {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellLinearSpace a)
    (hinj : Function.Injective x.val) (k : Fin d) :
    (Finset.univ.image (fuksProjection ⟨x.val, hinj⟩ k)).card ≤
      1 + ∑ i : Fin m, if a i ≤ k.castSucc then 1 else 0 := by
  classical
  exact (card_image_le_adjacent_changes _).trans
    (Nat.add_le_add_left (Finset.sum_le_sum
      (fun i _ => generalCell_changes_le a x hinj k i)) 1)

/-- A vanishing last-coordinate gap would identify the two actual sites. -/
theorem generalCellGap_zero_lt_last_of_injective {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellLinearSpace a)
    (hinj : Function.Injective x.val) (i : Fin m)
    (hi : generalCellGap a i x = 0) : (a i).val < d := by
  by_contra hn
  have ha : a i = Fin.last d := Fin.ext (by have := (a i).isLt; simp; omega)
  have he : x.val i.castSucc = x.val i.succ := by
    apply PiLp.ext
    intro k
    by_cases hk : k < a i
    · exact x.property i k hk
    · have hka : k = a i := le_antisymm (ha ▸ Fin.le_last k) (le_of_not_gt hk)
      subst k
      exact (sub_eq_zero.mp hi).symm
  have hbad := congrArg Fin.val (hinj he)
  change i.val = i.val + 1 at hbad
  omega

/-- At the first horizontal coordinate of an inactive gap, one prescribed
prefix distinction is lost. -/
theorem card_fuksProjection_generalCellClosed_lt_of_gap_zero {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellLinearSpace a)
    (hinj : Function.Injective x.val) (i : Fin m)
    (hi : generalCellGap a i x = 0) :
    ∃ k : Fin d,
      (Finset.univ.image (fuksProjection ⟨x.val, hinj⟩ k)).card <
        1 + ∑ j : Fin m, if a j ≤ k.castSucc then 1 else 0 := by
  classical
  let k : Fin d := ⟨(a i).val, generalCellGap_zero_lt_last_of_injective a x hinj i hi⟩
  have hcast : k.castSucc = a i := Fin.ext rfl
  have he : fuksProjection ⟨x.val, hinj⟩ k i.castSucc =
      fuksProjection ⟨x.val, hinj⟩ k i.succ := by
    funext l
    change (if l ≤ k then x.val i.castSucc l.castSucc else 0) =
      (if l ≤ k then x.val i.succ l.castSucc else 0)
    by_cases hl : l ≤ k
    · simp only [hl, if_true]
      by_cases hlt : l < k
      · exact x.property i l.castSucc (by simpa only [← hcast] using hlt)
      · have hlk : l = k := le_antisymm hl (le_of_not_gt hlt)
        subst l
        rw [hcast]
        exact (sub_eq_zero.mp hi).symm
    · simp only [hl, if_false]
  refine ⟨k, (card_image_le_adjacent_changes _).trans_lt (Nat.add_lt_add_left ?_ 1)⟩
  apply Finset.sum_lt_sum (fun j _ => generalCell_changes_le a x hinj k j)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp only [he, if_true, hcast, le_refl, zero_lt_one]

private def generalCellReferencePoint {D m : ℕ} (a : Fin m → Fin D) :
    generalCellOpenDomain a :=
  ⟨generalCellDirection a, fun i => by rw [generalCellGap_direction]; exact zero_lt_one⟩

theorem fuksComplexity_generalCellClosed_le {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellLinearSpace a)
    (hinj : Function.Injective x.val) :
    fuksComplexity ⟨x.val, hinj⟩ ≤ generalCellFuksDegree a := by
  rw [generalCellFuksDegree, ← fuksComplexity_generalCell a (generalCellReferencePoint a)]
  apply Finset.sum_le_sum
  intro k _
  rw [card_fuksProjection_generalCell]
  exact card_fuksProjection_generalCellClosed_le a x hinj k

/-- Every noncollision point on the actual boundary of the closed word
cone has strictly smaller actual Fuks complexity than the open word. -/
theorem fuksComplexity_generalCellClosed_boundary_lt {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellClosedDomain a)
    (hinj : Function.Injective x.val.val) (hx : x.val ∉ generalCellOpenDomain a) :
    fuksComplexity ⟨x.val.val, hinj⟩ < generalCellFuksDegree a := by
  classical
  have hn : ¬ ∀ i, 0 < generalCellGap a i x.val := hx
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have hz : generalCellGap a i x.val = 0 :=
    le_antisymm (le_of_not_gt hi) (x.property i)
  obtain ⟨k, hk⟩ := card_fuksProjection_generalCellClosed_lt_of_gap_zero a x.val hinj i hz
  rw [generalCellFuksDegree, ← fuksComplexity_generalCell a (generalCellReferencePoint a)]
  apply Finset.sum_lt_sum
  · intro l _
    rw [card_fuksProjection_generalCell]
    exact card_fuksProjection_generalCellClosed_le a x.val hinj l
  · refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [card_fuksProjection_generalCell]
    exact hk

theorem fuksComplexity_generalCell_frontier_lt {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellClosedDomain a)
    (hinj : Function.Injective x.val.val)
    (hx : x.val ∈ frontier (generalCellClosedDomain a)) :
    fuksComplexity ⟨x.val.val, hinj⟩ < generalCellFuksDegree a := by
  apply fuksComplexity_generalCellClosed_boundary_lt a x hinj
  change x.val ∈ frontier (ClosedPolyhedralCone.carrier (generalCellGap a)) at hx
  rw [ClosedPolyhedralCone.frontier_carrier (generalCellGap a)
    (fun i => by rw [generalCellGap_direction]; exact zero_lt_one)] at hx
  exact hx.2

theorem isClosed_generalCellClosedDomain {D m : ℕ} (a : Fin m → Fin D) :
    IsClosed (generalCellClosedDomain a) :=
  ClosedPolyhedralCone.isClosed_carrier (generalCellGap a)

instance locallyCompact_generalCellClosedDomain {D m : ℕ} (a : Fin m → Fin D) :
    LocallyCompactSpace (generalCellClosedDomain a) :=
  (isClosed_generalCellClosedDomain a).locallyCompactSpace

/-- The actual finite-coordinate inclusion of the closed parameter cone. -/
def generalCellClosedIntoAmbient {D m : ℕ} (a : Fin m → Fin D) :
    C(generalCellClosedDomain a, GeneralCellAmbient D m) :=
  ⟨fun x => x.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

theorem isClosedEmbedding_generalCellClosedIntoAmbient {D m : ℕ}
    (a : Fin m → Fin D) : IsClosedEmbedding (generalCellClosedIntoAmbient a) :=
  (generalCellLinearSpace a).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.comp
    (isClosed_generalCellClosedDomain a).isClosedEmbedding_subtypeVal

/-- Finite parameters are included in the actual configuration ambient
space and then collapsed at collisions; infinity is sent to infinity. -/
def generalCellAttaching {D m : ℕ} (a : Fin m → Fin D) :
    C(OnePoint (generalCellClosedDomain a), OnePoint (Configuration D (m+1))) :=
  (compactifiedConfigurationCollapse D (m+1)).comp
    ⟨OnePoint.map (generalCellClosedIntoAmbient a),
      OnePoint.continuous_map (generalCellClosedIntoAmbient a).continuous (by
        rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
        exact (isClosedEmbedding_generalCellClosedIntoAmbient a).tendsto_cocompact)⟩

@[simp] theorem generalCellAttaching_infty {D m : ℕ} (a : Fin m → Fin D) :
    generalCellAttaching a ∞ = ∞ :=
  compactifiedConfigurationCollapse_infty _ _

@[simp] theorem generalCellAttaching_coe {D m : ℕ} (a : Fin m → Fin D)
    (x : generalCellClosedDomain a) :
    generalCellAttaching a (x : OnePoint (generalCellClosedDomain a)) =
      configurationCollapse D (m+1) x.val.val :=
  compactifiedConfigurationCollapse_coe _

theorem generalCellAttaching_mem_level {d m : ℕ} (a : Fin m → Fin (d+1))
    (p : OnePoint (generalCellClosedDomain a)) :
    generalCellAttaching a p ∈ compactifiedFuksLevel d (m+1) (generalCellFuksDegree a) := by
  classical
  induction p using OnePoint.rec with
  | infty =>
      rw [generalCellAttaching_infty]
      exact Or.inl rfl
  | coe x =>
      rw [generalCellAttaching_coe]
      by_cases hinj : Function.Injective x.val.val
      · rw [configurationCollapse_injective _ hinj]
        refine Or.inr ⟨⟨x.val.val, hinj⟩, ?_, rfl⟩
        exact (mem_fuksLevel_iff_complexity _).mpr
          (fuksComplexity_generalCellClosed_le a x.val hinj)
      · rw [configurationCollapse_collision _ hinj]
        exact Or.inl rfl

/-- The closed cone compactification gives a genuine continuous
characteristic map into the actual compactified Fuks level. -/
def generalCellCharacteristic {d m : ℕ} (a : Fin m → Fin (d+1)) :
    C(OnePoint (generalCellClosedDomain a),
      compactifiedFuksLevel d (m+1) (generalCellFuksDegree a)) :=
  ⟨fun p => ⟨generalCellAttaching a p, generalCellAttaching_mem_level a p⟩,
    (generalCellAttaching a).continuous.subtype_mk _⟩

/-- The whole topological boundary, including the added point at infinity. -/
def generalCellCharacteristicBoundary {D m : ℕ} (a : Fin m → Fin D) :
    Set (OnePoint (generalCellClosedDomain a)) :=
  ClosedPolyhedralCone.compactifiedBoundary (generalCellGap a)

@[simp] theorem generalCellCharacteristicBoundary_infty {D m : ℕ}
    (a : Fin m → Fin D) :
    (∞ : OnePoint (generalCellClosedDomain a)) ∈ generalCellCharacteristicBoundary a :=
  ClosedPolyhedralCone.infty_mem_compactifiedBoundary _

@[simp] theorem generalCellCharacteristicBoundary_coe_iff {D m : ℕ}
    (a : Fin m → Fin D) (x : generalCellClosedDomain a) :
    (x : OnePoint (generalCellClosedDomain a)) ∈ generalCellCharacteristicBoundary a ↔
      x.val ∉ generalCellOpenDomain a :=
  ClosedPolyhedralCone.coe_mem_compactifiedBoundary_iff _ _

theorem isClosed_generalCellCharacteristicBoundary {D m : ℕ}
    (a : Fin m → Fin D) : IsClosed (generalCellCharacteristicBoundary a) := by
  have ho : IsOpen (generalCellOpenDomain a) := by
    rw [← interior_generalCellClosedDomain]
    exact isOpen_interior
  exact (OnePoint.isOpenEmbedding_coe.isOpenMap _
    (ho.preimage (continuous_subtype_val : Continuous
      (Subtype.val : generalCellClosedDomain a → generalCellLinearSpace a)))).isClosed_compl

/-- Inclusion of the open word chart in its actual closed cone. -/
def generalCellOpenIntoClosed {D m : ℕ} (a : Fin m → Fin D) :
    C(generalCellOpenDomain a, generalCellClosedDomain a) :=
  ⟨fun x => ⟨x.val, fun i => (x.property i).le⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem generalCellAttaching_interior {D m : ℕ} (a : Fin m → Fin D)
    (x : generalCellOpenDomain a) :
    generalCellAttaching a ((generalCellOpenIntoClosed a x) :
      OnePoint (generalCellClosedDomain a)) =
        ((generalCellConfigurationMap a x) : OnePoint (Configuration D (m+1))) := by
  rw [generalCellAttaching_coe]
  exact configurationCollapse_injective _ (generalCellAmbient_injective a x.val x.property)

theorem generalCellAttaching_boundary_mem_lower {d m : ℕ}
    (a : Fin m → Fin (d+1)) (p : generalCellCharacteristicBoundary a) :
    generalCellAttaching a p.val ∈
      compactifiedFuksLevel d (m+1) (generalCellFuksDegree a - 1) := by
  classical
  rcases p with ⟨p, hp⟩
  induction p using OnePoint.rec with
  | infty =>
      rw [generalCellAttaching_infty]
      exact Or.inl rfl
  | coe x =>
      rw [generalCellAttaching_coe]
      by_cases hinj : Function.Injective x.val.val
      · rw [configurationCollapse_injective _ hinj]
        refine Or.inr ⟨⟨x.val.val, hinj⟩, ?_, rfl⟩
        apply (mem_fuksLevel_iff_complexity _).mpr
        have hlt := fuksComplexity_generalCellClosed_boundary_lt a x hinj
          ((generalCellCharacteristicBoundary_coe_iff a x).mp hp)
        omega
      · rw [configurationCollapse_collision _ hinj]
        exact Or.inl rfl

/-- For a positive word degree, the preimage of the lower level is exactly
the whole compactified cone boundary. -/
theorem generalCellAttaching_mem_lower_iff {d m : ℕ}
    (a : Fin m → Fin (d+1)) (hdeg : 0 < generalCellFuksDegree a)
    (p : OnePoint (generalCellClosedDomain a)) :
    generalCellAttaching a p ∈
        compactifiedFuksLevel d (m+1) (generalCellFuksDegree a - 1) ↔
      p ∈ generalCellCharacteristicBoundary a := by
  classical
  constructor
  · intro hp
    induction p using OnePoint.rec with
    | infty => exact generalCellCharacteristicBoundary_infty a
    | coe x =>
        rw [generalCellCharacteristicBoundary_coe_iff]
        intro hx
        have hi := generalCellAmbient_injective a x.val hx
        rw [generalCellAttaching_coe, configurationCollapse_injective _ hi] at hp
        have hc : (⟨x.val.val, hi⟩ : Configuration (d+1) (m+1)) ∈
            fuksLevel d (m+1) (generalCellFuksDegree a - 1) := by
          simpa only [compactifiedFuksLevel, mem_union, mem_singleton_iff,
            OnePoint.coe_ne_infty, false_or, mem_image, OnePoint.coe_eq_coe,
            exists_eq_right] using hp
        have hle := (mem_fuksLevel_iff_complexity _).mp hc
        have he := fuksComplexity_generalCell a ⟨x.val, hx⟩
        change fuksComplexity ⟨x.val.val, hi⟩ = generalCellFuksDegree a at he
        omega
  · intro hp
    exact generalCellAttaching_boundary_mem_lower a ⟨p, hp⟩

def generalCellCharacteristicBoundaryMap {d m : ℕ} (a : Fin m → Fin (d+1)) :
    C(generalCellCharacteristicBoundary a,
      compactifiedFuksLevel d (m+1) (generalCellFuksDegree a - 1)) :=
  ⟨fun p => ⟨generalCellAttaching a p.val, generalCellAttaching_boundary_mem_lower a p⟩,
    ((generalCellAttaching a).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- A disk characteristic map in the actual linear parameter space. -/
def generalCellDiskCharacteristic {d m : ℕ} [NeZero m]
    (a : Fin m → Fin (d+1)) :
    C(closedBall (0 : generalCellLinearSpace a) 1,
      compactifiedFuksLevel d (m+1) (generalCellFuksDegree a)) :=
  (generalCellCharacteristic a).comp
    ⟨(generalCellClosedDisk a).symm, (generalCellClosedDisk a).symm.continuous⟩

/-- Every point of the actual disk sphere maps to the lower filtration
level, including all collision faces and the point compactifying infinity. -/
theorem generalCellDiskCharacteristic_boundary {d m : ℕ} [NeZero m]
    (a : Fin m → Fin (d+1)) (q : closedBall (0 : generalCellLinearSpace a) 1)
    (hq : q.val ∈ sphere 0 1) :
    (generalCellDiskCharacteristic a q).val ∈
      compactifiedFuksLevel d (m+1) (generalCellFuksDegree a - 1) := by
  apply generalCellAttaching_boundary_mem_lower a
    ⟨(generalCellClosedDisk a).symm q, ?_⟩
  apply (ClosedPolyhedralCone.onePointHomeomorphClosedBall_sphere_iff
    (generalCellGap a) (v := generalCellDirection a)
    (fun i => by rw [generalCellGap_direction]; exact zero_lt_one) _).mp
  change ((generalCellClosedDisk a) ((generalCellClosedDisk a).symm q)).val ∈ sphere 0 1
  simpa only [Homeomorph.apply_symm_apply] using hq

theorem generalCellDiskCharacteristic_mem_lower_iff {d m : ℕ} [NeZero m]
    (a : Fin m → Fin (d+1)) (hdeg : 0 < generalCellFuksDegree a)
    (q : closedBall (0 : generalCellLinearSpace a) 1) :
    (generalCellDiskCharacteristic a q).val ∈
        compactifiedFuksLevel d (m+1) (generalCellFuksDegree a - 1) ↔
      q.val ∈ sphere 0 1 := by
  change generalCellAttaching a ((generalCellClosedDisk a).symm q) ∈ _ ↔ _
  rw [generalCellAttaching_mem_lower_iff a hdeg]
  have h := ClosedPolyhedralCone.onePointHomeomorphClosedBall_sphere_iff
    (generalCellGap a) (v := generalCellDirection a)
    (fun i => by rw [generalCellGap_direction]; exact zero_lt_one)
    ((generalCellClosedDisk a).symm q)
  change ((generalCellClosedDisk a) ((generalCellClosedDisk a).symm q)).val ∈ sphere 0 1 ↔ _ at h
  simpa only [Homeomorph.apply_symm_apply] using h.symm

end NRR.PrimePowerTopology
