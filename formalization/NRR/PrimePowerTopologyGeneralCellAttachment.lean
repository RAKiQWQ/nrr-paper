import NRR.PrimePowerTopologyGeneralCellCover
import NRR.PrimePowerTopologyGeneralCellBoundary
import NRR.PrimePowerTopologyFilteredChains
import NRR.SingularHomologyFiniteCellGluing

/-!
Finite characteristic families for the actual compactified Fuks filtration.
The indices record an actual lexicographic label order and an adjacent word
of the specified Fuks degree. All maps below take values in the genuine
configuration compactification, with collisions collapsed to infinity.
-/

noncomputable section
set_option maxHeartbeats 1600000
open Set Topology Metric
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- The finite family of labelled words attached between levels `k` and `k+1`. -/
abbrev GeneralFuksCellIndex (d m k : ℕ) :=
  Equiv.Perm (Fin (m+1)) × {a : Fin m → Fin (d+1) // generalCellFuksDegree a = k+1}

def generalFuksLowerSubset (d m k : ℕ) : Set (compactifiedFuksLevel d (m+1) (k+1)) :=
  Subtype.val ⁻¹' compactifiedFuksLevel d (m+1) k

theorem isClosed_generalFuksLowerSubset (d m k : ℕ) :
    IsClosed (generalFuksLowerSubset d m k) :=
  (isClosed_compactifiedFuksLevel d (m+1) k).preimage continuous_subtype_val

instance compactSpace_generalFuksLowerSubset (d m k : ℕ) :
    CompactSpace (generalFuksLowerSubset d m k) := by
  letI : CompactSpace (compactifiedFuksLevel d (m+1) (k+1)) :=
    isCompact_iff_compactSpace.mp (isCompact_compactifiedFuksLevel d (m+1) (k+1))
  exact isCompact_iff_compactSpace.mp (isClosed_generalFuksLowerSubset d m k).isCompact

theorem nonempty_generalFuksLowerSubset (d m k : ℕ) :
    (generalFuksLowerSubset d m k).Nonempty :=
  ⟨⟨∞, Or.inl rfl⟩, Or.inl rfl⟩

theorem fuksComplexity_generalCellRelabelled {d m : ℕ}
    (σ : Equiv.Perm (Fin (m+1))) (a : Fin m → Fin (d+1))
    (p : generalCellOpenDomain a) :
    fuksComplexity (generalCellRelabelledConfigurationMap σ a p) = generalCellFuksDegree a := by
  change fuksComplexity (σ • generalCellConfigurationMap a p) = _
  rw [fuksComplexity_relabel, fuksComplexity_generalCell]
  rfl

theorem generalCellFuksDegree_configurationAdjacentWord {d m : ℕ}
    (x : Configuration (d+1) (m+1)) :
    generalCellFuksDegree (configurationAdjacentWord x) = fuksComplexity x := by
  calc
    _ = fuksComplexity (generalCellRelabelledConfigurationMap
        (configurationLexOrder x) (configurationAdjacentWord x)
          (configurationGeneralCellParameter x)) :=
      (fuksComplexity_generalCellRelabelled _ _ _).symm
    _ = _ := congrArg fuksComplexity (configurationGeneralCellParameter_map x)

/-- The actual relabelled compact cone characteristic map at a fixed degree. -/
def generalFuksConeCharacteristic {d m k : ℕ} (c : GeneralFuksCellIndex d m k) :
    C(OnePoint (generalCellClosedDomain c.2.val), compactifiedFuksLevel d (m+1) (k+1)) where
  toFun p := ⟨compactifiedConfigurationRelabel c.1 (generalCellAttaching c.2.val p), by
    apply (compactifiedFuksLevel_relabel_mem_iff c.1 _).mpr
    simpa only [c.2.property] using generalCellAttaching_mem_level c.2.val p⟩
  continuous_toFun :=
    ((compactifiedConfigurationRelabel c.1).continuous.comp
      (generalCellAttaching c.2.val).continuous).subtype_mk _

@[simp] theorem generalFuksConeCharacteristic_infty {d m k : ℕ}
    (c : GeneralFuksCellIndex d m k) :
    (generalFuksConeCharacteristic c ∞).val = ∞ := by
  change compactifiedConfigurationRelabel c.1 (generalCellAttaching c.2.val ∞) = ∞
  rw [generalCellAttaching_infty]
  rfl

theorem generalFuksConeCharacteristic_interior {d m k : ℕ}
    (c : GeneralFuksCellIndex d m k) (p : generalCellOpenDomain c.2.val) :
    (generalFuksConeCharacteristic c
      ((generalCellOpenIntoClosed c.2.val p) : OnePoint (generalCellClosedDomain c.2.val))).val =
      ((generalCellRelabelledConfigurationMap c.1 c.2.val p : Configuration (d+1) (m+1)) :
        OnePoint (Configuration (d+1) (m+1))) := by
  change compactifiedConfigurationRelabel c.1
    (generalCellAttaching c.2.val (generalCellOpenIntoClosed c.2.val p)) = _
  rw [generalCellAttaching_interior]
  rfl

/-- The lower subspace is exactly the whole compactified cone boundary. -/
theorem generalFuksConeCharacteristic_mem_lower_iff {d m k : ℕ}
    (c : GeneralFuksCellIndex d m k) (p : OnePoint (generalCellClosedDomain c.2.val)) :
    generalFuksConeCharacteristic c p ∈ generalFuksLowerSubset d m k ↔
      p ∈ generalCellCharacteristicBoundary c.2.val := by
  change compactifiedConfigurationRelabel c.1 (generalCellAttaching c.2.val p) ∈
    compactifiedFuksLevel d (m+1) k ↔ _
  rw [compactifiedFuksLevel_relabel_mem_iff]
  have hdeg : 0 < generalCellFuksDegree c.2.val := by rw [c.2.property]; omega
  simpa only [c.2.property, Nat.add_sub_cancel] using
    generalCellAttaching_mem_lower_iff c.2.val hdeg p

/-- Actual coverage by the lower level and the finite family of fixed-degree
compactified cones; no chart-coverage hypothesis is assumed. -/
theorem generalFuksConeCharacteristic_cover {d m k : ℕ}
    (x : compactifiedFuksLevel d (m+1) (k+1)) :
    x ∈ generalFuksLowerSubset d m k ∨
      ∃ (c : GeneralFuksCellIndex d m k)
        (p : OnePoint (generalCellClosedDomain c.2.val)), generalFuksConeCharacteristic c p = x := by
  rcases x.property with hx | ⟨y, hy, he⟩
  · left
    change x.val ∈ compactifiedFuksLevel d (m+1) k
    exact hx.symm ▸ Or.inl rfl
  · by_cases hl : y ∈ fuksLevel d (m+1) k
    · left
      exact Or.inr ⟨y, hl, he⟩
    · right
      have hdegree : generalCellFuksDegree (configurationAdjacentWord y) = k+1 := by
        rw [generalCellFuksDegree_configurationAdjacentWord]
        have hu := (mem_fuksLevel_iff_complexity y).mp hy
        have hlow := (mem_fuksLevel_iff_complexity y).not.mp hl
        omega
      let c : GeneralFuksCellIndex d m k :=
        (configurationLexOrder y, ⟨configurationAdjacentWord y, hdegree⟩)
      refine ⟨c, (generalCellOpenIntoClosed c.2.val (configurationGeneralCellParameter y) :
        OnePoint (generalCellClosedDomain c.2.val)), ?_⟩
      apply Subtype.ext
      rw [generalFuksConeCharacteristic_interior]
      exact (congrArg (fun z : Configuration (d+1) (m+1) =>
        (z : OnePoint (Configuration (d+1) (m+1))))
          (configurationGeneralCellParameter_map y)).trans he

theorem exists_generalCellOpenParameter_of_not_boundary {D m : ℕ}
    (a : Fin m → Fin D) (p : OnePoint (generalCellClosedDomain a))
    (hp : p ∉ generalCellCharacteristicBoundary a) :
    ∃ u : generalCellOpenDomain a,
      ((generalCellOpenIntoClosed a u) : OnePoint (generalCellClosedDomain a)) = p := by
  induction p using OnePoint.rec with
  | infty => exact False.elim (hp (generalCellCharacteristicBoundary_infty a))
  | coe p =>
    have hu : p.val ∈ generalCellOpenDomain a := by
      simpa only [generalCellCharacteristicBoundary_coe_iff, not_not] using hp
    exact ⟨⟨p.val, hu⟩, rfl⟩

theorem generalFuksConeCharacteristic_interior_unique {d m k : ℕ}
    (c e : GeneralFuksCellIndex d m k)
    (p : OnePoint (generalCellClosedDomain c.2.val))
    (q : OnePoint (generalCellClosedDomain e.2.val))
    (hp : p ∉ generalCellCharacteristicBoundary c.2.val)
    (he : generalFuksConeCharacteristic c p = generalFuksConeCharacteristic e q) :
    ∃ hce : c = e, hce ▸ p = q := by
  have hq : q ∉ generalCellCharacteristicBoundary e.2.val := by
    intro hq
    exact hp ((generalFuksConeCharacteristic_mem_lower_iff c p).mp
      (he ▸ (generalFuksConeCharacteristic_mem_lower_iff e q).mpr hq))
  obtain ⟨u, rfl⟩ := exists_generalCellOpenParameter_of_not_boundary c.2.val p hp
  obtain ⟨v, rfl⟩ := exists_generalCellOpenParameter_of_not_boundary e.2.val q hq
  have hconf := congrArg Subtype.val he
  rw [generalFuksConeCharacteristic_interior, generalFuksConeCharacteristic_interior] at hconf
  have hconf' := OnePoint.coe_injective hconf
  obtain ⟨hσ, ha⟩ := generalCellRelabelledConfigurationMap_indices_unique
    c.1 e.1 c.2.val e.2.val u v hconf'
  have hce : c = e := Prod.ext hσ (Subtype.ext ha)
  subst e
  refine ⟨rfl, ?_⟩
  have huv : u = v := (isEmbedding_generalCellConfigurationMap c.2.val).injective
    ((relabelConfiguration c.1).injective hconf')
  cases huv
  rfl

/-- A continuous linear equivalence induces a sphere-preserving homeomorphism
of closed unit balls even when the norms are not induced by inner products. -/
theorem exists_closedBallHomeomorph_pair {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    ∃ h : closedBall (0 : E) 1 ≃ₜ closedBall (0 : F) 1,
      ∀ q, ‖(h q).val‖ = 1 ↔ ‖q.val‖ = 1 := by
  let s : Set F := e '' closedBall (0 : E) 1
  have hsc : Convex ℝ s := (convex_closedBall (0 : E) 1).linear_image e.toLinearMap
  have hsclosed : IsClosed s := e.toHomeomorph.isClosedMap _ isClosed_closedBall
  have hscompact : IsCompact s := (isCompact_closedBall (0 : E) 1).image e.continuous
  have hsint : (interior s).Nonempty := by
    change (interior (e.toHomeomorph '' closedBall (0 : E) 1)).Nonempty
    rw [← e.toHomeomorph.image_interior, interior_closedBall _ one_ne_zero]
    exact ⟨e 0, ⟨0, mem_ball_self zero_lt_one, rfl⟩⟩
  obtain ⟨h, _, hcl, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hsc hsint hscompact.isBounded
  let H : E ≃ₜ F := e.toHomeomorph.trans h
  have himage : H '' closedBall (0 : E) 1 = closedBall (0 : F) 1 := by
    change (h ∘ e) '' closedBall (0 : E) 1 = _
    rw [hsclosed.closure_eq] at hcl
    simpa only [s, Set.image_image] using hcl
  have hsphere : H '' sphere (0 : E) 1 = sphere (0 : F) 1 := by
    rw [← frontier_closedBall _ one_ne_zero, H.image_frontier, himage,
      frontier_closedBall _ one_ne_zero]
  refine ⟨(H.image _).trans (Homeomorph.setCongr himage), ?_⟩
  intro q
  change ‖H q.val‖ = 1 ↔ ‖q.val‖ = 1
  rw [← mem_sphere_zero_iff_norm, ← mem_sphere_zero_iff_norm, ← hsphere]
  exact H.injective.mem_set_image

abbrev GeneralFuksParameters (m k : ℕ) := Space (k+1+(m+1))

theorem finrank_generalFuksParameters (m k : ℕ) :
    Module.finrank ℝ (GeneralFuksParameters m k) = k+1+(m+1) :=
  finrank_euclideanSpace_fin

theorem finrank_generalFuksCellLinearSpace {d m k : ℕ} (c : GeneralFuksCellIndex d m k) :
    Module.finrank ℝ (generalCellLinearSpace c.2.val) = k+1+(m+1) := by
  obtain ⟨p, hp⟩ := generalCellOpenDomain_nonempty c.2.val
  rw [finrank_generalCellLinearSpace_eq_fuksComplexity_add c.2.val ⟨p, hp⟩,
    fuksComplexity_generalCell]
  change generalCellFuksDegree c.2.val + (m+1) = _
  rw [c.2.property]

/-- The norm-independent change from each actual parameter disk to the
single Euclidean disk of the common cell dimension. -/
theorem exists_generalFuksCellDiskHomeomorph {d m k : ℕ}
    (c : GeneralFuksCellIndex d m k) :
    ∃ h : closedBall (0 : generalCellLinearSpace c.2.val) 1 ≃ₜ
        closedBall (0 : GeneralFuksParameters m k) 1,
      ∀ q, ‖(h q).val‖ = 1 ↔ ‖q.val‖ = 1 := by
  apply exists_closedBallHomeomorph_pair
  apply ContinuousLinearEquiv.ofFinrankEq
  rw [finrank_generalFuksCellLinearSpace, finrank_generalFuksParameters]

def generalFuksCellDiskHomeomorph {d m k : ℕ} (c : GeneralFuksCellIndex d m k) :
    closedBall (0 : generalCellLinearSpace c.2.val) 1 ≃ₜ
      closedBall (0 : GeneralFuksParameters m k) 1 :=
  (exists_generalFuksCellDiskHomeomorph c).choose

theorem generalFuksCellDiskHomeomorph_sphere_iff {d m k : ℕ}
    (c : GeneralFuksCellIndex d m k) (q : closedBall (0 : generalCellLinearSpace c.2.val) 1) :
    ‖(generalFuksCellDiskHomeomorph c q).val‖ = 1 ↔ ‖q.val‖ = 1 :=
  (exists_generalFuksCellDiskHomeomorph c).choose_spec q

def generalFuksCompactDisk {d m k : ℕ} [NeZero m] (c : GeneralFuksCellIndex d m k) :
    OnePoint (generalCellClosedDomain c.2.val) ≃ₜ CellDisk (GeneralFuksParameters m k) :=
  (generalCellClosedDisk c.2.val).trans (generalFuksCellDiskHomeomorph c)

theorem generalFuksCompactDisk_boundary_iff {d m k : ℕ} [NeZero m]
    (c : GeneralFuksCellIndex d m k) (p : OnePoint (generalCellClosedDomain c.2.val)) :
    ‖(generalFuksCompactDisk c p).val‖ = 1 ↔
      p ∈ generalCellCharacteristicBoundary c.2.val := by
  change ‖(generalFuksCellDiskHomeomorph c (generalCellClosedDisk c.2.val p)).val‖ = 1 ↔ _
  rw [generalFuksCellDiskHomeomorph_sphere_iff]
  exact (mem_sphere_zero_iff_norm.symm).trans
    (ClosedPolyhedralCone.onePointHomeomorphClosedBall_sphere_iff
      (generalCellGap c.2.val) (v := generalCellDirection c.2.val)
      (fun i => by rw [generalCellGap_direction]; exact zero_lt_one) p)

/-- The genuine finite family of Euclidean disk characteristic maps. -/
def generalFuksDiskCharacteristic {d m k : ℕ} [NeZero m] (c : GeneralFuksCellIndex d m k) :
    C(CellDisk (GeneralFuksParameters m k), compactifiedFuksLevel d (m+1) (k+1)) :=
  (generalFuksConeCharacteristic c).comp
    ⟨(generalFuksCompactDisk c).symm, (generalFuksCompactDisk c).symm.continuous⟩

theorem generalFuksDiskCharacteristic_mem_lower_iff {d m k : ℕ} [NeZero m]
    (c : GeneralFuksCellIndex d m k) (q : CellDisk (GeneralFuksParameters m k)) :
    generalFuksDiskCharacteristic c q ∈ generalFuksLowerSubset d m k ↔ ‖q.val‖ = 1 := by
  change generalFuksConeCharacteristic c ((generalFuksCompactDisk c).symm q) ∈ _ ↔ _
  rw [generalFuksConeCharacteristic_mem_lower_iff]
  simpa only [Homeomorph.apply_symm_apply] using
    (generalFuksCompactDisk_boundary_iff c ((generalFuksCompactDisk c).symm q)).symm

theorem generalFuksDiskCharacteristic_interior_unique {d m k : ℕ} [NeZero m]
    (c e : GeneralFuksCellIndex d m k) (q r : CellDisk (GeneralFuksParameters m k))
    (hq : ‖q.val‖ < 1)
    (he : generalFuksDiskCharacteristic c q = generalFuksDiskCharacteristic e r) :
    c = e ∧ q = r := by
  have hp : (generalFuksCompactDisk c).symm q ∉ generalCellCharacteristicBoundary c.2.val := by
    rw [← generalFuksCompactDisk_boundary_iff]
    simpa only [Homeomorph.apply_symm_apply] using ne_of_lt hq
  obtain ⟨hce, hqr⟩ := generalFuksConeCharacteristic_interior_unique c e
    ((generalFuksCompactDisk c).symm q) ((generalFuksCompactDisk e).symm r) hp he
  subst e
  exact ⟨rfl, (generalFuksCompactDisk c).symm.injective hqr⟩

theorem generalFuksDiskCharacteristic_cover {d m k : ℕ} [NeZero m]
    (x : compactifiedFuksLevel d (m+1) (k+1)) :
    x ∈ generalFuksLowerSubset d m k ∨
      ∃ c q, generalFuksDiskCharacteristic c q = x := by
  rcases generalFuksConeCharacteristic_cover x with hx | ⟨c, p, hp⟩
  · exact Or.inl hx
  · right
    refine ⟨c, generalFuksCompactDisk c p, ?_⟩
    change generalFuksConeCharacteristic c
      ((generalFuksCompactDisk c).symm (generalFuksCompactDisk c p)) = x
    rw [Homeomorph.symm_apply_apply]
    exact hp

/-- Every consecutive positive-degree compactified Fuks pair is the actual
finite disk attachment, with all geometric axioms proved from its charts. -/
def generalFuksFiniteAttachment (d m k : ℕ) [NeZero m] :
    FiniteCellAttachment (GeneralFuksCellIndex d m k) (GeneralFuksParameters m k)
      (compactifiedFuksLevel d (m+1) (k+1)) (generalFuksLowerSubset d m k) where
  characteristic := generalFuksDiskCharacteristic
  boundary := generalFuksDiskCharacteristic_mem_lower_iff
  interior_unique := generalFuksDiskCharacteristic_interior_unique
  cover := generalFuksDiskCharacteristic_cover

/-- The lower member of the original Fuks pair is exactly the lower subset
used by the finite disk attachment. -/
def generalFuksLowerHomeomorph (d m k : ℕ) :
    compactifiedFuksLevel d (m+1) k ≃ₜ generalFuksLowerSubset d m k where
  toFun x := ⟨⟨x.val, compactifiedFuksLevel_mono d (m+1) (by omega) x.property⟩,
    x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def generalFuksGoodNeighborhood (d m k : ℕ) [NeZero m] :
    Set (compactifiedFuksLevel d (m+1) (k+1)) :=
  (generalFuksFiniteAttachment d m k).neighborhood

theorem isOpen_generalFuksGoodNeighborhood (d m k : ℕ) [NeZero m] :
    IsOpen (generalFuksGoodNeighborhood d m k) :=
  (generalFuksFiniteAttachment d m k).isOpen_neighborhood

/-- The actual lower compactified level deformation retracts from an open
neighborhood inside the actual upper compactified level. -/
def generalFuksNeighborhoodDeformation (d m k : ℕ) [NeZero m] :
    NeighborhoodDeformation (generalFuksLowerSubset d m k) (generalFuksGoodNeighborhood d m k) :=
  (generalFuksFiniteAttachment d m k).neighborhoodDeformation

end NRR.PrimePowerTopology
