import NRR.PrimePowerTopologyInfinityNeighborhoodCones

/-! Finite disk attachments for every level of the genuine stabilized
configuration filtration, beginning at its point at infinity. -/

noncomputable section
set_option maxHeartbeats 1800000
open Set Topology Metric
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

abbrev StabilizedFuksCellIndex (d m r : ℕ) :=
  Equiv.Perm (Fin (m+1)) × {a : Fin m → Fin (d+1) // generalCellFuksDegree a = r}

def stabilizedFuksLowerSubset (d m k r : ℕ) :
    Set (stabilizedFuksLevel d (m+1) k (r+1)) :=
  Subtype.val ⁻¹' stabilizedFuksLevel d (m+1) k r

instance compactSpace_stabilizedFuksLowerSubset (d m k r : ℕ) :
    CompactSpace (stabilizedFuksLowerSubset d m k r) :=
  isCompact_iff_compactSpace.mp
    ((isClosed_stabilizedFuksLevel d (m+1) k r).preimage continuous_subtype_val).isCompact

def stabilizedFuksConeCharacteristic {d m k r : ℕ} (c : StabilizedFuksCellIndex d m r) :
    C(OnePoint (stabilizedCellClosedDomain c.2.val k),
      stabilizedFuksLevel d (m+1) k (r+1)) where
  toFun p := ⟨stabilizedConfigurationRelabel c.1 (stabilizedCellAttaching c.2.val k p),by
    apply (stabilizedFuksLevel_relabel_iff c.1 _).mpr
    simpa only [c.2.property] using stabilizedCellAttaching_mem_level c.2.val p⟩
  continuous_toFun := ((stabilizedConfigurationRelabel c.1).continuous.comp
    (stabilizedCellAttaching c.2.val k).continuous).subtype_mk _

@[simp] theorem stabilizedFuksConeCharacteristic_infty {d m k r : ℕ}
    (c : StabilizedFuksCellIndex d m r) :
    (stabilizedFuksConeCharacteristic (k := k) c ∞).val = ∞ := by
  change stabilizedConfigurationRelabel c.1 (stabilizedCellAttaching c.2.val k ∞) = ∞
  simp

theorem stabilizedFuksConeCharacteristic_mem_lower_iff {d m k r : ℕ}
    (c : StabilizedFuksCellIndex d m r)
    (p : OnePoint (stabilizedCellClosedDomain c.2.val k)) :
    stabilizedFuksConeCharacteristic c p ∈ stabilizedFuksLowerSubset d m k r ↔
      p ∈ stabilizedCellBoundary c.2.val k := by
  change stabilizedConfigurationRelabel c.1 (stabilizedCellAttaching c.2.val k p) ∈
    stabilizedFuksLevel d (m+1) k r ↔ _
  rw [stabilizedFuksLevel_relabel_iff]
  simpa only [c.2.property] using stabilizedCellAttaching_mem_lower_iff c.2.val p

def stabilizedCellInterior {D m : ℕ} (a : Fin m → Fin D) (k : ℕ)
    (u : generalCellOpenDomain a) (v : Space k) : stabilizedCellClosedDomain a k :=
  ⟨(u.val,v),fun i => (u.property i).le⟩

theorem stabilizedFuksConeCharacteristic_interior {d m k r : ℕ}
    (c : StabilizedFuksCellIndex d m r) (u : generalCellOpenDomain c.2.val) (v : Space k) :
    (stabilizedFuksConeCharacteristic c
      ((stabilizedCellInterior c.2.val k u v) : OnePoint _)).val =
      ((generalCellRelabelledConfigurationMap c.1 c.2.val u,v) :
        OnePoint (Configuration (d+1) (m+1) × Space k)) := by
  change stabilizedConfigurationRelabel c.1
    (stabilizedCellAttaching c.2.val k ((stabilizedCellInterior c.2.val k u v) : OnePoint _)) = _
  rw [stabilizedCellAttaching_coe]
  change stabilizedConfigurationRelabel c.1
    (stabilizedConfigurationCollapse (d+1) (m+1) k ((u.val.val,v) : OnePoint _)) = _
  rw [stabilizedConfigurationCollapse_injective _ _
    (generalCellAmbient_injective c.2.val u.val u.property)]
  rfl

theorem exists_stabilizedCellInterior_of_not_boundary {D m k : ℕ}
    (a : Fin m → Fin D) (p : OnePoint (stabilizedCellClosedDomain a k))
    (hp : p ∉ stabilizedCellBoundary a k) :
    ∃ (u : generalCellOpenDomain a) (v : Space k),
      ((stabilizedCellInterior a k u v) : OnePoint _) = p := by
  induction p using OnePoint.rec with
  | infty => exact False.elim (hp (ClosedPolyhedralCone.infty_mem_compactifiedBoundary _))
  | coe x =>
    have hu : x.val.1 ∈ generalCellOpenDomain a := by
      have hb : (x : OnePoint (stabilizedCellClosedDomain a k)) ∈ stabilizedCellBoundary a k ↔
          x.val.1 ∉ generalCellOpenDomain a :=
        ClosedPolyhedralCone.coe_mem_compactifiedBoundary_iff (stabilizedCellGap a k) x
      exact not_not.mp (fun hn => hp (hb.mpr hn))
    exact ⟨⟨x.val.1,hu⟩,x.val.2,rfl⟩

theorem stabilizedFuksConeCharacteristic_cover {d m k r : ℕ}
    (x : stabilizedFuksLevel d (m+1) k (r+1)) :
    x ∈ stabilizedFuksLowerSubset d m k r ∨
      ∃ (c : StabilizedFuksCellIndex d m r)
        (p : OnePoint (stabilizedCellClosedDomain c.2.val k)),
        stabilizedFuksConeCharacteristic c p = x := by
  rcases x.property with hx | ⟨⟨y,v⟩,hy,he⟩
  · left
    change x.val ∈ stabilizedFuksLevel d (m+1) k r
    exact hx.symm ▸ stabilizedFuksLevel_infty _ _ _ _
  · by_cases hl : fuksComplexity y < r
    · exact Or.inl (Or.inr ⟨(y,v),hl,he⟩)
    · right
      change fuksComplexity y < r+1 at hy
      have hd : generalCellFuksDegree (configurationAdjacentWord y) = r := by
        rw [generalCellFuksDegree_configurationAdjacentWord]
        omega
      let c : StabilizedFuksCellIndex d m r :=
        (configurationLexOrder y,⟨configurationAdjacentWord y,hd⟩)
      refine ⟨c,((stabilizedCellInterior c.2.val k
        (configurationGeneralCellParameter y) v) : OnePoint _),?_⟩
      apply Subtype.ext
      rw [stabilizedFuksConeCharacteristic_interior]
      exact (congrArg (fun z : Configuration (d+1) (m+1) =>
        ((z,v) : OnePoint (Configuration (d+1) (m+1) × Space k)))
          (configurationGeneralCellParameter_map y)).trans he

theorem stabilizedFuksConeCharacteristic_interior_unique {d m k r : ℕ}
    (c e : StabilizedFuksCellIndex d m r)
    (p : OnePoint (stabilizedCellClosedDomain c.2.val k))
    (q : OnePoint (stabilizedCellClosedDomain e.2.val k))
    (hp : p ∉ stabilizedCellBoundary c.2.val k)
    (he : stabilizedFuksConeCharacteristic c p = stabilizedFuksConeCharacteristic e q) :
    ∃ hce : c = e, hce ▸ p = q := by
  have hq : q ∉ stabilizedCellBoundary e.2.val k := by
    intro hq
    exact hp ((stabilizedFuksConeCharacteristic_mem_lower_iff c p).mp
      (he ▸ (stabilizedFuksConeCharacteristic_mem_lower_iff e q).mpr hq))
  obtain ⟨u,v,rfl⟩ := exists_stabilizedCellInterior_of_not_boundary c.2.val p hp
  obtain ⟨u',v',rfl⟩ := exists_stabilizedCellInterior_of_not_boundary e.2.val q hq
  have hv := congrArg Subtype.val he
  rw [stabilizedFuksConeCharacteristic_interior,stabilizedFuksConeCharacteristic_interior] at hv
  have hpair := OnePoint.coe_injective hv
  have hconf := congrArg Prod.fst hpair
  obtain ⟨hσ,ha⟩ := generalCellRelabelledConfigurationMap_indices_unique
    c.1 e.1 c.2.val e.2.val u u' hconf
  have hce : c = e := Prod.ext hσ (Subtype.ext ha)
  subst e
  refine ⟨rfl,?_⟩
  have huu : u = u' := (isEmbedding_generalCellConfigurationMap c.2.val).injective
    ((relabelConfiguration c.1).injective hconf)
  have hvv : v = v' := congrArg Prod.snd hpair
  cases huu
  cases hvv
  rfl

abbrev StabilizedFuksParameters (m k r : ℕ) := Space (r+(m+1)+k)

theorem finrank_stabilizedCellLinearSpace {d m k r : ℕ}
    (c : StabilizedFuksCellIndex d m r) :
    Module.finrank ℝ (StabilizedCellLinearSpace c.2.val k) = r+(m+1)+k := by
  rw [Module.finrank_prod,finrank_euclideanSpace_fin]
  congr 1
  obtain ⟨u,hu⟩ := generalCellOpenDomain_nonempty c.2.val
  rw [finrank_generalCellLinearSpace_eq_fuksComplexity_add c.2.val ⟨u,hu⟩,
    fuksComplexity_generalCell]
  change generalCellFuksDegree c.2.val + (m+1) = _
  rw [c.2.property]

def stabilizedFuksDiskChange {d m k r : ℕ} (c : StabilizedFuksCellIndex d m r) :
    CellDisk (StabilizedCellLinearSpace c.2.val k) ≃ₜ CellDisk (StabilizedFuksParameters m k r) :=
  (exists_closedBallHomeomorph_pair (ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_stabilizedCellLinearSpace,finrank_euclideanSpace_fin]))).choose

theorem stabilizedFuksDiskChange_boundary_iff {d m k r : ℕ}
    (c : StabilizedFuksCellIndex d m r) (q : CellDisk (StabilizedCellLinearSpace c.2.val k)) :
    ‖(stabilizedFuksDiskChange c q).val‖ = 1 ↔ ‖q.val‖ = 1 :=
  (exists_closedBallHomeomorph_pair (ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_stabilizedCellLinearSpace,finrank_euclideanSpace_fin]))).choose_spec q

def stabilizedFuksCompactDisk {d m k r : ℕ} [NeZero m] (c : StabilizedFuksCellIndex d m r) :
    OnePoint (stabilizedCellClosedDomain c.2.val k) ≃ₜ CellDisk (StabilizedFuksParameters m k r) :=
  (stabilizedCellDisk c.2.val k).trans (stabilizedFuksDiskChange c)

theorem stabilizedFuksCompactDisk_boundary_iff {d m k r : ℕ} [NeZero m]
    (c : StabilizedFuksCellIndex d m r) (p : OnePoint (stabilizedCellClosedDomain c.2.val k)) :
    ‖(stabilizedFuksCompactDisk c p).val‖ = 1 ↔ p ∈ stabilizedCellBoundary c.2.val k := by
  change ‖(stabilizedFuksDiskChange c (stabilizedCellDisk c.2.val k p)).val‖ = 1 ↔ _
  rw [stabilizedFuksDiskChange_boundary_iff,stabilizedCellDisk_boundary_iff]

def stabilizedFuksDiskCharacteristic {d m k r : ℕ} [NeZero m]
    (c : StabilizedFuksCellIndex d m r) :
    C(CellDisk (StabilizedFuksParameters m k r),stabilizedFuksLevel d (m+1) k (r+1)) :=
  (stabilizedFuksConeCharacteristic c).comp
    ⟨(stabilizedFuksCompactDisk c).symm,(stabilizedFuksCompactDisk c).symm.continuous⟩

def stabilizedFuksFiniteAttachment (d m k r : ℕ) [NeZero m] :
    FiniteCellAttachment (StabilizedFuksCellIndex d m r) (StabilizedFuksParameters m k r)
      (stabilizedFuksLevel d (m+1) k (r+1)) (stabilizedFuksLowerSubset d m k r) where
  characteristic := stabilizedFuksDiskCharacteristic
  boundary c q := by
    change stabilizedFuksConeCharacteristic c ((stabilizedFuksCompactDisk c).symm q) ∈ _ ↔ _
    rw [stabilizedFuksConeCharacteristic_mem_lower_iff]
    simpa only [Homeomorph.apply_symm_apply] using
      (stabilizedFuksCompactDisk_boundary_iff c ((stabilizedFuksCompactDisk c).symm q)).symm
  interior_unique c e q s hq he := by
    have hp : (stabilizedFuksCompactDisk c).symm q ∉ stabilizedCellBoundary c.2.val k := by
      rw [← stabilizedFuksCompactDisk_boundary_iff]
      simpa only [Homeomorph.apply_symm_apply] using ne_of_lt hq
    obtain ⟨hce,hqs⟩ := stabilizedFuksConeCharacteristic_interior_unique c e
      ((stabilizedFuksCompactDisk c).symm q) ((stabilizedFuksCompactDisk e).symm s) hp he
    subst e
    exact ⟨rfl,(stabilizedFuksCompactDisk c).symm.injective hqs⟩
  cover x := by
    rcases stabilizedFuksConeCharacteristic_cover x with hx | ⟨c,p,hp⟩
    · exact Or.inl hx
    · right
      refine ⟨c,stabilizedFuksCompactDisk c p,?_⟩
      change stabilizedFuksConeCharacteristic c
        ((stabilizedFuksCompactDisk c).symm (stabilizedFuksCompactDisk c p)) = x
      rw [Homeomorph.symm_apply_apply]
      exact hp

def stabilizedFuksLowerHomeomorph (d m k r : ℕ) :
    stabilizedFuksLevel d (m+1) k r ≃ₜ stabilizedFuksLowerSubset d m k r where
  toFun x := ⟨⟨x.val,stabilizedFuksLevel_mono d (m+1) k (by omega) x.property⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end NRR.PrimePowerTopology
