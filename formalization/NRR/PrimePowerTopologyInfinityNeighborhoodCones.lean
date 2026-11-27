import NRR.PrimePowerTopologyInfinityNeighborhoodCore

/-! Actual compactified Fox--Neuwirth cones with an arbitrary Euclidean
factor, including the zero dimensional factor. -/

noncomputable section
set_option maxHeartbeats 1600000
open Set Topology Metric Filter
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

def stabilizedConfigurationAmbient (D n k : ℕ) :
    C(Configuration D n × Space k, (Fin n → Space D) × Space k) :=
  ⟨fun p => (p.1.val,p.2),
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

theorem isOpenEmbedding_stabilizedConfigurationAmbient (D n k : ℕ) :
    IsOpenEmbedding (stabilizedConfigurationAmbient D n k) :=
  (isOpen_injectiveSites D n).isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id

def stabilizedConfigurationCollapse (D n k : ℕ) :
    C(OnePoint ((Fin n → Space D) × Space k), OnePoint (Configuration D n × Space k)) :=
  onePointOpenEmbeddingCollapse (stabilizedConfigurationAmbient D n k)
    (isOpenEmbedding_stabilizedConfigurationAmbient D n k)

@[simp] theorem stabilizedConfigurationCollapse_infty (D n k : ℕ) :
    stabilizedConfigurationCollapse D n k ∞ = ∞ :=
  onePointOpenEmbeddingCollapse_infty _ _

theorem stabilizedConfigurationCollapse_injective {D n k : ℕ}
    (x : Fin n → Space D) (v : Space k) (hx : Function.Injective x) :
    stabilizedConfigurationCollapse D n k ((x,v) : OnePoint _) =
      (((⟨x,hx⟩ : Configuration D n),v) : OnePoint _) :=
  onePointOpenEmbeddingCollapse_coe _ _ ((⟨x,hx⟩ : Configuration D n),v)

theorem stabilizedConfigurationCollapse_collision {D n k : ℕ}
    (x : Fin n → Space D) (v : Space k) (hx : ¬ Function.Injective x) :
    stabilizedConfigurationCollapse D n k ((x,v) : OnePoint _) = ∞ := by
  apply onePointOpenEmbeddingCollapse_outside
  rintro ⟨⟨y,w⟩,he⟩
  have hy : y.val = x := congrArg Prod.fst (OnePoint.coe_injective he)
  exact hx (hy ▸ y.property)

def stabilizedConfigurationRelabel {D n k : ℕ} (σ : Equiv.Perm (Fin n)) :
    OnePoint (Configuration D n × Space k) ≃ₜ OnePoint (Configuration D n × Space k) :=
  ((relabelConfiguration σ).prodCongr (Homeomorph.refl (Space k))).onePointCongr

@[simp] theorem stabilizedConfigurationRelabel_infty {D n k : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    stabilizedConfigurationRelabel (D := D) (k := k) σ ∞ = ∞ := rfl

@[simp] theorem stabilizedConfigurationRelabel_coe {D n k : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Configuration D n) (v : Space k) :
    stabilizedConfigurationRelabel σ ((x,v) : OnePoint (Configuration D n × Space k)) =
      ((σ • x,v) : OnePoint _) := rfl

/-- Level zero is just infinity; the next step attaches degree-zero cells.
This convention also handles configurations in one real dimension. -/
def stabilizedFuksLevel (d n k r : ℕ) : Set (OnePoint (Configuration (d+1) n × Space k)) :=
  {∞} ∪ ((↑) '' {p : Configuration (d+1) n × Space k | fuksComplexity p.1 < r})

@[simp] theorem stabilizedFuksLevel_infty (d n k r : ℕ) :
    (∞ : OnePoint (Configuration (d+1) n × Space k)) ∈ stabilizedFuksLevel d n k r :=
  Or.inl rfl

@[simp] theorem stabilizedFuksLevel_coe {d n k r : ℕ}
    (x : Configuration (d+1) n) (v : Space k) :
    ((x,v) : OnePoint (Configuration (d+1) n × Space k)) ∈ stabilizedFuksLevel d n k r ↔
      fuksComplexity x < r := by
  simp [stabilizedFuksLevel]

theorem stabilizedFuksLevel_mono (d n k : ℕ) : Monotone (stabilizedFuksLevel d n k) := by
  intro r s hrs
  apply union_subset_union_right
  apply Set.image_mono
  intro x hx
  exact hx.trans_le hrs

theorem isClosed_stabilizedFuksLevel (d n k r : ℕ) [NeZero n] :
    IsClosed (stabilizedFuksLevel d n k r) := by
  apply (OnePoint.isClosed_iff_of_mem (stabilizedFuksLevel_infty d n k r)).mpr
  have he : ((↑) : Configuration (d+1) n × Space k → OnePoint _) ⁻¹'
      stabilizedFuksLevel d n k r = {p | fuksComplexity p.1 < r} := by
    ext p
    exact stabilizedFuksLevel_coe p.1 p.2
  rw [he]
  cases r with
  | zero => simp
  | succ r =>
    have hs : {p : Configuration (d+1) n × Space k | fuksComplexity p.1 < r+1} =
        Prod.fst ⁻¹' fuksLevel d n r := by
      ext p
      exact Nat.lt_succ_iff.trans (mem_fuksLevel_iff_complexity p.1).symm
    rw [hs]
    exact (isClosed_fuksLevel d n r).preimage continuous_fst

instance compactSpace_stabilizedFuksLevel (d n k r : ℕ) [NeZero n] :
    CompactSpace (stabilizedFuksLevel d n k r) :=
  isCompact_iff_compactSpace.mp (isClosed_stabilizedFuksLevel d n k r).isCompact

theorem stabilizedFuksLevel_zero (d n k : ℕ) :
    stabilizedFuksLevel d n k 0 = {∞} := by simp [stabilizedFuksLevel]

theorem stabilizedFuksLevel_top (d n k : ℕ) [NeZero n] :
    stabilizedFuksLevel d n k (d*n+1) = univ := by
  apply Set.eq_univ_of_forall
  intro p
  induction p using OnePoint.rec with
  | infty => exact stabilizedFuksLevel_infty _ _ _ _
  | coe p =>
    apply (stabilizedFuksLevel_coe p.1 p.2).mpr
    apply Nat.lt_succ_iff.mpr
    apply (mem_fuksLevel_iff_complexity p.1).mp
    rw [fuksLevel_top]
    trivial

theorem stabilizedFuksLevel_relabel_iff {d n k r : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) (p : OnePoint (Configuration (d+1) n × Space k)) :
    stabilizedConfigurationRelabel σ p ∈ stabilizedFuksLevel d n k r ↔
      p ∈ stabilizedFuksLevel d n k r := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe p =>
    rcases p with ⟨x,v⟩
    simp only [stabilizedConfigurationRelabel_coe,stabilizedFuksLevel_coe,
      fuksComplexity_relabel]

abbrev StabilizedCellLinearSpace {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) :=
  generalCellLinearSpace a × Space k

def stabilizedCellGap {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) (i : Fin m) :
    StabilizedCellLinearSpace a k →L[ℝ] ℝ :=
  (generalCellGap a i).comp (ContinuousLinearMap.fst ℝ _ _)

def stabilizedCellClosedDomain {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) :
    Set (StabilizedCellLinearSpace a k) :=
  ClosedPolyhedralCone.carrier (stabilizedCellGap a k)

instance locallyCompact_stabilizedCellClosedDomain {D m : ℕ}
    (a : Fin m → Fin D) (k : ℕ) : LocallyCompactSpace (stabilizedCellClosedDomain a k) :=
  (ClosedPolyhedralCone.isClosed_carrier (stabilizedCellGap a k)).locallyCompactSpace

def stabilizedCellClosedIntoAmbient {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) :
    C(stabilizedCellClosedDomain a k, (Fin (m+1) → Space D) × Space k) :=
  ⟨fun x => (x.val.1.val,x.val.2),
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)⟩

theorem isClosedEmbedding_stabilizedCellClosedIntoAmbient {D m : ℕ}
    (a : Fin m → Fin D) (k : ℕ) : IsClosedEmbedding (stabilizedCellClosedIntoAmbient a k) := by
  let f : StabilizedCellLinearSpace a k →ₗ[ℝ] (Fin (m+1) → Space D) × Space k :=
    (generalCellLinearSpace a).subtype.prodMap (LinearMap.id : Space k →ₗ[ℝ] Space k)
  have hi : Function.Injective f := by
    intro x y he
    change (x.1.val,x.2) = (y.1.val,y.2) at he
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : (Fin (m+1) → Space D) × Space k => z.1) he
    · exact congrArg (fun z : (Fin (m+1) → Space D) × Space k => z.2) he
  exact (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)).comp
    (ClosedPolyhedralCone.isClosed_carrier (stabilizedCellGap a k)).isClosedEmbedding_subtypeVal

def stabilizedCellAttaching {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) :
    C(OnePoint (stabilizedCellClosedDomain a k),
      OnePoint (Configuration D (m+1) × Space k)) :=
  (stabilizedConfigurationCollapse D (m+1) k).comp
    ⟨OnePoint.map (stabilizedCellClosedIntoAmbient a k),
      OnePoint.continuous_map (stabilizedCellClosedIntoAmbient a k).continuous (by
        rw [coclosedCompact_eq_cocompact,coclosedCompact_eq_cocompact]
        exact (isClosedEmbedding_stabilizedCellClosedIntoAmbient a k).tendsto_cocompact)⟩

@[simp] theorem stabilizedCellAttaching_infty {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) :
    stabilizedCellAttaching a k ∞ = ∞ := stabilizedConfigurationCollapse_infty _ _ _

@[simp] theorem stabilizedCellAttaching_coe {D m : ℕ} (a : Fin m → Fin D) (k : ℕ)
    (x : stabilizedCellClosedDomain a k) :
    stabilizedCellAttaching a k (x : OnePoint _) =
      stabilizedConfigurationCollapse D (m+1) k ((x.val.1.val,x.val.2) : OnePoint _) := rfl

def stabilizedCellDisk {D m : ℕ} [NeZero m] (a : Fin m → Fin D) (k : ℕ) :
    OnePoint (stabilizedCellClosedDomain a k) ≃ₜ CellDisk (StabilizedCellLinearSpace a k) :=
  ClosedPolyhedralCone.onePointHomeomorphClosedBall (stabilizedCellGap a k)
    (v := (generalCellDirection a,0))
    (fun i => by change 0 < generalCellGap a i (generalCellDirection a)
                 rw [generalCellGap_direction]; exact zero_lt_one)

def stabilizedCellBoundary {D m : ℕ} (a : Fin m → Fin D) (k : ℕ) :
    Set (OnePoint (stabilizedCellClosedDomain a k)) :=
  ClosedPolyhedralCone.compactifiedBoundary (stabilizedCellGap a k)

theorem stabilizedCellDisk_boundary_iff {D m : ℕ} [NeZero m]
    (a : Fin m → Fin D) (k : ℕ) (p : OnePoint (stabilizedCellClosedDomain a k)) :
    ‖(stabilizedCellDisk a k p).val‖ = 1 ↔ p ∈ stabilizedCellBoundary a k := by
  exact mem_sphere_zero_iff_norm.symm.trans
    (ClosedPolyhedralCone.onePointHomeomorphClosedBall_sphere_iff
      (stabilizedCellGap a k) (v := (generalCellDirection a,0))
      (fun i => by change 0 < generalCellGap a i (generalCellDirection a)
                   rw [generalCellGap_direction]; exact zero_lt_one) p)

theorem stabilizedCellAttaching_mem_level {d m k : ℕ} (a : Fin m → Fin (d+1))
    (p : OnePoint (stabilizedCellClosedDomain a k)) :
    stabilizedCellAttaching a k p ∈ stabilizedFuksLevel d (m+1) k (generalCellFuksDegree a+1) := by
  classical
  induction p using OnePoint.rec with
  | infty => simp
  | coe x =>
    rw [stabilizedCellAttaching_coe]
    by_cases hi : Function.Injective x.val.1.val
    · rw [stabilizedConfigurationCollapse_injective _ _ hi,stabilizedFuksLevel_coe]
      exact Nat.lt_succ_iff.mpr (fuksComplexity_generalCellClosed_le a x.val.1 hi)
    · rw [stabilizedConfigurationCollapse_collision _ _ hi]
      exact stabilizedFuksLevel_infty _ _ _ _

theorem stabilizedCellAttaching_mem_lower_iff {d m k : ℕ}
    (a : Fin m → Fin (d+1)) (p : OnePoint (stabilizedCellClosedDomain a k)) :
    stabilizedCellAttaching a k p ∈ stabilizedFuksLevel d (m+1) k (generalCellFuksDegree a) ↔
      p ∈ stabilizedCellBoundary a k := by
  classical
  induction p using OnePoint.rec with
  | infty =>
    constructor
    · intro _; exact ClosedPolyhedralCone.infty_mem_compactifiedBoundary _
    · intro _; rw [stabilizedCellAttaching_infty]; exact stabilizedFuksLevel_infty _ _ _ _
  | coe x =>
    rw [stabilizedCellAttaching_coe]
    rw [stabilizedCellBoundary,ClosedPolyhedralCone.coe_mem_compactifiedBoundary_iff]
    by_cases hi : Function.Injective x.val.1.val
    · rw [stabilizedConfigurationCollapse_injective _ _ hi,stabilizedFuksLevel_coe]
      constructor
      · intro hl hs
        have he := fuksComplexity_generalCell a ⟨x.val.1,hs⟩
        change fuksComplexity ⟨x.val.1.val,hi⟩ = generalCellFuksDegree a at he
        omega
      · intro hb
        exact fuksComplexity_generalCellClosed_boundary_lt a ⟨x.val.1,x.property⟩ hi hb
    · rw [stabilizedConfigurationCollapse_collision _ _ hi]
      constructor
      · intro _ hs; exact hi (generalCellAmbient_injective a x.val.1 hs)
      · intro _; exact stabilizedFuksLevel_infty _ _ _ _

end NRR.PrimePowerTopology
