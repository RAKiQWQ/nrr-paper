import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! One-point compactifications of finite closed polyhedral cones with a
strictly feasible direction. The construction uses radial norm inversion,
then the homeomorphism theorem for bounded convex bodies. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Metric Topology
open scoped OnePoint

namespace NRR.ClosedPolyhedralCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial inversion, available for every real normed space. -/
def normInv (x : E) : E := (‖x‖⁻¹)^2 • x

@[simp] theorem normInv_zero : normInv (0 : E) = 0 := by simp [normInv]

@[simp] theorem norm_normInv (x : E) : ‖normInv x‖ = ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · subst x; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [normInv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  field_simp

@[simp] theorem normInv_normInv (x : E) : normInv (normInv x) = x := by
  by_cases hx : x = 0
  · subst x; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [normInv, norm_normInv, inv_inv, normInv, smul_smul, ← mul_pow,
    mul_inv_cancel₀ hn, one_pow, one_smul]

theorem normInv_ne_zero {x : E} (hx : x ≠ 0) : normInv x ≠ 0 := by
  intro h
  have := congrArg normInv h
  exact hx (by simpa using this)

theorem continuousAt_normInv {x : E} (hx : x ≠ 0) : ContinuousAt normInv x :=
  ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).pow 2).smul
    continuousAt_id

variable {J : Type*} (L : J → E →L[ℝ] ℝ)

def carrier : Set E := {x | ∀ j, 0 ≤ L j x}

def strict : Set E := {x | ∀ j, 0 < L j x}

/-- The bounded convex body obtained after shifting and radial inversion. -/
def rounded (v : E) : Set E := {y | ∀ j, L j v * ‖y‖^2 ≤ L j y}

@[simp] theorem zero_mem_rounded (v : E) : (0 : E) ∈ rounded L v := by
  simp [rounded]

theorem add_direction_ne_zero {v x : E} (hv : ∀ j, 0 < L j v)
    [Nonempty J] (hx : x ∈ carrier L) : x + v ≠ 0 := by
  intro h
  obtain ⟨j⟩ := ‹Nonempty J›
  have hsum : L j x + L j v = 0 := by simpa using congrArg (L j) h
  have := hx j
  linarith [hv j]

theorem normInv_mem_rounded_iff {v z : E} (hz : z ≠ 0) :
    normInv z ∈ rounded L v ↔ ∀ j, L j v ≤ L j z := by
  have hs : 0 < (‖z‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz))
  change (∀ j, L j v * ‖normInv z‖^2 ≤ L j (normInv z)) ↔ _
  simp_rw [norm_normInv]
  simp only [normInv, map_smul, smul_eq_mul]
  constructor
  · intro h j
    exact (mul_le_mul_left hs).mp (by simpa only [mul_comm] using h j)
  · intro h j
    simpa only [mul_comm] using (mul_le_mul_left hs).mpr (h j)

theorem normInv_add_mem_rounded {v x : E} [Nonempty J]
    (hv : ∀ j, 0 < L j v) (hx : x ∈ carrier L) :
    normInv (x+v) ∈ rounded L v := by
  rw [normInv_mem_rounded_iff L (add_direction_ne_zero L hv hx)]
  intro j
  simpa only [map_add, le_add_iff_nonneg_left] using hx j

theorem normInv_sub_mem_carrier {v y : E}
    (hy : y ∈ rounded L v) (hy0 : y ≠ 0) : normInv y - v ∈ carrier L := by
  have h := (normInv_mem_rounded_iff L (normInv_ne_zero hy0)).mp
    (show normInv (normInv y) ∈ rounded L v by simpa using hy)
  intro j
  simpa only [map_sub, sub_nonneg] using h j

theorem isClosed_rounded (v : E) : IsClosed (rounded L v) := by
  simp only [rounded, setOf_forall]
  exact isClosed_iInter fun j =>
    isClosed_le (continuous_const.mul (continuous_norm.pow 2)) (L j).continuous

theorem isBounded_rounded [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    Bornology.IsBounded (rounded L v) := by
  obtain ⟨j⟩ := ‹Nonempty J›
  refine isBounded_iff_forall_norm_le.mpr ⟨‖L j‖ / L j v, ?_⟩
  intro y hy
  have hle : L j y ≤ ‖L j‖ * ‖y‖ := (le_abs_self _).trans ((L j).le_opNorm y)
  apply (le_div_iff₀ (hv j)).mpr
  by_cases hy0 : y = 0
  · subst y; simp
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hi := hy j
  nlinarith

theorem convex_rounded {v : E} (hv : ∀ j, 0 < L j v) : Convex ℝ (rounded L v) := by
  simp only [rounded, setOf_forall]
  apply convex_iInter
  intro j
  have hf : ConvexOn ℝ univ (fun y : E => L j v * ‖y‖^2 - L j y) :=
    (ConvexOn.smul (hv j).le
      (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2)).sub
        ((L j).toLinearMap.concaveOn convex_univ)
  simpa only [mem_univ, true_and, sub_nonpos] using hf.convex_le 0

def strictRounded (v : E) : Set E := {y | ∀ j, L j v * ‖y‖^2 < L j y}

theorem isOpen_strictRounded [Finite J] (v : E) : IsOpen (strictRounded L v) := by
  simp only [strictRounded, setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_const.mul (continuous_norm.pow 2)) (L j).continuous

theorem strictRounded_subset_interior [Finite J] (v : E) :
    strictRounded L v ⊆ interior (rounded L v) := by
  apply interior_maximal _ (isOpen_strictRounded L v)
  intro y hy j
  exact (hy j).le

theorem normInv_mem_strictRounded_iff {v z : E} (hz : z ≠ 0) :
    normInv z ∈ strictRounded L v ↔ ∀ j, L j v < L j z := by
  have hs : 0 < (‖z‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz))
  change (∀ j, L j v * ‖normInv z‖^2 < L j (normInv z)) ↔ _
  simp_rw [norm_normInv]
  simp only [normInv, map_smul, smul_eq_mul]
  constructor
  · intro h j
    exact (mul_lt_mul_left hs).mp (by simpa only [mul_comm] using h j)
  · intro h j
    simpa only [mul_comm] using (mul_lt_mul_left hs).mpr (h j)

theorem interior_rounded_nonempty [Finite J] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) : (interior (rounded L v)).Nonempty := by
  refine ⟨normInv (v+v), strictRounded_subset_interior L v ?_⟩
  rw [normInv_mem_strictRounded_iff L
    (add_direction_ne_zero L hv (fun j => (hv j).le))]
  intro j
  simpa only [map_add, lt_add_iff_pos_left] using hv j

/-- Shifted norm inversion identifies the cone with the punctured body. -/
def inversionChart [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    carrier L ≃ₜ {y : rounded L v // (y : E) ≠ 0} where
  toFun x := ⟨⟨normInv (x.val+v), normInv_add_mem_rounded L hv x.property⟩,
    normInv_ne_zero (add_direction_ne_zero L hv x.property)⟩
  invFun y := ⟨normInv y.val.val - v,
    normInv_sub_mem_carrier L y.val.property y.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; apply Subtype.ext; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun x : carrier L => normInv (x.val+v))
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (continuousAt_normInv (add_direction_ne_zero L hv x.property)).comp
      (f := fun z : carrier L => z.val+v)
      (continuous_subtype_val.continuousAt.add continuousAt_const)
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun y : {y : rounded L v // (y : E) ≠ 0} => normInv y.val.val - v)
    apply Continuous.sub
    · apply continuous_iff_continuousAt.mpr
      intro y
      exact (continuousAt_normInv y.property).comp
        (f := fun z : {y : rounded L v // (y : E) ≠ 0} => z.val.val)
        (continuous_subtype_val.comp continuous_subtype_val).continuousAt
    · exact continuous_const

def inversionMap [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    carrier L → rounded L v := fun x => (inversionChart L hv x).val

theorem isEmbedding_inversionMap [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    IsEmbedding (inversionMap L hv) :=
  IsEmbedding.subtypeVal.comp (inversionChart L hv).isEmbedding

theorem range_inversionMap [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    range (inversionMap L hv) = {⟨0, zero_mem_rounded L v⟩}ᶜ := by
  ext y
  simp only [mem_range, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩ h
    exact (inversionChart L hv x).property (congrArg Subtype.val h)
  · intro hy
    have hy0 : (y : E) ≠ 0 := fun h => hy (Subtype.ext h)
    refine ⟨(inversionChart L hv).symm ⟨y, hy0⟩, ?_⟩
    exact congrArg Subtype.val ((inversionChart L hv).apply_symm_apply ⟨y, hy0⟩)

theorem isCompact_rounded [FiniteDimensional ℝ E] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) : IsCompact (rounded L v) :=
  isCompact_of_isClosed_isBounded (isClosed_rounded L v) (isBounded_rounded L hv)

/-- The actual one-point compactification of the closed cone is the body K. -/
def onePointRoundedHomeomorph [FiniteDimensional ℝ E] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) : OnePoint (carrier L) ≃ₜ rounded L v := by
  letI : CompactSpace (rounded L v) := isCompact_iff_compactSpace.mp (isCompact_rounded L hv)
  exact OnePoint.equivOfIsEmbeddingOfRangeEq ⟨0, zero_mem_rounded L v⟩
    (inversionMap L hv) (isEmbedding_inversionMap L hv) (range_inversionMap L hv)

@[simp] theorem onePointRoundedHomeomorph_infty [FiniteDimensional ℝ E] [Nonempty J]
    {v : E} (hv : ∀ j, 0 < L j v) :
    (onePointRoundedHomeomorph L hv (∞ : OnePoint (carrier L)) : E) = 0 := rfl

@[simp] theorem onePointRoundedHomeomorph_coe [FiniteDimensional ℝ E] [Nonempty J]
    {v : E} (hv : ∀ j, 0 < L j v) (x : carrier L) :
    (onePointRoundedHomeomorph L hv (x : OnePoint (carrier L)) : E) =
      normInv (x.val+v) := rfl

/-- The compactified cone is homeomorphic to the closed unit ball in its
ambient finite-dimensional real normed space. -/
theorem nonempty_onePointHomeomorphClosedBall [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    Nonempty (OnePoint (carrier L) ≃ₜ closedBall (0 : E) 1) := by
  obtain ⟨h, _, hcl, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_rounded L hv) (interior_rounded_nonempty L hv) (isBounded_rounded L hv)
  have himg : h '' rounded L v = closedBall (0 : E) 1 := by
    simpa only [(isClosed_rounded L v).closure_eq] using hcl
  exact ⟨(onePointRoundedHomeomorph L hv).trans
    ((h.image (rounded L v)).trans (Homeomorph.setCongr himg))⟩

theorem functional_surjective {v : E} (hv : ∀ j, 0 < L j v) (j : J) :
    Function.Surjective (L j) := by
  intro a
  refine ⟨(a / L j v) • v, ?_⟩
  simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ (hv j).ne']

theorem mem_interior_halfspace_iff {v : E} (hv : ∀ j, 0 < L j v) (j : J) (x : E) :
    x ∈ interior {z | 0 ≤ L j z} ↔ 0 < L j x := by
  have hop : IsOpenMap (L j) :=
    (L j).toLinearMap.isOpenMap_of_finiteDimensional (functional_surjective L hv j)
  change x ∈ interior ((L j) ⁻¹' Ici 0) ↔ _
  rw [← hop.preimage_interior_eq_interior_preimage (L j).continuous, interior_Ici]
  rfl

/-- Strict feasibility identifies the ambient interior of the cone exactly. -/
theorem interior_carrier [Finite J] {v : E} (hv : ∀ j, 0 < L j v) :
    interior (carrier L) = strict L := by
  ext x
  simp only [carrier, strict, setOf_forall, interior_iInter_of_finite, mem_iInter,
    mem_setOf_eq]
  exact forall_congr' fun j => mem_interior_halfspace_iff L hv j x

theorem isClosed_carrier : IsClosed (carrier L) := by
  simp only [carrier, setOf_forall]
  exact isClosed_iInter fun j => isClosed_le continuous_const (L j).continuous

/-- Thus its topological frontier is exactly the failure of at least one
strict inequality inside the closed cone. -/
theorem frontier_carrier [Finite J] {v : E} (hv : ∀ j, 0 < L j v) :
    frontier (carrier L) = carrier L \ strict L := by
  rw [← closure_diff_interior, (isClosed_carrier L).closure_eq, interior_carrier L hv]

theorem interior_rounded [Finite J] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) : interior (rounded L v) = strictRounded L v := by
  apply Set.Subset.antisymm _ (strictRounded_subset_interior L v)
  intro y hy
  have hL (j : J) : 0 < L j y := by
    apply (mem_interior_halfspace_iff L hv j y).mp
    apply interior_mono (s := rounded L v) (t := {z | 0 ≤ L j z}) _ hy
    intro z hz
    exact (mul_nonneg (hv j).le (sq_nonneg _)).trans (hz j)
  have hy0 : y ≠ 0 := by
    obtain ⟨j⟩ := ‹Nonempty J›
    intro h
    simpa only [h, map_zero, lt_self_iff_false] using hL j
  have hm : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), t • y ∈ rounded L v := by
    have hc : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
    have hnh : rounded L v ∈ 𝓝 ((1 : ℝ) • y) := by
      simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hy
    exact hc.continuousAt.preimage_mem_nhds hnh
  obtain ⟨t, ht, hty⟩ : ∃ t : ℝ, 1 < t ∧ t • y ∈ rounded L v := by
    have hm' : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), t • y ∈ rounded L v :=
      hm.filter_mono nhdsWithin_le_nhds
    have ht' : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), 1 < t := self_mem_nhdsWithin
    exact Filter.Eventually.exists (Filter.Eventually.and ht' hm')
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  intro j
  have hj := hty j
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, map_smul, smul_eq_mul] at hj
  have hc : t * (L j v * ‖y‖^2) ≤ L j y := by
    apply (mul_le_mul_left ht0).mp
    nlinarith only [hj]
  have hp : 0 < L j v * ‖y‖^2 := mul_pos (hv j) (sq_pos_of_pos (norm_pos_iff.mpr hy0))
  have := mul_pos (sub_pos.mpr ht) hp
  nlinarith

theorem onePointRoundedHomeomorph_interior_coe_iff
    [FiniteDimensional ℝ E] [Finite J] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) (x : carrier L) :
    (onePointRoundedHomeomorph L hv (x : OnePoint (carrier L)) : E) ∈
        interior (rounded L v) ↔ x.val ∈ strict L := by
  rw [onePointRoundedHomeomorph_coe, interior_rounded L hv,
    normInv_mem_strictRounded_iff L (add_direction_ne_zero L hv x.property)]
  simp only [strict, map_add, lt_add_iff_pos_left, mem_setOf_eq]

theorem zero_not_mem_interior_rounded [Finite J] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) : (0 : E) ∉ interior (rounded L v) := by
  rw [interior_rounded L hv]
  obtain ⟨j⟩ := ‹Nonempty J›
  intro h
  have := h j
  simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, map_zero, lt_self_iff_false] using this

/-- The compactified boundary is the complement of the finite strict interior. -/
def compactifiedBoundary : Set (OnePoint (carrier L)) :=
  (OnePoint.some '' {x : carrier L | x.val ∈ strict L})ᶜ

@[simp] theorem infty_mem_compactifiedBoundary :
    (∞ : OnePoint (carrier L)) ∈ compactifiedBoundary L := by
  simp [compactifiedBoundary]

@[simp] theorem coe_mem_compactifiedBoundary_iff (x : carrier L) :
    (x : OnePoint (carrier L)) ∈ compactifiedBoundary L ↔ x.val ∉ strict L := by
  simp [compactifiedBoundary]

theorem compactifiedBoundary_eq :
    compactifiedBoundary L = {∞} ∪
      OnePoint.some '' {x : carrier L | x.val ∉ strict L} := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp
  | coe x => simp

theorem compactifiedBoundary_eq_frontier [Finite J] {v : E}
    (hv : ∀ j, 0 < L j v) :
    compactifiedBoundary L = {∞} ∪
      OnePoint.some '' {x : carrier L | x.val ∈ frontier (carrier L)} := by
  rw [compactifiedBoundary_eq]
  congr 1
  congr 1
  ext x
  rw [frontier_carrier L hv]
  simp only [mem_setOf_eq, mem_diff, x.property, true_and]

theorem onePointRoundedHomeomorph_frontier_iff
    [FiniteDimensional ℝ E] [Finite J] [Nonempty J] {v : E}
    (hv : ∀ j, 0 < L j v) (p : OnePoint (carrier L)) :
    (onePointRoundedHomeomorph L hv p : E) ∈ frontier (rounded L v) ↔
      p ∈ compactifiedBoundary L := by
  rw [← closure_diff_interior, (isClosed_rounded L v).closure_eq]
  change ((onePointRoundedHomeomorph L hv p : E) ∈ rounded L v ∧
    (onePointRoundedHomeomorph L hv p : E) ∉ interior (rounded L v)) ↔ _
  simp only [(onePointRoundedHomeomorph L hv p).property, true_and]
  induction p using OnePoint.rec with
  | infty => simp only [onePointRoundedHomeomorph_infty, zero_not_mem_interior_rounded L hv,
      not_false_eq_true, infty_mem_compactifiedBoundary]
  | coe x => rw [onePointRoundedHomeomorph_interior_coe_iff L hv,
      coe_mem_compactifiedBoundary_iff]

/-- The cone compactification is a closed ball as a pair: exactly its
compactified non-strict boundary is carried to the unit sphere. -/
theorem exists_onePointHomeomorphClosedBall_pair [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    ∃ e : OnePoint (carrier L) ≃ₜ closedBall (0 : E) 1,
      ∀ p, (e p : E) ∈ sphere (0 : E) 1 ↔ p ∈ compactifiedBoundary L := by
  obtain ⟨h, _, hcl, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_rounded L hv) (interior_rounded_nonempty L hv) (isBounded_rounded L hv)
  have himg : h '' rounded L v = closedBall (0 : E) 1 := by
    simpa only [(isClosed_rounded L v).closure_eq] using hcl
  refine ⟨(onePointRoundedHomeomorph L hv).trans
    ((h.image (rounded L v)).trans (Homeomorph.setCongr himg)), ?_⟩
  intro p
  change h (onePointRoundedHomeomorph L hv p : E) ∈ sphere (0 : E) 1 ↔ _
  rw [← hfr, h.injective.mem_set_image, onePointRoundedHomeomorph_frontier_iff L hv]

/-- A chosen closed-ball chart, carrying precisely the compactified
topological boundary of the cone to the unit sphere. -/
def onePointHomeomorphClosedBall [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    OnePoint (carrier L) ≃ₜ closedBall (0 : E) 1 :=
  (exists_onePointHomeomorphClosedBall_pair L hv).choose

theorem onePointHomeomorphClosedBall_sphere_iff [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v)
    (p : OnePoint (carrier L)) :
    (onePointHomeomorphClosedBall L hv p : E) ∈ sphere (0 : E) 1 ↔
      p ∈ compactifiedBoundary L :=
  (exists_onePointHomeomorphClosedBall_pair L hv).choose_spec p

@[simp] theorem onePointHomeomorphClosedBall_infty_mem_sphere [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    (onePointHomeomorphClosedBall L hv (∞ : OnePoint (carrier L)) : E) ∈
      sphere (0 : E) 1 :=
  (onePointHomeomorphClosedBall_sphere_iff L hv ∞).mpr (infty_mem_compactifiedBoundary L)

@[simp] theorem onePointHomeomorphClosedBall_coe_mem_sphere_iff [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) (x : carrier L) :
    (onePointHomeomorphClosedBall L hv (x : OnePoint (carrier L)) : E) ∈
      sphere (0 : E) 1 ↔ ¬ ∀ j, 0 < L j x.val := by
  rw [onePointHomeomorphClosedBall_sphere_iff, coe_mem_compactifiedBoundary_iff]
  rfl

theorem onePointHomeomorphClosedBall_image_boundary [FiniteDimensional ℝ E]
    [Finite J] [Nonempty J] {v : E} (hv : ∀ j, 0 < L j v) :
    onePointHomeomorphClosedBall L hv '' compactifiedBoundary L =
      {y : closedBall (0 : E) 1 | (y : E) ∈ sphere (0 : E) 1} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (onePointHomeomorphClosedBall_sphere_iff L hv p).mpr hp
  · intro hy
    refine ⟨(onePointHomeomorphClosedBall L hv).symm y, ?_,
      (onePointHomeomorphClosedBall L hv).apply_symm_apply y⟩
    apply (onePointHomeomorphClosedBall_sphere_iff L hv _).mp
    simpa only [Homeomorph.apply_symm_apply] using hy

end NRR.ClosedPolyhedralCone
