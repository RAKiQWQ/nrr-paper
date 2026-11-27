import NRR.CubeSectionJensen
import NRR.CubeSectionTranslation
import NRR.ConvexSectionContinuity

/-! Rigidity of the actual section masses of a centered product partition.
The sole unproved geometric input is explicitly the root-volume concavity
of each real convex cell; no product shape is assumed. -/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace NRR.CubeSectionMass
open CubeProductMoments

variable {k : ℕ}

theorem zero_mem_interior_passiveCube (k : ℕ) :
    (0 : Passive k) ∈ interior (passiveCube k) := by
  have sub : Metric.ball (0 : Passive k) 1 ⊆ passiveCube k := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right] at hu
    constructor <;> intro j
    · have h := (norm_le_pi_norm u j).trans_lt hu
      rw [Real.norm_eq_abs] at h
      exact (abs_lt.mp h).1.le
    · have h := (norm_le_pi_norm u j).trans_lt hu
      rw [Real.norm_eq_abs] at h
      exact (abs_lt.mp h).2.le
  exact interior_maximal sub Metric.isOpen_ball (by simp)

theorem ae_restrict_cube_of_ae_uniform {p : Passive k → Prop}
    (h : ∀ᵐ u ∂uniform k, p u) :
    ∀ᵐ u ∂volume.restrict (passiveCube k), p u := by
  have scale : (volume (passiveCube k))⁻¹ ≠ (0 : ℝ≥0∞) := by
    simp [(passiveCube_compact k).measure_lt_top.ne]
  exact (Measure.ae_smul_measure_iff scale).mp h

/-- Positive almost-everywhere section mass forces the entire closed passive
cube to lie in the actual projection. Thus missing boundary parameters
cannot be concealed in a null exceptional set. -/
theorem projection_eq_cube_of_ae_constant {C : Set (Active × Passive k)}
    (hc : IsCompact C) {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k)
    {M : ℝ} (hM : 0 < M)
    (constant : ∀ᵐ u ∂uniform k, mass C u = M) :
    projection C = passiveCube k := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Passive k)) :=
    isAddHaarMeasure_volume_pi (Fin k)
  have closedP := (compact_projection hc).isClosed
  have aeP : ∀ᵐ u ∂volume.restrict (passiveCube k), u ∈ projection C := by
    filter_upwards [ae_restrict_cube_of_ae_uniform constant] with u hu
    by_contra hp
    have hz := mass_eq_zero_of_notMem_projection hp
    rw [hu] at hz
    exact hM.ne' hz
  have null : volume ((projection C)ᶜ ∩ passiveCube k) = 0 := by
    have h := ae_iff.mp aeP
    change (volume.restrict (passiveCube k)) (projection C)ᶜ = 0 at h
    rwa [Measure.restrict_apply closedP.isOpen_compl.measurableSet] at h
  have nullOpen : volume (interior (passiveCube k) \ projection C) = 0 :=
    measure_mono_null (by
      intro u hu
      exact ⟨hu.2, interior_subset hu.1⟩) null
  have intSub : interior (passiveCube k) ⊆ projection C :=
    diff_eq_empty.mp ((isOpen_interior.sdiff closedP).eq_empty_of_measure_zero nullOpen)
  apply Subset.antisymm
  · rintro u ⟨p,hp,rfl⟩
    exact (sub hp).2
  · have hconv : Convex ℝ (passiveCube k) := convex_Icc _ _
    have dense : closure (interior (passiveCube k)) = passiveCube k :=
      (hconv.closure_interior_eq_closure_of_nonempty_interior
        ⟨0,zero_mem_interior_passiveCube k⟩).trans isClosed_Icc.closure_eq
    rw [← dense]
    exact closedP.closure_subset_iff.mpr intSub

/-- Interior continuity upgrades the actual almost-everywhere section
identity to every interior cube parameter. Boundary mass continuity
is neither assumed nor used. -/
theorem mass_eq_interior_of_ae_constant {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C)
    (full : (interior C).Nonempty)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k)
    {M : ℝ} (hM : 0 < M)
    (constant : ∀ᵐ u ∂uniform k, mass C u = M) :
    projection C = passiveCube k ∧
      ∀ u ∈ interior (passiveCube k), mass C u = M := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Passive k)) :=
    isAddHaarMeasure_volume_pi (Fin k)
  have proj := projection_eq_cube_of_ae_constant hc sub hM constant
  have cont : ContinuousOn (mass C) (interior (passiveCube k)) := by
    have h := ConvexSectionContinuity.continuousOn_mass hc hv full
    change ContinuousOn (mass C) (interior (projection C)) at h
    simpa only [proj] using h
  exact ⟨proj, Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset interior_subset
      (ae_restrict_cube_of_ae_uniform constant))
    isOpen_interior cont continuousOn_const⟩

/-- Ambient interior disjointness does imply section-interior disjointness
at parameters interior to every cell projection. -/
theorem fibers_disjoint_of_interior_projection {n : ℕ}
    (C : Fin n → Set (Active × Passive k))
    (hv : ∀ i, Convex ℝ (C i)) (full : ∀ i, (interior (C i)).Nonempty)
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {u : Passive k} (hu : ∀ i, u ∈ interior (projection (C i))) :
    Pairwise fun i j => Disjoint (interior (fiber (C i) u))
      (interior (fiber (C j) u)) := by
  choose q hq using fun i =>
    ConvexSectionContinuity.exists_interior_over_projection (hv i) (full i) (hu i)
  intro i j hij
  exact Set.disjoint_left.mpr fun x hi hj =>
    Set.disjoint_left.mp (disj hij)
      (fiber_interior_into_interior (hv i) (hq i) hi)
      (fiber_interior_into_interior (hv j) (hq j) hj)

/-- On a genuine centered equal-volume partition, summing the lower Jensen
bounds forces equality for every central section, and hence almost-everywhere
constancy for each actual section mass. -/
theorem central_and_ae_mass_of_concavity {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (centered : ∀ i, ∫ p in C i, p.2 ∂volume = (0 : Passive k))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (concavity : ∀ i, ConcaveOn ℝ (projection (C i)) (rootMass (C i))) :
    ∀ i, mass (C i) 0 = volume.real D / (n : ℝ) ∧
      ∀ᵐ u ∂uniform k, mass (C i) u = volume.real D / (n : ℝ) := by
  classical
  let M : ℝ := volume.real D / (n : ℝ)
  have sub (i) : C i ⊆ D ×ˢ passiveCube k := cover ▸ subset_iUnion C i
  have mean (i) : (∫ u, mass (C i) u ∂uniform k) = M :=
    mean_mass_of_equal_partition hn C hc hv disj hD cover equal i
  have lower (i) : M ≤ mass (C i) 0 := by
    rw [← mean i]
    exact central_mass_lower_of_concavity (hc i) (hv i) (hm i)
      (sub i) (centered i) (concavity i)
  have zeroCube : (0 : Passive k) ∈ passiveCube k :=
    interior_subset (zero_mem_interior_passiveCube k)
  have total := sum_central_mass C hc hv hm centered disj cover zeroCube
  have nM : (n : ℝ)*M = volume.real D := by
    dsimp [M]
    field_simp
  have diffTotal : (∑ i, (mass (C i) 0 - M)) = 0 := by
    rw [Finset.sum_sub_distrib, total]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith [nM]
  have each := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => sub_nonneg.mpr (lower i))).mp diffTotal
  intro i
  have central : mass (C i) 0 = M := sub_eq_zero.mp (each i (Finset.mem_univ i))
  refine ⟨central, ?_⟩
  have ae := ae_constant_mass_of_concavity_of_central_eq
    (hc i) (hv i) (hm i) (sub i) (centered i) (concavity i)
    (central.trans (mean i).symm)
  simpa only [mean i] using ae

/-- The actual cell projections are the whole passive cube and all their
interior sections have precisely the expected equal volume. This theorem
isolates root-volume concavity as the remaining Brunn--Minkowski input. -/
theorem interior_mass_of_partition_concavity {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (centered : ∀ i, ∫ p in C i, p.2 ∂volume = (0 : Passive k))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (concavity : ∀ i, ConcaveOn ℝ (projection (C i)) (rootMass (C i))) :
    ∀ i, projection (C i) = passiveCube k ∧
      ∀ u ∈ interior (passiveCube k), mass (C i) u = volume.real D / (n : ℝ) := by
  have ae := central_and_ae_mass_of_concavity hn C hc hv hm centered disj hD cover equal concavity
  intro i
  have sub : C i ⊆ D ×ˢ passiveCube k := cover ▸ subset_iUnion C i
  have full : (interior (C i)).Nonempty := by
    obtain ⟨x,hx⟩ := exists_central_interior (hc i) (hv i) (hm i) (centered i)
    exact ⟨(x,0),hx⟩
  have positive : 0 < volume.real D / (n : ℝ) := by
    rw [← mean_mass_of_equal_partition hn C hc hv disj hD cover equal i,
      integral_mass_uniform (hc i) sub]
    exact div_pos (hm i) (by positivity)
  exact mass_eq_interior_of_ae_constant (hc i) (hv i) full sub positive (ae i).2


/-- Every interior passive section is itself a genuine convex partition of
the active parent. The section cells have positive equal volume. -/
theorem interior_section_partition_of_concavity {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (centered : ∀ i, ∫ p in C i, p.2 ∂volume = (0 : Passive k))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (concavity : ∀ i, ConcaveOn ℝ (projection (C i)) (rootMass (C i)))
    {u : Passive k} (hu : u ∈ interior (passiveCube k)) :
    CubeSectionTranslation.ConvexFamilyPartition D (fun i => fiber (C i) u) ∧
      (∀ i, (interior (fiber (C i) u)).Nonempty) ∧
      ∀ i, volume.real (fiber (C i) u) = volume.real D / (n : ℝ) := by
  have masses := interior_mass_of_partition_concavity hn C hc hv hm centered disj hD cover equal concavity
  have full (i) : (interior (C i)).Nonempty := by
    obtain ⟨x,hx⟩ := exists_central_interior (hc i) (hv i) (hm i) (centered i)
    exact ⟨(x,0),hx⟩
  have huP (i) : u ∈ interior (projection (C i)) := by
    rw [(masses i).1]
    exact hu
  refine ⟨⟨fun i => (compact_fiber (hc i) u).isClosed,
    fun i => convex_fiber (hv i) u,
    fiber_covers C cover (interior_subset hu),
    fibers_disjoint_of_interior_projection C hv full disj huP⟩, ?_, ?_⟩
  · intro i
    obtain ⟨x,hx⟩ := ConvexSectionContinuity.exists_interior_over_projection
      (hv i) (full i) (huP i)
    exact ⟨x,mem_fiber_interior_of_mem_interior hx⟩
  · exact fun i => (masses i).2 u hu

end NRR.CubeSectionMass
