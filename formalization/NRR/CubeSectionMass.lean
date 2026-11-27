import NRR.CubeProductMoments
import NRR.PartitionMoments
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! True active sections of a high-dimensional convex cell. The results here
establish geometric and integration facts, not the as-yet unproved
Brunn--Minkowski concavity of their cube-root volumes. -/

noncomputable section
open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace NRR.CubeSectionMass

open CubeProductMoments

variable {k : ℕ}

/-- The actual three-dimensional section at a passive parameter. -/
def fiber (C : Set (Active × Passive k)) (u : Passive k) : Set Active :=
  (fun x => (x,u)) ⁻¹' C

/-- Ordinary three-dimensional volume of a section, zero outside its projection. -/
def mass (C : Set (Active × Passive k)) (u : Passive k) : ℝ :=
  volume.real (fiber C u)

def projection (C : Set (Active × Passive k)) : Set (Passive k) :=
  Prod.snd '' C

theorem compact_fiber {C : Set (Active × Passive k)} (hc : IsCompact C) (u : Passive k) :
    IsCompact (fiber C u) := by
  have eq : fiber C u = Prod.fst '' (C ∩ Prod.snd ⁻¹' {u}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x,u),⟨hx,rfl⟩,rfl⟩
    · rintro ⟨⟨y,v⟩,⟨hy,hv⟩,rfl⟩
      exact (show v = u from hv) ▸ hy
  rw [eq]
  exact (hc.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem convex_fiber {C : Set (Active × Passive k)} (hv : Convex ℝ C) (u : Passive k) :
    Convex ℝ (fiber C u) := by
  intro x hx y hy a b ha hb hab
  have h := hv hx hy ha hb hab
  change (a • x + b • y, a • u + b • u) ∈ C at h
  simpa [fiber, ← add_smul, hab] using h

theorem compact_projection {C : Set (Active × Passive k)} (hc : IsCompact C) :
    IsCompact (projection C) := hc.image continuous_snd

theorem convex_projection {C : Set (Active × Passive k)} (hv : Convex ℝ C) :
    Convex ℝ (projection C) :=
  hv.linear_image (LinearMap.snd ℝ Active (Passive k))

theorem fiber_nonempty_iff {C : Set (Active × Passive k)} {u : Passive k} :
    (fiber C u).Nonempty ↔ u ∈ projection C := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨(x,u),hx,rfl⟩
  · rintro ⟨⟨x,v⟩,hx,rfl⟩
    exact ⟨x,hx⟩

theorem mass_nonneg (C : Set (Active × Passive k)) (u : Passive k) : 0 ≤ mass C u :=
  measureReal_nonneg

theorem mass_eq_zero_of_notMem_projection {C : Set (Active × Passive k)}
    {u : Passive k} (hu : u ∉ projection C) : mass C u = 0 := by
  have hf : fiber C u = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun h => hu (fiber_nonempty_iff.mp h))
  simp [mass,hf]

theorem measurable_mass {C : Set (Active × Passive k)} (hc : IsCompact C) :
    Measurable (mass C) :=
  (measurable_measure_prodMk_right (μ := (volume : Measure Active))
    hc.isClosed.measurableSet).ennreal_toReal

theorem mass_le_projection_volume {C : Set (Active × Passive k)} (hc : IsCompact C)
    (u : Passive k) :
    mass C u ≤ volume.real (Prod.fst '' C) := by
  apply measureReal_mono _ (hc.image continuous_fst).measure_lt_top.ne
  intro x hx
  exact ⟨(x,u),hx,rfl⟩

/-- Slice Fubini for an arbitrary passive density, including vector densities. -/
theorem integral_passive_on {C : Set (Active × Passive k)} (hc : IsCompact C)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : Passive k → E)
    (hg : IntegrableOn (fun p : Active × Passive k => g p.2) C volume) :
    (∫ p in C, g p.2 ∂volume) = ∫ u, mass C u • g u ∂volume := by
  have ms := hc.isClosed.measurableSet
  rw [← integral_indicator ms, Measure.volume_eq_prod,
    integral_prod_symm _ (hg.integrable_indicator ms)]
  apply integral_congr_ae (Eventually.of_forall ?_)
  intro u
  have eq : (fun x => C.indicator (fun p => g p.2) (x,u)) =
      (fiber C u).indicator (fun _ => g u) := by
    funext x
    by_cases h : (x,u) ∈ C <;> simp [fiber, h]
  have mf : MeasurableSet (fiber C u) :=
    ms.preimage (by fun_prop : Measurable (fun x : Active => (x,u)))
  rw [eq, integral_indicator mf, setIntegral_const]
  rfl

/-- The total volume is the integral of the actual section volumes. -/
theorem integral_mass {C : Set (Active × Passive k)} (hc : IsCompact C) :
    (∫ u, mass C u ∂volume) = volume.real C := by
  simpa [setIntegral_one_eq_measureReal] using
    (integral_passive_on hc (fun _ => (1 : ℝ))
      (integrableOn_const hc.measure_lt_top.ne)).symm

/-- The passive moment is the moment of the density given by section volume. -/
theorem integral_passive_moment {C : Set (Active × Passive k)} (hc : IsCompact C) :
    (∫ p in C, p.2 ∂volume) = ∫ u, mass C u • u ∂volume :=
  integral_passive_on hc id (continuous_snd.continuousOn.integrableOn_compact hc)

theorem centered_mass {C : Set (Active × Passive k)} (hc : IsCompact C)
    (centered : ∫ p in C, p.2 ∂volume = (0 : Passive k)) :
    (∫ u, mass C u • u ∂volume) = 0 := by
  rw [← integral_passive_moment hc, centered]


/-- Section integration preserves integrability of passive densities. -/
theorem integrable_mass_smul {C : Set (Active × Passive k)} (hc : IsCompact C)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : Passive k → E)
    (hg : IntegrableOn (fun p : Active × Passive k => g p.2) C volume) :
    Integrable (fun u => mass C u • g u) volume := by
  have ms := hc.isClosed.measurableSet
  have h := (hg.integrable_indicator ms).integral_prod_right
  apply h.congr
  filter_upwards with u
  have eq : (fun x => C.indicator (fun p => g p.2) (x,u)) =
      (fiber C u).indicator (fun _ => g u) := by
    funext x
    by_cases h : (x,u) ∈ C <;> simp [fiber,h]
  rw [eq, integral_indicator (compact_fiber hc u).measurableSet, setIntegral_const]
  rfl

theorem integrable_mass {C : Set (Active × Passive k)} (hc : IsCompact C) :
    Integrable (mass C) volume := by
  simpa using integrable_mass_smul hc (fun _ => (1 : ℝ))
    (integrableOn_const hc.measure_lt_top.ne)

theorem integrable_mass_moment {C : Set (Active × Passive k)} (hc : IsCompact C) :
    Integrable (fun u => mass C u • u) volume :=
  integrable_mass_smul hc id (continuous_snd.continuousOn.integrableOn_compact hc)

theorem mass_eq_zero_outside {C : Set (Active × Passive k)} {D : Set Active}
    {E : Set (Passive k)} (sub : C ⊆ D ×ˢ E) {u : Passive k} (hu : u ∉ E) :
    mass C u = 0 := by
  apply mass_eq_zero_of_notMem_projection
  rintro ⟨p,hp,rfl⟩
  exact hu (sub hp).2

theorem integral_mass_on {C : Set (Active × Passive k)} (hc : IsCompact C)
    {D : Set Active} {E : Set (Passive k)} (sub : C ⊆ D ×ˢ E) :
    (∫ u in E, mass C u ∂volume) = volume.real C := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => mass_eq_zero_outside sub hu), integral_mass hc]

/-- The centroid of a positive-volume compact convex cell is an ambient
interior point, not merely a point of its passive projection. -/
theorem centroid_mem_interior {C : Set (Active × Passive k)} (hc : IsCompact C)
    (hv : Convex ℝ C) (hm : 0 < volume.real C) :
    (⨍ p in C, p ∂volume) ∈ interior C := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure Active) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    infer_instance
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Passive k)) :=
    isAddHaarMeasure_volume_pi (Fin k)
  let ρ : Measure (Active × Passive k) := volume
  haveI : Measure.IsAddHaarMeasure ρ := by
    dsimp [ρ]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hρ : ρ.restrict C ≠ 0 := by
    intro hz
    have h := congrArg (fun m : Measure (Active × Passive k) => m univ) hz
    exact (ENNReal.toReal_pos_iff.mp hm).1.ne' (by simpa [ρ] using h)
  letI : IsFiniteMeasure (ρ.restrict C) := isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  have aeInt : ∀ᵐ p ∂ρ.restrict C, p ∈ interior C := by
    have hf : ∀ᵐ p ∂ρ, p ∉ frontier C := compl_mem_ae_iff.mpr
      (hv.addHaar_frontier ρ)
    filter_upwards [ae_restrict_mem hc.measurableSet, ae_restrict_of_ae hf] with p hp hn
    by_contra h
    exact hn ⟨subset_closure hp,h⟩
  by_contra hout
  obtain ⟨F,hF⟩ := geometric_hahn_banach_open_point hv.interior isOpen_interior hout
  have hi : IntegrableOn id C ρ := continuous_id.continuousOn.integrableOn_compact hc
  have hu : IntegrableOn F C ρ := F.continuous.continuousOn.integrableOn_compact hc
  obtain ⟨p,hp,hge⟩ := exists_notMem_null_average_le hρ hu
    (ae_iff.mp aeInt : (ρ.restrict C) (interior C)ᶜ = 0)
  apply not_le_of_gt (hF p (not_not.mp hp))
  convert hge using 1
  rw [average_eq, average_eq, F.map_smul]
  exact congrArg (fun z : ℝ => ((ρ.restrict C).real univ)⁻¹ • z)
    (F.integral_comp_comm hi).symm

/-- Zero passive moment makes the central three-dimensional section meet
the ambient interior of the original cell. -/
theorem exists_central_interior {C : Set (Active × Passive k)} (hc : IsCompact C)
    (hv : Convex ℝ C) (hm : 0 < volume.real C)
    (centered : ∫ p in C, p.2 ∂volume = (0 : Passive k)) :
    ∃ x : Active, (x,0) ∈ interior C := by
  have h := centroid_mem_interior hc hv hm
  have hx : IntegrableOn (fun p : Active × Passive k => p.1) C volume :=
    continuous_fst.continuousOn.integrableOn_compact hc
  have hu : IntegrableOn (fun p : Active × Passive k => p.2) C volume :=
    continuous_snd.continuousOn.integrableOn_compact hc
  rw [setAverage_eq, show (∫ p in C, p ∂volume) =
      ((∫ p in C, p.1 ∂volume),(∫ p in C, p.2 ∂volume))
      from integral_pair hx hu, centered] at h
  exact ⟨_,by simpa only [Prod.smul_mk, smul_zero] using h⟩


/-- Within a passive section which meets the ambient interior, every section
interior point is an ambient interior point. -/
theorem fiber_interior_into_interior {C : Set (Active × Passive k)}
    (hv : Convex ℝ C) {u : Passive k} {q x : Active}
    (hq : (q,u) ∈ interior C) (hx : x ∈ interior (fiber C u)) :
    (x,u) ∈ interior C := by
  have con : Continuous (AffineMap.lineMap q x : ℝ → Active) :=
    AffineMap.lineMap_continuous
  have h1 : AffineMap.lineMap q x (1 : ℝ) = x :=
    by simp
  obtain ⟨t,ht,htmem⟩ :=
    ((con.tendsto' 1 x h1).eventually_mem
      (mem_interior_iff_mem_nhds.mp hx)).exists_gt
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt ht0
  have ha : 0 < 1-t⁻¹ := by
    have hi : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
    linarith
  have hb : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hcomb := hv.combo_interior_self_mem_interior hq
    (show (AffineMap.lineMap q x t,u) ∈ C from htmem)
    ha hb (show (1-t⁻¹)+t⁻¹ = 1 by ring)
  have heq : (1-t⁻¹) • (q,u) + t⁻¹ • (AffineMap.lineMap q x t,u) = (x,u) := by
    apply Prod.ext
    · change (1-t⁻¹) • q + t⁻¹ • AffineMap.lineMap q x t = x
      rw [AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul,
        ← add_assoc, ← add_smul]
      have coeff : (1-t⁻¹)+t⁻¹*(1-t) = 0 := by field_simp; ring
      simp only [coeff, inv_mul_cancel₀ htne, zero_smul, one_smul, zero_add]
    · change (1-t⁻¹) • u + t⁻¹ • u = u
      rw [← add_smul]
      simp
  exact heq ▸ hcomb

theorem mem_fiber_interior_of_mem_interior {C : Set (Active × Passive k)}
    {u : Passive k} {x : Active} (hx : (x,u) ∈ interior C) :
    x ∈ interior (fiber C u) := by
  have hop : IsOpen ((fun y : Active => (y,u)) ⁻¹' interior C) :=
    isOpen_interior.preimage (by fun_prop)
  exact interior_maximal (preimage_mono interior_subset) hop hx

theorem central_fiber_interior_nonempty {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    (centered : ∫ p in C, p.2 ∂volume = (0 : Passive k)) :
    (interior (fiber C 0)).Nonempty := by
  obtain ⟨x,hx⟩ := exists_central_interior hc hv hm centered
  exact ⟨x,mem_fiber_interior_of_mem_interior hx⟩

theorem fiber_covers {n : ℕ} (C : Fin n → Set (Active × Passive k))
    {D : Set Active} {E : Set (Passive k)} (cover : (⋃ i,C i) = D ×ˢ E)
    {u : Passive k} (hu : u ∈ E) :
    (⋃ i,fiber (C i) u) = D := by
  ext x
  simp only [mem_iUnion, fiber, mem_preimage]
  constructor
  · rintro ⟨i,hi⟩
    have h : (x,u) ∈ ⋃ i,C i := mem_iUnion.mpr ⟨i,hi⟩
    exact (cover ▸ h).1
  · intro hx
    have h : (x,u) ∈ D ×ˢ E := ⟨hx,hu⟩
    rw [← cover] at h
    exact mem_iUnion.mp h

/-- The central sections of centered cells have disjoint full-dimensional
interiors; ambient disjointness alone would not imply this on a singular slice. -/
theorem central_fibers_disjoint {n : ℕ} (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i,IsCompact (C i)) (hv : ∀ i,Convex ℝ (C i))
    (hm : ∀ i,0 < volume.real (C i))
    (centered : ∀ i,∫ p in C i,p.2 ∂volume = (0 : Passive k))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j))) :
    Pairwise fun i j => Disjoint (interior (fiber (C i) 0))
      (interior (fiber (C j) 0)) := by
  choose q hq using fun i => exists_central_interior (hc i) (hv i) (hm i) (centered i)
  intro i j hij
  exact Set.disjoint_left.mpr fun x hi hj =>
    Set.disjoint_left.mp (disj hij)
      (fiber_interior_into_interior (hv i) (hq i) hi)
      (fiber_interior_into_interior (hv j) (hq j) hj)


/-- Convexity gives the geometric inclusion to which the three-dimensional
Brunn--Minkowski inequality must subsequently be applied. -/
theorem combo_mem_fiber {C : Set (Active × Passive k)} (hv : Convex ℝ C)
    {u v : Passive k} {x y : Active} (hx : x ∈ fiber C u) (hy : y ∈ fiber C v)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) :
    a • x + b • y ∈ fiber C (a • u + b • v) :=
  hv hx hy ha hb hab

/-- The ordinary volumes of all central sections add to the active parent's
volume. Ambient centering is used to justify disjointness on this exact slice. -/
theorem sum_central_mass {n : ℕ} (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i,IsCompact (C i)) (hv : ∀ i,Convex ℝ (C i))
    (hm : ∀ i,0 < volume.real (C i))
    (centered : ∀ i,∫ p in C i,p.2 ∂volume = (0 : Passive k))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} {E : Set (Passive k)} (cover : (⋃ i,C i) = D ×ˢ E)
    (h0 : (0 : Passive k) ∈ E) :
    (∑ i,mass (C i) 0) = volume.real D := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure Active) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    infer_instance
  have hd := central_fibers_disjoint C hc hv hm centered disj
  have hf (i : Fin n) : volume (frontier (fiber (C i) 0)) = 0 :=
    (convex_fiber (hv i) 0).addHaar_frontier volume
  have hdae : Pairwise fun i j =>
      AEDisjoint volume (fiber (C i) 0) (fiber (C j) 0) := by
    intro i j hij
    apply measure_mono_null _ (measure_union_null (hf i) (hf j))
    intro x hx
    by_cases hi : x ∈ interior (fiber (C i) 0)
    · exact Or.inr ⟨subset_closure hx.2,
        fun hj => Set.disjoint_left.mp (hd hij) hi hj⟩
    · exact Or.inl ⟨subset_closure hx.1,hi⟩
  calc
    _ = (∑ i,volume (fiber (C i) 0)).toReal :=
      (ENNReal.toReal_sum (fun i _ => (compact_fiber (hc i) 0).measure_lt_top.ne)).symm
    _ = volume.real (⋃ i,fiber (C i) 0) := by
      rw [measureReal_def, measure_iUnion₀ hdae
        (fun i => (compact_fiber (hc i) 0).measurableSet.nullMeasurableSet),
        tsum_fintype]
    _ = _ := congrArg (fun A : Set Active => volume.real A) (fiber_covers C cover h0)


theorem zero_mem_interior_projection {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k)) :
    (0 : Passive k) ∈ interior (projection C) := by
  obtain ⟨x,hx⟩ := exists_central_interior hc hv hm centered
  exact isOpenMap_snd.image_interior_subset C ⟨(x,0),hx,rfl⟩

theorem central_mass_pos {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k)) :
    0 < mass C 0 :=
  ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      (central_fiber_interior_nonempty hc hv hm centered)).ne'
    (compact_fiber hc 0).measure_lt_top.ne

/-- Each passive coordinate has zero total moment on the full product cube. -/
theorem integral_passive_cube_coordinate (D : Set Active) (j : Fin k) :
    (∫ p in D ×ˢ passiveCube k,p.2 j ∂volume) = 0 := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_fun_snd (fun u : Passive k => u j),
    integral_passiveCube_coordinate]
  simp

/-- Equality of the extra scalar characteristics forces each one to be zero,
because the genuine closed partition is additive up to null frontiers. -/
theorem coordinate_centered_of_equal {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i,IsCompact (C i)) (hv : ∀ i,Convex ℝ (C i))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i,C i) = D ×ˢ passiveCube k)
    (equal : ∀ i l (j : Fin k),
      (∫ p in C i,p.2 j ∂volume) = ∫ p in C l,p.2 j ∂volume) :
    ∀ i (j : Fin k),(∫ p in C i,p.2 j ∂volume) = 0 := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure Active) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    infer_instance
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Passive k)) :=
    isAddHaarMeasure_volume_pi (Fin k)
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Active × Passive k)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  intro i j
  have hcont : Continuous (fun p : Active × Passive k => p.2 j) :=
    (continuous_apply j).comp continuous_snd
  have parentInt : IntegrableOn (fun p : Active × Passive k => p.2 j)
      (D ×ˢ passiveCube k) volume :=
    hcont.continuousOn.integrableOn_compact (hD.prod isCompact_Icc)
  have balanced : (∑ l,∫ p in C l,p.2 j ∂volume) = 0 := by
    rw [← ConvexLimits.integral_partition volume volume Measure.AbsolutelyContinuous.rfl
      C (fun l => (hc l).isClosed) hv disj cover
      (fun p => p.2 j) parentInt]
    exact integral_passive_cube_coordinate D j
  have hconst : (∑ l,∫ p in C l,p.2 j ∂volume) =
      (n : ℝ)*(∫ p in C i,p.2 j ∂volume) := by
    simp_rw [equal _ i j]
    simp
  rw [hconst] at balanced
  exact (mul_eq_zero.mp balanced).resolve_left (by exact_mod_cast hn.ne')

theorem passive_centered_of_equal {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i,IsCompact (C i)) (hv : ∀ i,Convex ℝ (C i))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i,C i) = D ×ˢ passiveCube k)
    (equal : ∀ i l (j : Fin k),
      (∫ p in C i,p.2 j ∂volume) = ∫ p in C l,p.2 j ∂volume) :
    ∀ i,(∫ p in C i,p.2 ∂volume) = (0 : Passive k) := by
  intro i
  funext j
  have hi : IntegrableOn (fun p : Active × Passive k => p.2) (C i) volume :=
    continuous_snd.continuousOn.integrableOn_compact (hc i)
  have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j).integral_comp_comm hi
  change (∫ p in C i,p.2 j ∂volume) = (∫ p in C i,p.2 ∂volume) j at hcomm
  exact hcomm.symm.trans (coordinate_centered_of_equal hn C hc hv disj hD cover equal i j)


/-- Uniform probability on the passive cube, in every passive dimension. -/
def uniform (k : ℕ) : Measure (Passive k) :=
  (volume (passiveCube k))⁻¹ • volume.restrict (passiveCube k)

theorem passiveCube_compact (k : ℕ) : IsCompact (passiveCube k) :=
  isCompact_Icc

theorem passiveCube_volume_pos (k : ℕ) : 0 < volume (passiveCube k) := by
  have h : (0 : ℝ) < (volume (passiveCube k)).toReal := by
    rw [passiveCube_volume]
    positivity
  exact (ENNReal.toReal_pos_iff.mp h).1

theorem uniform_probability (k : ℕ) : IsProbabilityMeasure (uniform k) := by
  constructor
  simp only [uniform,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (passiveCube_volume_pos k).ne'
    (passiveCube_compact k).measure_lt_top.ne

theorem uniform_ac (k : ℕ) : uniform k ≪ volume :=
  Measure.absolutelyContinuous_restrict.smul_left _

theorem uniform_full (k : ℕ) : uniform k (passiveCube k) = 1 := by
  simp only [uniform,Measure.smul_apply,Measure.restrict_apply_self,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (passiveCube_volume_pos k).ne'
    (passiveCube_compact k).measure_lt_top.ne

/-- With normalized passive probability, the mean section mass has exactly
the ambient cell volume divided by the passive cube's volume. -/
theorem integral_mass_uniform {C : Set (Active × Passive k)} (hc : IsCompact C)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k) :
    (∫ u,mass C u ∂uniform k) = volume.real C / (2 : ℝ)^k := by
  rw [uniform,integral_smul_measure,integral_mass_on hc sub,
    ENNReal.toReal_inv,passiveCube_volume]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem centered_mass_uniform {C : Set (Active × Passive k)} (hc : IsCompact C)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k)) :
    (∫ u,mass C u • u ∂uniform k) = 0 := by
  have outside (u : Passive k) (hu : u ∉ passiveCube k) :
      mass C u • u = 0 := by rw [mass_eq_zero_outside sub hu,zero_smul]
  rw [uniform,integral_smul_measure,
    setIntegral_eq_integral_of_forall_compl_eq_zero outside,centered_mass hc centered,smul_zero]


section Jensen

variable (ν : Measure (Passive k)) [IsProbabilityMeasure ν]

theorem integrable_mass_probability {C : Set (Active × Passive k)} (hc : IsCompact C) :
    Integrable (mass C) ν := by
  refine (integrable_const (volume.real (Prod.fst '' C))).mono'
    (measurable_mass hc).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg C u)]
  exact mass_le_projection_volume hc u

theorem integrable_mass_rpow {C : Set (Active × Passive k)} (hc : IsCompact C)
    {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun u => (mass C u)^p) ν := by
  have cr : Continuous (fun a : ℝ => a^p) :=
    continuous_id.rpow_const (fun _ => Or.inr hp)
  refine (integrable_const ((volume.real (Prod.fst '' C))^p)).mono'
    (cr.measurable.comp (measurable_mass hc)).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (mass_nonneg C u) p)]
  exact Real.rpow_le_rpow (mass_nonneg C u) (mass_le_projection_volume hc u) hp

/-- The ordinary Jensen half of the section-volume estimate is already
available without any geometric concavity assumption. -/
theorem mean_mass_rpow_le_integral_rpow {C : Set (Active × Passive k)}
    (hc : IsCompact C) {p : ℝ} (hp : 1 ≤ p) :
    (∫ u,mass C u ∂ν)^p ≤ ∫ u,(mass C u)^p ∂ν := by
  have cr : Continuous (fun a : ℝ => a^p) :=
    continuous_id.rpow_const (fun _ => Or.inr (zero_le_one.trans hp))
  exact (convexOn_rpow hp).map_integral_le cr.continuousOn isClosed_Ici
    (ae_of_all _ (fun u => mass_nonneg C u))
    (integrable_mass_probability ν hc)
    (integrable_mass_rpow ν hc (zero_le_one.trans hp))

/-- Equality in the strictly convex power mean forces actual section
volumes to be almost everywhere constant on the passive probability space. -/
theorem ae_constant_mass_of_rpow_eq {C : Set (Active × Passive k)}
    (hc : IsCompact C) {p : ℝ} (hp : 1 < p)
    (heq : (∫ u,(mass C u)^p ∂ν) = (∫ u,mass C u ∂ν)^p) :
    ∀ᵐ u ∂ν,mass C u = ∫ v,mass C v ∂ν := by
  have cr : Continuous (fun a : ℝ => a^p) :=
    continuous_id.rpow_const (fun _ => Or.inr (zero_lt_one.trans hp).le)
  rcases (strictConvexOn_rpow hp).ae_eq_const_or_map_average_lt
      cr.continuousOn isClosed_Ici (ae_of_all _ (fun u => mass_nonneg C u))
      (integrable_mass_probability ν hc)
      (integrable_mass_rpow ν hc (zero_lt_one.trans hp).le) with constant | strict
  · simpa only [average_eq_integral,Function.const_apply] using constant
  · rw [average_eq_integral,average_eq_integral] at strict
    exact False.elim ((not_lt_of_ge heq.le) strict)

end Jensen


/-- Equal-volume cells of the actual product partition have the expected
normalized mean section volume, without assuming they are product cells. -/
theorem mean_mass_of_equal_partition {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i,IsCompact (C i)) (hv : ∀ i,Convex ℝ (C i))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i,C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j,volume.real (C i) = volume.real (C j)) (i : Fin n) :
    (∫ u,mass (C i) u ∂uniform k) = volume.real D / (n : ℝ) := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure Active) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    infer_instance
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Passive k)) :=
    isAddHaarMeasure_volume_pi (Fin k)
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Active × Passive k)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have parentInt : IntegrableOn (fun _ : Active × Passive k => (1 : ℝ))
      (D ×ˢ passiveCube k) volume :=
    integrableOn_const (hD.prod (passiveCube_compact k)).measure_lt_top.ne
  have additivity := ConvexLimits.integral_partition volume volume Measure.AbsolutelyContinuous.rfl
    C (fun j => (hc j).isClosed) hv disj cover (fun _ => (1 : ℝ)) parentInt
  simp only [setIntegral_one_eq_measureReal] at additivity
  have total : volume.real (D ×ˢ passiveCube k) =
      volume.real D * (2 : ℝ)^k := by
    rw [Measure.volume_eq_prod,measureReal_prod_prod]
    exact congrArg (fun t : ℝ => volume.real D * t) (passiveCube_volume k)
  have sum : (∑ j,volume.real (C j)) = (n : ℝ)*volume.real (C i) := by
    simp_rw [equal _ i]
    simp
  have sub : C i ⊆ D ×ˢ passiveCube k :=
    cover ▸ subset_iUnion C i
  rw [integral_mass_uniform (hc i) sub]
  apply (div_eq_div_iff (by positivity : (2 : ℝ)^k ≠ 0)
    (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)).mpr
  rw [total,sum] at additivity
  nlinarith [additivity]

end NRR.CubeSectionMass
