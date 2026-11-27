import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Interior continuity of actual convex-body section volumes.
The proof uses convexity, compactness and dominated convergence, without
Brunn--Minkowski or continuity at the boundary of the projection. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.ConvexSectionContinuity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fiber (C : Set (E × F)) (u : F) : Set E := {x | (x,u) ∈ C}

theorem compact_fiber {C : Set (E × F)} (hc : IsCompact C) (u : F) :
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

theorem convex_fiber {C : Set (E × F)} (hv : Convex ℝ C) (u : F) :
    Convex ℝ (fiber C u) := by
  intro x hx y hy s t hs ht hst
  have h := hv hx hy hs ht hst
  change (s • x+t • y,s • u+t • u) ∈ C at h
  simpa only [← add_smul,hst,one_smul] using h

/-- Over an interior projection point, a full-dimensional convex set has
an actual ambient interior point in the prescribed section. -/
theorem exists_interior_over_projection {C : Set (E × F)}
    (hv : Convex ℝ C) (full : (interior C).Nonempty) {u : F}
    (hu : u ∈ interior (Prod.snd '' C)) :
    ∃ x : E, (x,u) ∈ interior C := by
  obtain ⟨⟨q,v⟩,hq⟩ := full
  have con : Continuous (AffineMap.lineMap v u : ℝ → F) :=
    AffineMap.lineMap_continuous
  have h1 : AffineMap.lineMap v u (1 : ℝ) = u := by simp
  obtain ⟨t,ht,htmem⟩ :=
    ((con.tendsto' 1 u h1).eventually_mem
      (mem_interior_iff_mem_nhds.mp hu)).exists_gt
  obtain ⟨⟨x,w⟩,hx,he⟩ := htmem
  change w = AffineMap.lineMap v u t at he
  subst w
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ht0.ne'
  have ha : 0 < 1-t⁻¹ := by
    have hi : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
    linarith
  have comb := hv.combo_interior_self_mem_interior hq hx ha
    (inv_nonneg.mpr ht0.le) (show (1-t⁻¹)+t⁻¹ = 1 by ring)
  have passive : (1-t⁻¹) • v+t⁻¹ • AffineMap.lineMap v u t = u := by
    rw [AffineMap.lineMap_apply_module,smul_add,smul_smul,smul_smul,
      ← add_assoc,← add_smul]
    have coeff : (1-t⁻¹)+t⁻¹*(1-t) = 0 := by field_simp; ring
    simp only [coeff,inv_mul_cancel₀ htne,zero_smul,one_smul,zero_add]
  refine ⟨(1-t⁻¹) • q+t⁻¹ • x,?_⟩
  simpa only [Prod.smul_mk,Prod.mk_add_mk,passive] using comb

/-- An ambient interior point in a section transports every relative
section interior point into the ambient interior. -/
theorem fiber_interior_into_interior {C : Set (E × F)} (hv : Convex ℝ C)
    {u : F} {q x : E} (hq : (q,u) ∈ interior C)
    (hx : x ∈ interior (fiber C u)) : (x,u) ∈ interior C := by
  have con : Continuous (AffineMap.lineMap q x : ℝ → E) :=
    AffineMap.lineMap_continuous
  have h1 : AffineMap.lineMap q x (1 : ℝ) = x := by simp
  obtain ⟨t,ht,htmem⟩ :=
    ((con.tendsto' 1 x h1).eventually_mem
      (mem_interior_iff_mem_nhds.mp hx)).exists_gt
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ht0.ne'
  have ha : 0 < 1-t⁻¹ := by
    have hi : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
    linarith
  have comb := hv.combo_interior_self_mem_interior hq
    (show (AffineMap.lineMap q x t,u) ∈ C from htmem)
    ha (inv_nonneg.mpr ht0.le) (show (1-t⁻¹)+t⁻¹ = 1 by ring)
  have active : (1-t⁻¹) • q+t⁻¹ • AffineMap.lineMap q x t = x := by
    rw [AffineMap.lineMap_apply_module,smul_add,smul_smul,smul_smul,
      ← add_assoc,← add_smul]
    have coeff : (1-t⁻¹)+t⁻¹*(1-t) = 0 := by field_simp; ring
    simp only [coeff,inv_mul_cancel₀ htne,zero_smul,one_smul,zero_add]
  have passive : (1-t⁻¹) • u+t⁻¹ • u = u := by
    rw [← add_smul]
    simp
  simpa only [Prod.smul_mk,Prod.mk_add_mk,active,passive] using comb

/-- Away from the section frontier, membership stabilizes as the passive
parameter tends to a point in the interior of the projection. -/
theorem eventually_mem_fiber_iff {C : Set (E × F)}
    (closed : IsClosed C) (convex : Convex ℝ C)
    {u : F} (full : ∃ q : E, (q,u) ∈ interior C)
    {x : E} (notFrontier : x ∉ frontier (fiber C u)) :
    ∀ᶠ v in 𝓝 u, (x ∈ fiber C v ↔ x ∈ fiber C u) := by
  by_cases hx : x ∈ fiber C u
  · have inside : x ∈ interior (fiber C u) := by
      by_contra h
      exact notFrontier ⟨subset_closure hx,h⟩
    obtain ⟨q,hq⟩ := full
    have ambient := fiber_interior_into_interior convex hq inside
    have near : ∀ᶠ v in 𝓝 u, (x,v) ∈ interior C :=
      (isOpen_interior.preimage (continuous_const.prodMk continuous_id)).mem_nhds ambient
    filter_upwards [near] with v hv
    exact iff_of_true (show (x,v) ∈ C from interior_subset hv) hx
  · have near : ∀ᶠ v in 𝓝 u, (x,v) ∉ C :=
      (closed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx
    filter_upwards [near] with v hv
    exact iff_of_false hv hx

section Volume

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Section mass is continuous in the interior of the passive projection.
No claim of boundary continuity is made. -/
theorem continuousOn_mass {C : Set (E × F)}
    (compact : IsCompact C) (convex : Convex ℝ C)
    (full : (interior C).Nonempty) :
    ContinuousOn (fun u : F => volume.real (fiber C u))
      (interior (Prod.snd '' C)) := by
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_iff_seqContinuous.mpr ?_
  intro seq u converge
  have conv : Tendsto (fun n => (seq n).val) atTop (𝓝 u.val) :=
    (continuous_subtype_val.tendsto u).comp converge
  have fullSection := exists_interior_over_projection convex full u.property
  let K : Set E := Prod.fst '' C
  have compactK : IsCompact K := compact.image continuous_fst
  let bound : E → ℝ := K.indicator (fun _ => 1)
  have integrableBound : Integrable bound :=
    (continuous_const.continuousOn.integrableOn_compact compactK).integrable_indicator
      compactK.isClosed.measurableSet
  let f (n : ℕ) : E → ℝ := (fiber C (seq n).val).indicator (fun _ => 1)
  have measurableF (n : ℕ) : AEStronglyMeasurable (f n) volume :=
    stronglyMeasurable_const.aestronglyMeasurable.indicator
      (compact_fiber compact _).isClosed.measurableSet
  have domination (n : ℕ) : ∀ᵐ x ∂volume, ‖f n x‖ ≤ bound x := by
    filter_upwards with x
    by_cases hx : x ∈ fiber C (seq n).val
    · have hk : x ∈ K := ⟨(x,(seq n).val),hx,rfl⟩
      simp only [f,bound,indicator_of_mem hx,indicator_of_mem hk,norm_one,le_refl]
    · have hn : 0 ≤ bound x := by
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
      simpa only [f,indicator_of_notMem hx,norm_zero] using hn
  have notFrontier : ∀ᵐ x ∂volume, x ∉ frontier (fiber C u.val) :=
    compl_mem_ae_iff.mpr ((convex_fiber convex u.val).addHaar_frontier volume)
  have limit : ∀ᵐ x ∂volume,
      Tendsto (fun n => f n x) atTop
        (𝓝 ((fiber C u.val).indicator (fun _ => (1 : ℝ)) x)) := by
    filter_upwards [notFrontier] with x hx
    have stable := conv.eventually
      (eventually_mem_fiber_iff compact.isClosed convex fullSection hx)
    apply tendsto_const_nhds.congr'
    filter_upwards [stable] with n hn
    by_cases hmem : x ∈ fiber C u.val
    · simp only [f,indicator_of_mem hmem,indicator_of_mem (hn.mpr hmem)]
    · simp only [f,indicator_of_notMem hmem,
        indicator_of_notMem (fun h => hmem (hn.mp h))]
  have result := tendsto_integral_of_dominated_convergence bound measurableF
    integrableBound domination limit
  have identity (v : F) :
      (∫ x, (fiber C v).indicator (fun _ => (1 : ℝ)) x) = volume.real (fiber C v) := by
    rw [integral_indicator (compact_fiber compact v).isClosed.measurableSet,
      setIntegral_one_eq_measureReal]
  simpa only [f,identity,Set.restrict_apply] using result

end Volume

end NRR.ConvexSectionContinuity
