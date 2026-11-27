import NRR.Geometry
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Vertical fibres of convex pieces in a product cylinder. -/

noncomputable section
open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace NRR.Cylinder
variable {d : ℕ}

def fiber (C : Set (Space d × ℝ)) (u : Space d) : Set ℝ := Prod.mk u ⁻¹' C

def length (C : Set (Space d × ℝ)) (u : Space d) : ℝ := volume.real (fiber C u)

private theorem compact_fiber {C : Set (Space d × ℝ)} (hc : IsCompact C) (u : Space d) :
    IsCompact (fiber C u) := by
  have e : fiber C u = Prod.snd '' (C ∩ Prod.fst ⁻¹' {u}) := by
    ext t
    constructor
    · intro ht
      exact ⟨(u,t), ⟨ht, rfl⟩, rfl⟩
    · rintro ⟨⟨x,y⟩, ⟨hxy, hx⟩, rfl⟩
      exact (show x = u from hx) ▸ hxy
  rw [e]
  exact (hc.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd

private theorem interval_fiber {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    {u : Space d} (hne : (fiber C u).Nonempty) :
    ∃ a b, a ≤ b ∧ fiber C u = Icc a b := by
  have cv : Convex ℝ (fiber C u) := by
    intro a ha b hb s t hs ht hst
    have h := hv ha hb hs ht hst
    change (s • u + t • u, s • a + t • b) ∈ C at h
    simpa [← add_smul, hst, fiber] using h
  exact ⟨_, _, (csInf_le_csSup (compact_fiber hc u).bddBelow (compact_fiber hc u).bddAbove hne),
    eq_Icc_of_connected_compact (cv.isConnected hne) (compact_fiber hc u)⟩

/-- Vertical differences of points lying in the same fibre. -/
private def differences (C : Set (Space d × ℝ)) : Set (Space d × ℝ) :=
  {p | ∃ s t : ℝ, (p.1,s) ∈ C ∧ (p.1,t) ∈ C ∧ p.2 = s-t}

private theorem compact_differences {C : Set (Space d × ℝ)} (hc : IsCompact C) :
    IsCompact (differences C) := by
  let B := (C ×ˢ C) ∩ {p : (Space d × ℝ) × (Space d × ℝ) | p.1.1 = p.2.1}
  let f := fun p : (Space d × ℝ) × (Space d × ℝ) => (p.1.1, p.1.2 - p.2.2)
  have eq : differences C = f '' B := by
    ext ⟨u,z⟩
    constructor
    · rintro ⟨s,t,hs,ht,rfl⟩
      exact ⟨((u,s),(u,t)), ⟨⟨hs,ht⟩,rfl⟩,rfl⟩
    · rintro ⟨⟨⟨v,s⟩,⟨w,t⟩⟩, ⟨⟨hs,ht⟩, he⟩, h⟩
      obtain rfl : v = w := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨s,t,hs,ht,rfl⟩
  rw [eq]
  exact ((hc.prod hc).inter_right (isClosed_eq (by fun_prop) (by fun_prop))).image (by fun_prop)

private theorem convex_differences {C : Set (Space d × ℝ)} (hv : Convex ℝ C) :
    Convex ℝ (differences C) := by
  rintro ⟨u,z⟩ ⟨a,b,ha,hb,rfl⟩ ⟨v,w⟩ ⟨c,e,hc,he,rfl⟩ s t hs ht hst
  refine ⟨s * a + t * c, s * b + t * e, hv ha hc hs ht hst, hv hb he hs ht hst, ?_⟩
  change s * (a-b) + t * (c-e) = _
  ring

private theorem length_mem {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    {u : Space d} (hne : (fiber C u).Nonempty) : (u, length C u) ∈ differences C := by
  obtain ⟨a,b,hab,eq⟩ := interval_fiber hc hv hne
  exact ⟨b,a, show b ∈ fiber C u from eq ▸ right_mem_Icc.mpr hab,
    show a ∈ fiber C u from eq ▸ left_mem_Icc.mpr hab, by
      simp only [length, eq, Real.volume_real_Icc_of_le hab]⟩

private theorem le_length {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    {u : Space d} {z : ℝ} (hz : (u,z) ∈ differences C) : z ≤ length C u := by
  obtain ⟨s,t,hs,ht,rfl⟩ := hz
  obtain ⟨a,b,hab,eq⟩ := interval_fiber hc hv (show (fiber C u).Nonempty from ⟨s,hs⟩)
  have hs' : s ∈ Icc a b := eq ▸ hs
  have ht' : t ∈ Icc a b := eq ▸ ht
  simpa [length, eq, Real.volume_real_Icc_of_le hab] using sub_le_sub hs'.2 ht'.1

private theorem integral_fst_on (ν : Measure (Space d)) [IsFiniteMeasure ν]
    {C : Set (Space d × ℝ)} (hc : IsCompact C) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (g : Space d → E)
    (hg : IntegrableOn (fun p : Space d × ℝ => g p.1) C (ν.prod volume)) :
    ∫ p in C, g p.1 ∂(ν.prod volume) = ∫ u, length C u • g u ∂ν := by
  have ms := hc.isClosed.measurableSet
  rw [← integral_indicator ms, integral_prod _ (hg.integrable_indicator ms)]
  apply integral_congr_ae (Eventually.of_forall ?_)
  intro u
  have eq : (fun t => C.indicator (fun p => g p.1) (u,t)) =
      (fiber C u).indicator (fun _ => g u) := by
    funext t
    by_cases h : (u,t) ∈ C <;> simp [Set.indicator, fiber, h]
  have mfu : MeasurableSet (fiber C u) := ms.preimage (by fun_prop : Measurable (Prod.mk u))
  rw [eq, integral_indicator mfu, setIntegral_const]
  rfl

private theorem measurable_length {C : Set (Space d × ℝ)} (hc : IsCompact C) :
    Measurable (length C) :=
  (measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hc.isClosed.measurableSet).ennreal_toReal

private theorem bounded_length {C : Set (Space d × ℝ)} (hc : IsCompact C) :
    ∃ M : ℝ, ∀ u, ‖length C u‖ ≤ M := by
  obtain ⟨R, _, hR⟩ := (hc.image continuous_snd).isBounded.exists_pos_norm_le
  refine ⟨volume.real (Icc (-R) R), fun u => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ length C u from measureReal_nonneg)]
  apply measureReal_mono _ isCompact_Icc.measure_lt_top.ne
  intro t ht
  exact abs_le.mp (hR _ (mem_image_of_mem Prod.snd (show (u,t) ∈ C from ht)))

theorem integral_length (ν : Measure (Space d)) [IsFiniteMeasure ν] {C : Set (Space d × ℝ)}
    (hc : IsCompact C) : ∫ u, length C u ∂ν = (ν.prod volume).real C := by
  simpa [setIntegral_one_eq_measureReal] using (integral_fst_on ν hc (fun _ => (1 : ℝ))
    (integrableOn_const hc.measure_lt_top.ne)).symm

/-- The upper and lower points of each vertical fibre define a point of the
compact convex set of vertical differences. Averaging this point across the
piece locates its mean squared fibre length on the central fibre. -/
theorem integral_sq_le_central (ν : Measure (Space d)) [IsFiniteMeasure ν]
    {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    (hm : 0 < (ν.prod volume).real C)
    (centered : ∫ p in C, p.1 ∂(ν.prod volume) = (0 : Space d)) :
    (∫ u, (length C u)^2 ∂ν) ≤ (ν.prod volume).real C * length C 0 := by
  let ρ := ν.prod (volume : Measure ℝ)
  obtain ⟨M, hM⟩ := bounded_length hc
  have ht : IntegrableOn (fun p : Space d × ℝ => length C p.1) C ρ := by
    apply (integrableOn_const (C := M) (hc.measure_lt_top (μ := ρ)).ne).mono'
      ((measurable_length hc).comp measurable_fst).aestronglyMeasurable
    exact Eventually.of_forall fun p => hM p.1
  have hx : IntegrableOn (fun p : Space d × ℝ => p.1) C ρ :=
    continuous_fst.continuousOn.integrableOn_compact hc
  have good : ∀ᵐ p ∂ρ.restrict C, (p.1, length C p.1) ∈ differences C := by
    filter_upwards [ae_restrict_mem hc.isClosed.measurableSet] with p hp
    exact length_mem hc hv ⟨p.2,hp⟩
  have avg := (convex_differences hv).set_average_mem (compact_differences hc).isClosed
    (ENNReal.toReal_pos_iff.mp hm).1.ne' (hc.measure_lt_top (μ := ρ)).ne good (hx.prodMk ht)
  rw [setAverage_eq, integral_pair hx ht, centered] at avg
  have hs : (∫ p in C, length C p.1 ∂ρ) = ∫ u, (length C u)^2 ∂ν := by
    simpa [sq] using integral_fst_on ν hc (length C) ht
  rw [hs] at avg
  have inequality : ((ν.prod volume).real C)⁻¹ * (∫ u, (length C u)^2 ∂ν) ≤ length C 0 :=
    le_length hc hv (by simpa using avg)
  rwa [← div_eq_inv_mul, div_le_iff₀ hm, mul_comm (length C 0)] at inequality

private theorem variance_identity {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : X → ℝ) (hf : Integrable f ν)
    (hf2 : Integrable (fun x => f x ^ 2) ν) :
    (∫ x, (f x - (∫ y, f y ∂ν))^2 ∂ν) =
    (∫ x, f x^2 ∂ν) - (∫ x, f x ∂ν)^2 := by
  let a := ∫ x, f x ∂ν
  have he (x) : (f x - a)^2 = f x^2 - (2*a) * f x + a^2 := by ring
  change (∫ x, (f x-a)^2 ∂ν) = _ - a^2
  simp_rw [he]
  have hdiff : Integrable (fun x => f x^2 - (2*a)*f x) ν := hf2.sub (hf.const_mul _)
  rw [integral_add hdiff (integrable_const (a^2)),
    integral_sub hf2 (hf.const_mul _), integral_const_mul]
  simp [a]
  ring

private theorem integrable_length_sq (ν : Measure (Space d)) [IsFiniteMeasure ν]
    {C : Set (Space d × ℝ)} (hc : IsCompact C) :
    Integrable (length C) ν ∧ Integrable (fun u => length C u ^ 2) ν := by
  obtain ⟨M, hM⟩ := bounded_length hc
  have h1 := Measure.integrable_measure_prodMk_left (μ := ν) (ν := (volume : Measure ℝ))
    hc.isClosed.measurableSet hc.measure_lt_top.ne
  refine ⟨h1, ?_⟩
  simpa [sq] using (show Integrable (fun u => length C u) ν from h1).bdd_mul
    (measurable_length hc).aestronglyMeasurable ⟨M,hM⟩

theorem mean_sq_le_integral_sq (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    {C : Set (Space d × ℝ)} (hc : IsCompact C) :
    ((ν.prod volume).real C)^2 ≤ ∫ u, (length C u)^2 ∂ν := by
  obtain ⟨h1,h2⟩ := integrable_length_sq ν hc
  have hvar := variance_identity ν (length C) h1 h2
  rw [integral_length ν hc] at hvar
  linarith [integral_nonneg (μ := ν) (fun u => sq_nonneg (length C u - (ν.prod volume).real C))]

theorem ae_const_of_sq_eq (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    {C : Set (Space d × ℝ)} (hc : IsCompact C)
    (heq : ∫ u, length C u^2 ∂ν = ((ν.prod volume).real C)^2) :
    ∀ᵐ u ∂ν, length C u = (ν.prod volume).real C := by
  let a := (ν.prod volume).real C
  obtain ⟨h1,h2⟩ := integrable_length_sq ν hc
  have hsq : Integrable (fun u => (length C u-a)^2) ν := by
    have h := (h2.sub (h1.const_mul (2*a))).add (integrable_const (a^2))
    refine h.congr (Eventually.of_forall fun u => ?_)
    change length C u ^ 2 - 2*a*length C u + a^2 = (length C u-a)^2
    ring
  have hvar := variance_identity ν (length C) h1 h2
  rw [integral_length ν hc, heq, sub_self] at hvar
  have hn := (integral_eq_zero_iff_of_nonneg (f := fun u => (length C u-a)^2)
    (fun u => sq_nonneg _) hsq).mp hvar
  filter_upwards [hn] with u hu
  exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hu)

private theorem centroid_interior (ν : Measure (Space d)) [IsFiniteMeasure ν]
    (hν : ν ≪ volume) {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    (hm : 0 < (ν.prod volume).real C) :
    (⨍ p in C, p ∂(ν.prod volume)) ∈ interior C := by
  let ρ := ν.prod (volume : Measure ℝ)
  have hac : ρ ≪ volume := hν.prod Measure.AbsolutelyContinuous.rfl
  have hρ : (ρ.restrict C) ≠ 0 := by
    intro hz
    have h := congrArg (fun m : Measure (Space d × ℝ) => m Set.univ) hz
    exact (ENNReal.toReal_pos_iff.mp hm).1.ne' (by simpa using h)
  letI : IsFiniteMeasure (ρ.restrict C) := isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  have aeInt : ∀ᵐ p ∂ρ.restrict C, p ∈ interior C := by
    have hf : ∀ᵐ p ∂ρ, p ∉ frontier C := compl_mem_ae_iff.mpr
      (hac (hv.addHaar_frontier ((volume : Measure (Space d)).prod (volume : Measure ℝ))))
    filter_upwards [ae_restrict_mem hc.isClosed.measurableSet, ae_restrict_of_ae hf] with p hp hn
    by_contra h
    exact hn ⟨subset_closure hp,h⟩
  by_contra hout
  obtain ⟨F,hF⟩ := geometric_hahn_banach_open_point hv.interior isOpen_interior hout
  have hi : IntegrableOn id C ρ := continuous_id.continuousOn.integrableOn_compact hc
  have hu : IntegrableOn F C ρ := F.continuous.continuousOn.integrableOn_compact hc
  obtain ⟨p,hp,hge⟩ := exists_notMem_null_average_le hρ hu
    (ae_iff.mp aeInt : (ρ.restrict C) (interior C)ᶜ = 0)
  apply (not_le_of_gt (hF p (not_not.mp hp))) -- average of F is F of the centroid
  convert hge using 1
  rw [average_eq, average_eq, F.map_smul]
  exact congrArg (fun z : ℝ => ((ρ.restrict C).real univ)⁻¹ • z) (F.integral_comp_comm hi).symm

/-- The central line meets the interior of every positive-mass convex piece
whose horizontal moment vanishes. -/
theorem exists_axis_interior (ν : Measure (Space d)) [IsFiniteMeasure ν]
    (hν : ν ≪ volume) {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    (hm : 0 < (ν.prod volume).real C)
    (centered : ∫ p in C, p.1 ∂(ν.prod volume) = (0 : Space d)) :
    ∃ t : ℝ, (0,t) ∈ interior C := by
  have h := centroid_interior ν hν hc hv hm
  have hx : IntegrableOn (fun p : Space d × ℝ => p.1) C (ν.prod volume) :=
    continuous_fst.continuousOn.integrableOn_compact hc
  have hz : IntegrableOn (fun p : Space d × ℝ => p.2) C (ν.prod volume) :=
    continuous_snd.continuousOn.integrableOn_compact hc
  rw [setAverage_eq, show (∫ p in C, p ∂(ν.prod volume)) =
    ((∫ p in C, p.1 ∂(ν.prod volume)),(∫ p in C, p.2 ∂(ν.prod volume))) from integral_pair hx hz,
    centered] at h
  exact ⟨_, by simpa only [Prod.smul_mk, smul_zero] using h⟩

private theorem fiber_int_into_int {C : Set (Space d × ℝ)} (hc : IsCompact C) (hv : Convex ℝ C)
    {u : Space d} {q : ℝ} (hq : (u,q) ∈ interior C) {t : ℝ}
    (ht : t ∈ interior (fiber C u)) : (u,t) ∈ interior C := by
  obtain ⟨a,b,hab,eq⟩ := interval_fiber hc hv
    (show (fiber C u).Nonempty from ⟨q,show (u,q) ∈ C from interior_subset hq⟩)
  rw [eq, interior_Icc] at ht
  have transport {r : ℝ} (hr : r ∈ Icc a b) (hs : t ∈ openSegment ℝ q r) :
      (u,t) ∈ interior C := by
    obtain ⟨k,l,hk,hl,hkl,hkt⟩ := hs
    have hr' : r ∈ fiber C u := eq ▸ hr
    have h := hv.combo_interior_self_mem_interior hq (show (u,r) ∈ C from hr') hk hl.le hkl
    change (k • u + l • u,k • q + l • r) ∈ interior C at h
    rwa [← add_smul, hkl, one_smul, hkt] at h
  rcases lt_trichotomy t q with h | rfl | h
  · exact transport (left_mem_Icc.mpr hab) (openSegment_symm ℝ a q ▸ Ioo_subset_openSegment ⟨ht.1,h⟩)
  · exact hq
  · exact transport (right_mem_Icc.mpr hab) (Ioo_subset_openSegment ⟨h,ht.2⟩)

private theorem measureReal_union_of_null_frontiers {n : ℕ} {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (ρ : Measure X) (A : Fin n → Set X) (ms : ∀ i, MeasurableSet (A i))
    (finite : ∀ i, ρ (A i) ≠ ∞) (null : ∀ i, ρ (frontier (A i)) = 0)
    (disj : Pairwise fun i j => Disjoint (interior (A i)) (interior (A j))) :
    ρ.real (⋃ i, A i) = ∑ i, ρ.real (A i) := by
  have hd : Pairwise (fun i j => AEDisjoint ρ (A i) (A j)) := by
    intro i j hij
    apply measure_mono_null _ (measure_union_null (null i) (null j))
    intro x hx
    by_cases hi : x ∈ interior (A i)
    · exact Or.inr ⟨subset_closure hx.2, fun hj => Set.disjoint_left.mp (disj hij) hi hj⟩
    · exact Or.inl ⟨subset_closure hx.1, hi⟩
  simp only [measureReal_def, measure_iUnion₀ hd (fun i => (ms i).nullMeasurableSet),
    tsum_fintype, ENNReal.toReal_sum (fun i _ => finite i)]

/-- In a partition of a cylinder, simultaneous centering of the horizontal
moments forces every vertical fibre length to be almost everywhere constant.
No regularity or consistency of the ordering of the pieces is assumed. -/
theorem partition_fiber_lengths {n : ℕ} (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) {D : Set (Space d)} (hD : ν D = 1) {lo hi : ℝ}
    (C : Fin n → Set (Space d × ℝ)) (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hcover : (⋃ i, C i) = D ×ˢ Icc lo hi)
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (hm : ∀ i, 0 < (ν.prod volume).real (C i))
    (centered : ∀ i, ∫ p in C i, p.1 ∂(ν.prod volume) = (0 : Space d)) :
    ∀ i, length (C i) 0 = (ν.prod volume).real (C i) ∧
      ∀ᵐ u ∂ν, length (C i) u = (ν.prod volume).real (C i) := by
  let ρ := ν.prod (volume : Measure ℝ)
  have hρ : ρ ≪ (volume : Measure (Space d)).prod (volume : Measure ℝ) :=
    hν.prod Measure.AbsolutelyContinuous.rfl
  have bound i := integral_sq_le_central ν (hc i) (hv i) (hm i) (centered i)
  have lower i := mean_sq_le_integral_sq ν (hc i)
  have ge (i : Fin n) : ρ.real (C i) ≤ length (C i) 0 := by
    have hq := (lower i).trans (bound i)
    rw [sq] at hq
    exact le_of_mul_le_mul_left hq (hm i)
  have total : ∑ i, ρ.real (C i) = volume.real (Icc lo hi) := by
    rw [← measureReal_union_of_null_frontiers ρ C (fun i => (hc i).isClosed.measurableSet)
      (fun i => (hc i).measure_lt_top.ne) (fun i => hρ ((hv i).addHaar_frontier _)) disj, hcover,
      measureReal_prod_prod, show ν.real D = 1 by simp [measureReal_def,hD], one_mul]
  let F (i : Fin n) := fiber (C i) 0
  choose z hz using fun i => exists_axis_interior ν hν (hc i) (hv i) (hm i) (centered i)
  have Fdisj : Pairwise fun i j => Disjoint (interior (F i)) (interior (F j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun t hi hj => Set.disjoint_left.mp (disj hij)
      (fiber_int_into_int (hc i) (hv i) (hz i) hi) (fiber_int_into_int (hc j) (hv j) (hz j) hj)
  have Fnull (i : Fin n) : volume (frontier (F i)) = 0 := by
    obtain ⟨a,b,_,h⟩ := interval_fiber (hc i) (hv i)
      (show (F i).Nonempty from ⟨z i,show (0,z i) ∈ C i from interior_subset (hz i)⟩)
    change volume (frontier (fiber (C i) 0)) = 0
    rw [h]
    exact (convex_Icc a b).addHaar_frontier _
  have sub : (⋃ i, F i) ⊆ Icc lo hi := by
    intro t ht
    obtain ⟨i,hit⟩ := mem_iUnion.mp ht
    have h : ((0,t) : Space d × ℝ) ∈ ⋃ i, C i := mem_iUnion.mpr ⟨i,hit⟩
    exact (hcover ▸ h : ((0,t) : Space d × ℝ) ∈ D ×ˢ Icc lo hi).2
  have sum_le : ∑ i, length (C i) 0 ≤ ∑ i, ρ.real (C i) := by
    rw [total]
    change ∑ i, volume.real (F i) ≤ _
    rw [← measureReal_union_of_null_frontiers volume F
      (fun i => (compact_fiber (hc i) 0).isClosed.measurableSet)
      (fun i => (compact_fiber (hc i) 0).measure_lt_top.ne) Fnull Fdisj]
    exact measureReal_mono sub isCompact_Icc.measure_lt_top.ne
  have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => ge i)).mp
    (le_antisymm (Finset.sum_le_sum fun i _ => ge i) sum_le)
  intro i
  have hi := (heq i (Finset.mem_univ i)).symm
  refine ⟨hi, ae_const_of_sq_eq ν (hc i) (le_antisymm ?_ (lower i))⟩
  simpa [hi, sq, ρ] using bound i

private theorem vertically_ordered {A B : Set (Space d × ℝ)} (ca : IsCompact A) (cb : IsCompact B)
    (va : Convex ℝ A) (vb : Convex ℝ B) (disj : Disjoint (interior A) (interior B))
    {a b : ℝ} (ha : (0,a) ∈ interior A) (hb : (0,b) ∈ interior B) (hab : a < b)
    {u : Space d} {s t : ℝ} (hs : (u,s) ∈ A) (ht : (u,t) ∈ B) : s ≤ t := by
  obtain ⟨F,c,hA,hB⟩ := geometric_hahn_banach_open va.interior isOpen_interior vb.interior disj
  let k := F (0,1)
  have eval (x : Space d) (z : ℝ) : F (x,z) = F (x,0) + z*k := by
    have h : (x,z) = (x,0) + z • ((0,1) : Space d × ℝ) := by ext <;> simp
    rw [h, map_add, map_smul]
    rfl
  have hlt := (hA _ ha).trans_le (hB _ hb)
  rw [eval 0 a, eval 0 b] at hlt
  have hk : 0 < k := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab.le) h]
  have hs' : (u,s) ∈ closure (interior A) := by
    rwa [va.closure_interior_eq_closure_of_nonempty_interior ⟨_,ha⟩, ca.isClosed.closure_eq]
  have ht' : (u,t) ∈ closure (interior B) := by
    rwa [vb.closure_interior_eq_closure_of_nonempty_interior ⟨_,hb⟩, cb.isClosed.closure_eq]
  have h1 : F (u,s) ≤ c := closure_minimal (fun x hx => (hA x hx).le)
    (isClosed_le F.continuous continuous_const) hs'
  have h2 : c ≤ F (u,t) := closure_minimal hB (isClosed_le continuous_const F.continuous) ht'
  have h := h1.trans h2
  rw [eval u s, eval u t, add_le_add_iff_left, mul_le_mul_iff_left₀ hk] at h
  exact h

/-- In a tiling of a line segment by positive intervals, the position of a
piece is determined by its length and the lengths of all preceding pieces. -/
private theorem interval_start {n : ℕ} (z : Fin n → ℝ) (hz : Function.Injective z)
    (a b : Fin n → ℝ) (hab : ∀ i, a i ≤ b i) {lo hi : ℝ}
    (cover : (⋃ i, Icc (a i) (b i)) = Icc lo hi)
    (order : ∀ i j, z i < z j → b i ≤ a j) (i : Fin n) :
    a i - lo = ∑ j, (if z j < z i then b j - a j else 0) := by
  let F j := Icc (a j) (b j)
  let below : Measure ℝ := volume.restrict (Iic (a i))
  have mem : a i ∈ Icc lo hi := cover ▸ mem_iUnion.mpr ⟨i,left_mem_Icc.mpr (hab i)⟩
  have disj : Pairwise fun j k => Disjoint (interior (F j)) (interior (F k)) := by
    intro j k hne
    simp only [F, interior_Icc]
    apply Set.disjoint_left.mpr
    intro x hj hk
    rcases lt_or_gt_of_ne (hz.ne hne) with h | h
    · exact (not_lt_of_ge (order _ _ h)) (hk.1.trans hj.2)
    · exact (not_lt_of_ge (order _ _ h)) (hj.1.trans hk.2)
  have he := measureReal_union_of_null_frontiers below F (fun _ => measurableSet_Icc)
    (fun j => (isCompact_Icc.measure_lt_top (μ := below)).ne)
    (fun j => Measure.absolutelyContinuous_restrict ((convex_Icc (a j) (b j)).addHaar_frontier volume))
    disj
  have cut (s t : ℝ) : Icc s t ∩ Iic (a i) = Icc s (min t (a i)) := by
    ext x
    simp [and_assoc]
  change (volume.restrict (Iic (a i))).real (⋃ j, Icc (a j) (b j)) = _ at he
  rw [cover, measureReal_restrict_apply measurableSet_Icc, cut, min_eq_right mem.2,
    Real.volume_real_Icc_of_le mem.1] at he
  refine he.trans (Finset.sum_congr rfl (fun j _ => ?_))
  change (volume.restrict (Iic (a i))).real (Icc (a j) (b j)) = _
  rw [measureReal_restrict_apply measurableSet_Icc, cut, Real.volume_real_Icc]
  by_cases h : z j < z i
  · simp [h,min_eq_left (order _ _ h),max_eq_left (sub_nonneg.mpr (hab j))]
  · rw [if_neg h, max_eq_right_iff, sub_nonpos]
    rcases lt_or_eq_of_le (le_of_not_gt h) with h' | h'
    · exact (min_le_right _ _).trans ((hab i).trans (order _ _ h'))
    · rw [hz h']
      exact min_le_right _ _

private theorem dense_in_body {ν : Measure (Space d)} [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) {D G : Set (Space d)} (hclosed : IsClosed D)
    (hconv : Convex ℝ D) (full : ν D = 1) (hdom : volume.restrict D ≪ ν)
    (hg : ∀ᵐ u ∂ν, u ∈ G) : D ⊆ closure G := by
  have hint : (interior D).Nonempty := by
    by_contra! he
    have h := hν (hconv.addHaar_frontier volume)
    simp [frontier,he,full] at h
  let U := interior D \ closure G
  have hop : IsOpen U := isOpen_interior.sdiff isClosed_closure
  have hu : ν U = 0 := measure_mono_null
    (fun x hx => show x ∉ G from fun hxG => hx.2 (subset_closure hxG)) (ae_iff.mp hg)
  have h := hdom hu
  rw [Measure.restrict_apply hop.measurableSet,
    inter_eq_self_of_subset_left (show U ⊆ D from diff_subset.trans interior_subset)] at h
  have hsub : interior D ⊆ closure G := diff_eq_empty.mp ((hop.measure_eq_zero_iff volume).mp h)
  rw [← hclosed.closure_eq, ← hconv.closure_interior_eq_closure_of_nonempty_interior hint]
  exact closure_minimal hsub isClosed_closure

/-- A finite convex partition of a straight cylinder with all horizontal
moments zero consists exactly of horizontal slabs. The measure on the
base may be any probability equivalent there to ordinary volume. -/
theorem partition_is_slabs {n : ℕ} (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) {D : Set (Space d)} (hclosed : IsClosed D) (hconv : Convex ℝ D)
    (hdom : volume.restrict D ≪ ν) (hD : ν D = 1) {lo hi : ℝ}
    (C : Fin n → Set (Space d × ℝ)) (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hcover : (⋃ i, C i) = D ×ˢ Icc lo hi)
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (hm : ∀ i, 0 < (ν.prod volume).real (C i))
    (centered : ∀ i, ∫ p in C i, p.1 ∂(ν.prod volume) = (0 : Space d)) :
    ∀ i, ∃ a b : ℝ, a < b ∧ C i = D ×ˢ Icc a b := by
  let m i := (ν.prod volume).real (C i)
  have lens := partition_fiber_lengths ν hν hD C hc hv hcover disj hm centered
  choose z hz using fun i => exists_axis_interior ν hν (hc i) (hv i) (hm i) (centered i)
  have hzInj : Function.Injective z := by
    intro i j he
    by_contra hij
    exact Set.disjoint_left.mp (disj hij) (hz i) (he ▸ hz j)
  let G := {u | u ∈ D ∧ ∀ j, length (C j) u = m j}
  have hg : ∀ᵐ u ∂ν, u ∈ G := by
    have ha : ∀ᵐ u ∂ν, u ∈ D := (mem_ae_iff_prob_eq_one hclosed.measurableSet).mpr hD
    exact ha.and (Filter.eventually_all.mpr fun j => (lens j).2)
  have dense := dense_in_body hν hclosed hconv hD hdom hg
  have sub (i) : C i ⊆ D ×ˢ Icc lo hi :=
    hcover ▸ subset_iUnion C i
  intro i
  let start := lo + ∑ j, if z j < z i then m j else 0
  let J := Icc start (start + m i)
  have eqf (u : Space d) (hu : u ∈ G) : fiber (C i) u = J := by
    have ne (j) : (fiber (C j) u).Nonempty := by
      by_contra! h
      have : length (C j) u = 0 := by simp [length,h]
      linarith [show 0 < m j from hm j, hu.2 j]
    choose a b hab hcell using fun j => interval_fiber (hc j) (hv j) (ne j)
    have hlen j : b j - a j = m j := by
      simpa [length,hcell,Real.volume_real_Icc_of_le (hab j)] using hu.2 j
    have all : (⋃ j, Icc (a j) (b j)) = Icc lo hi := by
      ext t
      simp only [mem_iUnion, ← hcell]
      constructor
      · rintro ⟨j,hj⟩
        exact (sub j hj).2
      · intro ht
        have ht' : (u,t) ∈ D ×ˢ Icc lo hi := ⟨hu.1,ht⟩
        rw [← hcover] at ht'
        obtain ⟨j,hj⟩ := mem_iUnion.mp ht'
        exact ⟨j,hj⟩
    have ord j k (h : z j < z k) : b j ≤ a k := by
      have hb : b j ∈ fiber (C j) u := hcell j ▸ right_mem_Icc.mpr (hab j)
      have ha : a k ∈ fiber (C k) u := hcell k ▸ left_mem_Icc.mpr (hab k)
      exact vertically_ordered (hc j) (hc k) (hv j) (hv k) (disj (fun he => h.ne (congrArg z he)))
        (hz j) (hz k) h hb ha
    have head := interval_start z hzInj a b hab all ord i
    simp_rw [hlen] at head
    have hstart : a i = start := by dsimp [start]; linarith
    have hend : b i = start + m i := by linarith [hlen i]
    rw [hcell,hstart,hend]
  refine ⟨start, start + m i, lt_add_of_pos_right _ (hm i), Subset.antisymm ?_ ?_⟩
  · have incl : interior (C i) ⊆ D ×ˢ J := by
      rintro ⟨u,t⟩ hp
      have hu := (sub i (interior_subset hp)).1
      refine ⟨hu, ?_⟩
      have hop : IsOpen ((fun v : Space d => (v,t)) ⁻¹' interior (C i)) :=
        isOpen_interior.preimage (by fun_prop)
      obtain ⟨v,hvOpen,hvG⟩ := mem_closure_iff.mp (dense hu) _ hop hp
      exact eqf v hvG ▸ (show t ∈ fiber (C i) v from show (v,t) ∈ C i from interior_subset hvOpen)
    rw [← (hc i).isClosed.closure_eq, ← (hv i).closure_interior_eq_closure_of_nonempty_interior ⟨_,hz i⟩]
    exact closure_minimal incl (hclosed.prod isClosed_Icc)
  · rintro ⟨u,t⟩ ⟨hu,ht⟩
    have pre : IsClosed ((fun v : Space d => (v,t)) ⁻¹' C i) :=
      (hc i).isClosed.preimage (by fun_prop)
    exact closure_minimal (fun v hvG => show t ∈ fiber (C i) v from eqf v hvG ▸ ht) pre (dense hu)

end NRR.Cylinder
