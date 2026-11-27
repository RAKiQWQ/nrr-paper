import NRR.ConvexLimits
import NRR.Localization
import NRR.CylinderExtension

/-! The horizontal separating functional used to exclude disappearing
cylinder intersections in the localization argument. -/

noncomputable section
open Set Topology Filter Metric MeasureTheory

namespace NRR.Localization

variable {d : ℕ}

def solidCylinder (a h : ℝ) : Set (Space d × ℝ) :=
  closedBall 0 a ×ˢ Icc (-h) h

theorem interior_solidCylinder {a h : ℝ} (ha : 0 < a) :
    interior (solidCylinder (d := d) a h) = ball 0 a ×ˢ Ioo (-h) h := by
  rw [solidCylinder, interior_prod_eq, interior_closedBall _ ha.ne', interior_Icc]

/-- If a convex set avoids the cylinder interior but contains a point at
strictly intermediate height, a nonzero horizontal functional is positive
at that point and on every contact with the closed cylinder. -/
theorem horizontal_separator_of_avoids_cylinder {C : Set (Space d × ℝ)}
    (hC : Convex ℝ C) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (avoids : Disjoint (interior (solidCylinder (d := d) a h)) C)
    {y : Space d × ℝ} (hy : y ∈ C) (height : |y.2| < h) :
    ∃ L : Space d →L[ℝ] ℝ, L ≠ 0 ∧ 0 < L y.1 ∧
      ∀ q ∈ C ∩ solidCylinder a h, 0 < L q.1 := by
  have cv : Convex ℝ (solidCylinder (d := d) a h) :=
    (convex_closedBall (0 : Space d) a).prod (convex_Icc (-h) h)
  have interior_ne : (interior (solidCylinder (d := d) a h)).Nonempty := by
    rw [interior_solidCylinder ha]
    exact ⟨(0,0), by simp [ha, hh]⟩
  obtain ⟨F,c,hA,hS⟩ := geometric_hahn_banach_open cv.interior isOpen_interior hC avoids
  let L : Space d →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ (Space d) ℝ)
  let b : ℝ := F (0,1)
  have eval (u : Space d) (z : ℝ) : F (u,z) = L u + z*b := by
    have he : (u,z) = (u,0) + z • ((0,1) : Space d × ℝ) := by ext <;> simp
    rw [he, map_add, map_smul]
    rfl
  have hn : L ≠ 0 := by
    intro hz
    have hp : (0,y.2) ∈ interior (solidCylinder (d := d) a h) := by
      rw [interior_solidCylinder ha]
      exact ⟨mem_ball_self ha, abs_lt.mp height⟩
    have ht := (hA _ hp).trans_le (hS y hy)
    rw [eval, eval] at ht
    simp [hz] at ht
  have A_le (q : Space d × ℝ) (hq : q ∈ solidCylinder a h) : F q ≤ c := by
    apply closure_minimal (fun x hx => (hA x hx).le)
      (isClosed_le F.continuous continuous_const)
    have cl : IsClosed (solidCylinder (d := d) a h) := isClosed_closedBall.prod isClosed_Icc
    rwa [cv.closure_interior_eq_closure_of_nonempty_interior interior_ne, cl.closure_eq]
  obtain ⟨u,hu,huval⟩ := ConvexLimits.exists_support_unitBall L
  let z : ℝ := if 0 ≤ b then h else -h
  have hzmem : z ∈ Icc (-h) h := by
    dsimp [z]
    split_ifs <;> constructor <;> linarith
  have hzb : z*b = h*|b| := by
    dsimp [z]
    split_ifs with hb
    · rw [abs_of_nonneg hb]
    · rw [abs_of_neg (lt_of_not_ge hb)]
      ring
  have supA : a*‖L‖ + h*|b| ≤ c := by
    have H := A_le (a • u,z) ⟨by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      exact mul_le_of_le_one_right ha.le hu, hzmem⟩
    rw [eval, map_smul, smul_eq_mul, huval, hzb] at H
    exact H
  have sep (q : Space d × ℝ) (hq : q ∈ C) : a*‖L‖ + h*|b| ≤ L q.1 + b*q.2 := by
    have H := supA.trans (hS q hq)
    simpa only [eval, mul_comm q.2] using H
  refine ⟨L, hn, positive_centroid_of_separation ha (norm_pos_iff.mpr hn) height (sep y hy), ?_⟩
  intro q hq
  have ht : b*q.2 ≤ h*|b| := calc
    b*q.2 ≤ |b*q.2| := le_abs_self _
    _ = |b| * |q.2| := abs_mul _ _
    _ ≤ |b| * h := mul_le_mul_of_nonneg_left (abs_le.mpr hq.2.2) (abs_nonneg _)
    _ = h*|b| := mul_comm _ _
  have hs := sep q hq.1
  have hp := mul_pos ha (norm_pos_iff.mpr hn)
  linarith

/-- A nondegenerate convex body meeting an open set meets it in its
interior too. This turns a degenerate clip into genuine separation. -/
theorem disjoint_open_of_empty_interior_inter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C U : Set E} (hC : Convex ℝ C) (hc : IsClosed C)
    (hfull : (interior C).Nonempty) (hu : IsOpen U)
    (empty : interior (C ∩ U) = ∅) : Disjoint U C := by
  apply Set.disjoint_left.mpr
  intro x hxU hxC
  have hclosure : x ∈ closure (interior C) := by
    rwa [hC.closure_interior_eq_closure_of_nonempty_interior hfull, hc.closure_eq]
  obtain ⟨y, hyU, hyC⟩ := mem_closure_iff.mp hclosure U hu hxU
  have hy : y ∈ interior (C ∩ U) := by
    rw [interior_inter, hu.interior_eq]
    exact ⟨hyC,hyU⟩
  simp [empty] at hy

/-- A Hausdorff limit of zeros of a positive weighted horizontal moment
cannot lose the interior of its cylinder clip. No lower bound on the
positive tail weights, or prescribed rate of convergence, is needed. -/
theorem interior_clip_of_zero_moments
    (ρ : Measure (Space d × ℝ)) [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    (hfirst : Integrable (fun q : Space d × ℝ => q.1) ρ)
    {C : ConvexLimits.ConvexCompact (Space d × ℝ)}
    {Ck : ℕ → ConvexLimits.ConvexCompact (Space d × ℝ)}
    (near : Tendsto Ck atTop (𝓝 C)) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (mass : 0 < ρ (ConvexLimits.points C))
    (height : |⨍ q in ConvexLimits.points C, q.2 ∂ρ| < h)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k)
    (zero : ∀ k (L : Space d →L[ℝ] ℝ),
      (∫ q in ConvexLimits.points (Ck k) ∩ solidCylinder a h, L q.1 ∂volume) +
        δ k * (∫ q in ConvexLimits.points (Ck k), L q.1 ∂ρ) = 0) :
    (interior (ConvexLimits.points C ∩ solidCylinder a h)).Nonempty := by
  let S := ConvexLimits.points C
  have compact : IsCompact S := C.val.isCompact
  have convex : Convex ℝ S := C.property
  have full : (interior S).Nonempty := by
    by_contra! he
    have hf := hρ (convex.addHaar_frontier
      ((volume : Measure (Space d)).prod (volume : Measure ℝ)))
    rw [frontier, compact.isClosed.closure_eq, he, diff_empty] at hf
    exact mass.ne' hf
  by_contra! hempty
  have avoids : Disjoint (interior (solidCylinder (d := d) a h)) S := by
    apply disjoint_open_of_empty_interior_inter convex compact.isClosed full isOpen_interior
    have hi : interior (S ∩ interior (solidCylinder (d := d) a h)) ⊆
        interior (S ∩ solidCylinder a h) :=
      interior_mono (fun q hq => ⟨hq.1,interior_subset hq.2⟩)
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => by
      have hmem := hi hx
      simp only [S, hempty, mem_empty_iff_false] at hmem
  have hx : IntegrableOn (fun q : Space d × ℝ => q.1) S ρ :=
    continuous_fst.continuousOn.integrableOn_compact compact
  have hz : IntegrableOn (fun q : Space d × ℝ => q.2) S ρ :=
    continuous_snd.continuousOn.integrableOn_compact compact
  let y := (⨍ q in S, q ∂ρ)
  have hy : y ∈ S := convex.set_average_mem compact.isClosed mass.ne' (measure_ne_top _ _)
    (ae_restrict_mem compact.isClosed.measurableSet) (hx.prodMk hz)
  have yheight : y.2 = ⨍ q in S, q.2 ∂ρ := by
    dsimp [y]
    rw [setAverage_eq, setAverage_eq, integral_pair hx hz]
    rfl
  obtain ⟨L, _, hLy, contact⟩ := horizontal_separator_of_avoids_cylinder convex ha hh avoids hy
    (by rwa [yheight])
  have mpos : 0 < ρ.real S := ENNReal.toReal_pos mass.ne' (measure_ne_top _ _)
  have Lavg : L y.1 = (ρ.real S)⁻¹ * (∫ q in S, L q.1 ∂ρ) := by
    dsimp [y]
    rw [setAverage_eq, integral_pair hx hz]
    change L ((ρ.real S)⁻¹ • (∫ q in S, q.1 ∂ρ)) = _
    rw [map_smul, smul_eq_mul, L.integral_comp_comm hx]
  have positive : 0 < ∫ q in S, L q.1 ∂ρ := by
    rw [Lavg] at hLy
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr mpos)).mp hLy
  let l : C(Space d × ℝ, ℝ) := ⟨fun q => L q.1, by fun_prop⟩
  have cont := ConvexLimits.continuous_integral
    ((volume : Measure (Space d)).prod (volume : Measure ℝ))
    ρ hρ (L.integrable_comp hfirst)
  have ht : Tendsto (fun k => ∫ q in ConvexLimits.points (Ck k), L q.1 ∂ρ) atTop
      (𝓝 (∫ q in S, L q.1 ∂ρ)) := cont.continuousAt.tendsto.comp near
  have ev := eventually_positive_weighted_moment (volume : Measure (Space d × ℝ))
    ((continuous_subtype_val.tendsto C).comp near)
    (isClosed_closedBall.prod isClosed_Icc : IsClosed (solidCylinder (d := d) a h)) l
    contact δ (fun k => ∫ q in ConvexLimits.points (Ck k), L q.1 ∂ρ) positive ht hδ
  obtain ⟨k,hk⟩ := ev.exists
  exact (ne_of_gt hk) (zero k L)

theorem isCompact_solidCylinder (a h : ℝ) :
    IsCompact (solidCylinder (d := d) a h) :=
  (isCompact_closedBall (0 : Space d) a).prod isCompact_Icc

/-- The clipped moment remains continuous even when the clipping intersection
degenerates: use the fixed restricted measure, not continuity of intersections. -/
theorem continuous_clipped_moment (a h : ℝ) :
    Continuous (fun C : ConvexLimits.ConvexCompact (Space d × ℝ) =>
      ∫ q in ConvexLimits.points C ∩ solidCylinder a h, q.1 ∂volume) := by
  have cont := ConvexLimits.continuous_integral
    ((volume : Measure (Space d)).prod (volume : Measure ℝ))
    (volume.restrict (solidCylinder (d := d) a h)) Measure.absolutelyContinuous_restrict
    (continuous_fst.continuousOn.integrableOn_compact (isCompact_solidCylinder a h))
  convert cont using 1
  funext C
  rw [Measure.restrict_restrict C.val.isCompact.isClosed.measurableSet]

/-- Vanishing tail weight leaves a zero horizontal moment on each limiting
cylinder clip, as an actual vector integral. -/
theorem clipped_moment_zero_of_limit
    (ρ : Measure (Space d × ℝ)) (hρ : ρ ≪ volume)
    (hfirst : Integrable (fun q : Space d × ℝ => q.1) ρ)
    {C : ConvexLimits.ConvexCompact (Space d × ℝ)}
    {Ck : ℕ → ConvexLimits.ConvexCompact (Space d × ℝ)}
    (near : Tendsto Ck atTop (𝓝 C)) (a h : ℝ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (zero : ∀ k,
      (∫ q in ConvexLimits.points (Ck k) ∩ solidCylinder a h, q.1 ∂volume) +
        δ k • (∫ q in ConvexLimits.points (Ck k), q.1 ∂ρ) = 0) :
    (∫ q in ConvexLimits.points C ∩ solidCylinder a h, q.1 ∂volume) = 0 := by
  have hc := ((continuous_clipped_moment (d := d) a h).tendsto C).comp near
  have ht := ((ConvexLimits.continuous_integral
    ((volume : Measure (Space d)).prod (volume : Measure ℝ)) ρ hρ hfirst).tendsto C).comp near
  have H := hc.add (hδ.smul ht)
  simp only [zero_smul, add_zero] at H
  exact tendsto_nhds_unique H (by simpa only [Function.comp_apply, zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Space d)) atTop (𝓝 0)))

end NRR.Localization
