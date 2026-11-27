import NRR.ConvexLimits
import NRR.CubeSlabQuadrature
import NRR.CubeSlabFubini
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The four volume integrals used in the cube construction, on the full
Hausdorff space of nonempty compact convex sets. -/

noncomputable section
open Set Filter Topology Metric MeasureTheory

namespace NRR.ConvexLimits

/-- A locally integrable density suffices for continuity of a compact-convex
set integral. All bodies in a Hausdorff neighborhood fit in one fixed ball. -/
theorem continuous_integral_of_locallyIntegrable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (μ : Measure E) (hμ : μ ≪ ν) {f : E → F} (hf : LocallyIntegrable f μ) :
    Continuous (fun C : ConvexCompact E => ∫ x in points C, f x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro C
  obtain ⟨r, bound⟩ := C.val.isCompact.isBounded.subset_closedBall (0 : E)
  let B := closedBall (0 : E) (r+1)
  have localInt : Integrable f (μ.restrict B) :=
    hf.integrableOn_isCompact (isCompact_closedBall _ _)
  apply (continuous_integral ν (μ.restrict B)
    (Measure.absolutelyContinuous_restrict.trans hμ) localInt).continuousAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds C (by norm_num : (0 : ℝ) < 1)] with D hD
  have sub : points D ⊆ B := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx
      (show dist D.val C.val < 1 from hD) (edist_ne_top D.val C.val)
    exact (dist_triangle x y 0).trans (by linarith [show dist y 0 ≤ r from bound hy])
  rw [Measure.restrict_restrict_of_subset sub]

end NRR.ConvexLimits

namespace NRR.CubeFourMomentReadout

/-- Slopes of size at most `δ < 1/12` keep the two affine graphs strictly
ordered throughout the horizontal square. -/
theorem slabHeight_lt_of_small {m δ : ℝ} (top : ℝ) (lo hi : Plane)
    (hm : 0 < m) (hδ : δ < 1/12)
    (hl₁ : |lo.1| ≤ δ) (hl₂ : |lo.2| ≤ δ) (hu₁ : |hi.1| ≤ δ) (hu₂ : |hi.2| ≤ δ)
    (x y : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    slabHeight m (top-m) lo x y < slabHeight m top hi x y := by
  have bound (p : Plane) (h₁ : |p.1| ≤ δ) (h₂ : |p.2| ≤ δ) :
      |3*m*(p.1*x + p.2*y)| ≤ 6*m*δ := by
    have coord (a t : ℝ) (ha : |a| ≤ δ) (ht : t ∈ Icc (-1 : ℝ) 1) : |a*t| ≤ δ := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg a) (abs_le.mpr ht)).trans ha
    rw [abs_mul, abs_of_pos (by positivity : 0 < 3*m)]
    calc
      _ ≤ (3*m)*(δ+δ) := mul_le_mul_of_nonneg_left
        ((abs_add_le _ _).trans (add_le_add (coord _ x h₁ hx) (coord _ y h₂ hy))) (by positivity)
      _ = _ := by ring
  have hgap : 6*m*δ < m/2 := by nlinarith [mul_pos hm (sub_pos.mpr hδ)]
  unfold slabHeight
  linarith [(abs_le.mp (bound lo hl₁ hl₂)).2, (abs_le.mp (bound hi hu₁ hu₂)).1]

/-- A common positive bound on the two slopes for the layer window and
the interface readout at any given height. -/
theorem exists_readout_radius (m top : ℝ) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/12 ∧ m*δ + 2 * |top| * δ + 24*m*δ^2 ≤ m/8 := by
  let L := 25*m + 2 * |top|
  have hL : 0 < L := by dsimp [L]; positivity
  let δ := min (1/24 : ℝ) ((m/8)/L)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (by positivity) hL)
  have h₁ : δ ≤ 1/24 := min_le_left _ _
  have h₂ : δ*L ≤ m/8 := (le_div_iff₀ hL).mp (min_le_right _ _)
  have hsq : δ^2 ≤ δ := by nlinarith [mul_nonneg hδ.le (show 0 ≤ 1-δ by linarith)]
  refine ⟨δ, hδ, by linarith, ?_⟩
  dsimp [L] at h₂
  nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hsq)]

/-- Both coordinate functions on the centered horizontal square have mean zero. -/
private theorem integral_affine_square (c a b : ℝ) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (c+a*x) + b*y) = 4*c := by
  have linear (a b : ℝ) : (∫ t in (-1 : ℝ)..1, a + b*t) = 2*a := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const) (by
      apply Continuous.intervalIntegrable
      fun_prop), intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  simp_rw [linear]
  rw [intervalIntegral.integral_const_mul, linear]
  ring

/-- The centered square kills the two linear tilt terms in the volume. -/
theorem slabIntegral_one (m top : ℝ) (lo hi : Plane) :
    slabIntegral m top lo hi (fun _ _ _ => 1) = 4*m := by
  have width (x y : ℝ) : slabHeight m top hi x y - slabHeight m (top-m) lo x y =
      (m + 3*m*(hi.1-lo.1)*x) + (3*m*(hi.2-lo.2))*y := by unfold slabHeight; ring
  unfold slabIntegral
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  simp_rw [width, integral_affine_square]

/-- With layer thickness `m = 2/n`, this normalization is the cube's `n/8`. -/
def volumeFourMoments (m : ℝ) (S : Set (Plane × ℝ)) : Plane × Plane :=
  let avg (f : Plane × ℝ → ℝ) := (1 / (4*m)) * ∫ v in S, f v
  ((avg (fun v => v.1.1), avg (fun v => v.1.2)),
    (avg (fun v => (1+v.1.1)*v.2), avg (fun v => v.1.2*v.2)))

theorem continuous_volumeFourMoments (m : ℝ) :
    Continuous (fun C : ConvexLimits.ConvexCompact (Plane × ℝ) =>
      volumeFourMoments m (ConvexLimits.points C)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Plane × ℝ)) := by
    rw [Measure.volume_eq_prod Plane ℝ, Measure.volume_eq_prod ℝ ℝ]
    infer_instance
  have moment (f : Plane × ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun C : ConvexLimits.ConvexCompact (Plane × ℝ) =>
        (1 / (4*m)) * ∫ v in ConvexLimits.points C, f v) := by
    apply Continuous.mul continuous_const
    exact ConvexLimits.continuous_integral_of_locallyIntegrable
      (E := Plane × ℝ) (f := f) volume volume Measure.AbsolutelyContinuous.rfl hf.locallyIntegrable
  exact ((moment (fun v => v.1.1) (by fun_prop)).prodMk
    (moment (fun v => v.1.2) (by fun_prop))).prodMk
    ((moment (fun v => (1+v.1.1)*v.2) (by fun_prop)).prodMk
      (moment (fun v => v.1.2*v.2) (by fun_prop)))

def affineSlab (m top : ℝ) (lo hi : Plane) : Set (Plane × ℝ) :=
  graphSlab (fun p => slabHeight m (top-m) lo p.1 p.2) (fun p => slabHeight m top hi p.1 p.2)

/-- The two intercepts are free. Equal volume therefore fixes their difference,
even before identifying the heights of the individual cuts. -/
theorem volume_between_affine_graphs (m s t : ℝ) (lo hi : Plane)
    (ordered : ∀ p ∈ squareBase, slabHeight m s lo p.1 p.2 ≤ slabHeight m t hi p.1 p.2) :
    volume.real (graphSlab (fun p => slabHeight m s lo p.1 p.2)
      (fun p => slabHeight m t hi p.1 p.2)) = 4*(t-s) := by
  have I := integral_graphSlab (fun p => slabHeight m s lo p.1 p.2)
    (fun p => slabHeight m t hi p.1 p.2) (fun _ => (1 : ℝ))
    (by unfold slabHeight; fun_prop) (by unfold slabHeight; fun_prop) ordered continuous_const
  have width (x y : ℝ) : slabHeight m t hi x y - slabHeight m s lo x y =
      ((t-s) + (3*m*(hi.1-lo.1))*x) + (3*m*(hi.2-lo.2))*y := by unfold slabHeight; ring
  simpa only [setIntegral_one_eq_measureReal, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, width, integral_affine_square] using I

/-- The margin to the cube faces is allowed to vanish for a horizontal
exterior interface. -/
theorem cube_inter_affineSlab (m top : ℝ) (lo hi : Plane) (hm : 0 ≤ m)
    (bottom : -1 + 3*m*(|lo.1| + |lo.2|) ≤ top-m)
    (upper : top + 3*m*(|hi.1| + |hi.2|) ≤ 1) :
    (squareBase ×ˢ Icc (-1 : ℝ) 1) ∩ affineSlab m top lo hi = affineSlab m top lo hi := by
  apply inter_eq_right.mpr
  rintro ⟨⟨x,y⟩,z⟩ ⟨hx,hy,hz⟩
  have band (p : Plane) : |3*m*(p.1*x+p.2*y)| ≤ 3*m*(|p.1| + |p.2|) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3*m)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr hx))
      (mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr hy))
  refine ⟨⟨hx,hy⟩, ?_, ?_⟩
  · have hz' : top - m + 3*m*(lo.1*x+lo.2*y) ≤ z := hz.1
    linarith [(abs_le.mp (band lo)).1]
  · have hz' : z ≤ top + 3*m*(hi.1*x+hi.2*y) := hz.2
    linarith [(abs_le.mp (band hi)).2]

/-- Ordinary volume integration over the closed layer agrees with vertical
quadrature whenever the two interfaces are ordered on the full base. -/
theorem setIntegral_affineSlab (m top : ℝ) (lo hi : Plane)
    (ordered : ∀ p ∈ squareBase, slabHeight m (top-m) lo p.1 p.2 ≤ slabHeight m top hi p.1 p.2)
    (g : Plane × ℝ → ℝ) (hg : Continuous g) :
    (∫ v in affineSlab m top lo hi, g v) = slabIntegral m top lo hi (fun x y z => g ((x,y),z)) :=
  integral_graphSlab _ _ g (by unfold slabHeight; fun_prop)
    (by unfold slabHeight; fun_prop) ordered hg

theorem volume_affineSlab (m top : ℝ) (lo hi : Plane)
    (ordered : ∀ p ∈ squareBase, slabHeight m (top-m) lo p.1 p.2 ≤ slabHeight m top hi p.1 p.2) :
    volume.real (affineSlab m top lo hi) = 4*m := by
  simpa only [setIntegral_one_eq_measureReal, slabIntegral_one] using
    setIntegral_affineSlab m top lo hi ordered (fun _ => 1) continuous_const

/-- Section 4's four-moment identity for actual Lebesgue integrals over
a layer between two affine graphs above the square. -/
theorem volumeFourMoments_affineSlab (m top : ℝ) (lo hi : Plane) (hm : 0 < m)
    (ordered : ∀ p ∈ squareBase, slabHeight m (top-m) lo p.1 p.2 ≤ slabHeight m top hi p.1 p.2) :
    volumeFourMoments m (affineSlab m top lo hi) = cubeFourMoments m top lo hi := by
  dsimp only [volumeFourMoments]
  rw [setIntegral_affineSlab m top lo hi ordered (fun v => v.1.1) (by fun_prop),
    setIntegral_affineSlab m top lo hi ordered (fun v => v.1.2) (by fun_prop),
    setIntegral_affineSlab m top lo hi ordered (fun v => (1+v.1.1)*v.2) (by fun_prop),
    setIntegral_affineSlab m top lo hi ordered (fun v => v.1.2*v.2) (by fun_prop)]
  exact slabIntegral_fourMoments m top lo hi hm

/-- One positive slope radius works for every ordered layer at this height.
The selector reads its layer center, and the four volume integrals recover
both interfaces. -/
theorem exists_radius_volumeFourMoment_readout (m top : ℝ) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lo hi : Plane,
      |lo.1| ≤ δ → |lo.2| ≤ δ → |hi.1| ≤ δ → |hi.2| ≤ δ →
      let M := volumeFourMoments m (affineSlab m top lo hi)
      volume.real (affineSlab m top lo hi) = 4*m ∧
        layerWindow m (top-m/2) M.2.1 = 1 ∧
        lowerReadout m top M = lo ∧ lowerReadout m top M + M.1 = hi := by
  obtain ⟨δ, hδ, hsmall, hindex⟩ := exists_readout_radius m top hm
  refine ⟨δ, hδ, ?_⟩
  intro lo hi hl₁ hl₂ hu₁ hu₂
  have ordered (p : Plane) (hp : p ∈ squareBase) :=
    (slabHeight_lt_of_small top lo hi hm hsmall hl₁ hl₂ hu₁ hu₂ p.1 p.2 hp.1 hp.2).le
  have hslope : -(1/6 : ℝ) < hi.1 - lo.1 := by
    linarith [(abs_le.mp hl₁).2, (abs_le.mp hu₁).1]
  dsimp only
  rw [volumeFourMoments_affineSlab m top lo hi hm ordered]
  exact ⟨volume_affineSlab m top lo hi ordered,
    layerWindow_eq_one m (top-m/2) _ hm
      ((model_V1_center_bound m top δ lo hi hm hδ.le hl₁ hl₂ hu₁ hu₂).trans hindex),
    lowerReadout_model m top lo hi hm hslope, upperReadout_model m top lo hi hm hslope⟩

end NRR.CubeFourMomentReadout
