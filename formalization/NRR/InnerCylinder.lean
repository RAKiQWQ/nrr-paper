import NRR.PartitionMoments
import Mathlib.Topology.MetricSpace.Thickening

/-! Choosing one centered background and a uniformly long inner cylinder
for a prescribed compact family of positive-mass cells. -/

noncomputable section
open Set Filter Topology MeasureTheory Metric

namespace NRR.Localization

variable {d : ℕ}

theorem exists_innerCylinder {K : Set (Space d × ℝ)}
    (axis : ∀ z : ℝ, |z| < 1 → ((0 : Space d),z) ∈ interior K)
    {h : ℝ} (hh : 0 < h) (h1 : h < 1) :
    ∃ a : ℝ, 0 < a ∧ solidCylinder (d := d) a h ⊆ interior K := by
  let T : Set (Space d × ℝ) := {0} ×ˢ Icc (-h) h
  have ct : IsCompact T := isCompact_singleton.prod isCompact_Icc
  have ti : T ⊆ interior K := by
    rintro ⟨u,z⟩ ⟨hu,hz⟩
    have he : u = 0 := hu
    subst u
    exact axis z ((abs_le.mpr hz).trans_lt h1)
  obtain ⟨ε,hε,sub⟩ := ct.exists_thickening_subset_open isOpen_interior ti
  refine ⟨ε/2,by positivity,fun q hq => sub ?_⟩
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(0,q.2),⟨rfl,hq.2⟩,?_⟩
  have hu : ‖q.1‖ ≤ ε/2 := by simpa only [mem_closedBall,dist_zero_right] using hq.1
  rw [Prod.dist_eq,dist_self,max_eq_left dist_nonneg,dist_zero_right]
  linarith

/-- All choices are made from K and the compact family: no positive lower
bound for the prescribed density is assumed. A small added ball centers
the background, and strict interior centroids give one common height. -/
theorem exists_background_innerCylinder {n : ℕ}
    {K : Set (Space d × ℝ)} (compactK : IsCompact K)
    (stripK : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    (axis : ∀ z : ℝ, |z| < 1 → ((0 : Space d),z) ∈ interior K)
    (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    (s : Set (Fin n → ConvexLimits.ConvexCompact (Space d × ℝ)))
    (compact : IsCompact s)
    (subsets : ∀ C ∈ s, ∀ i, ConvexLimits.points (C i) ⊆ K)
    (mass : ∀ C ∈ s, ∀ i, 0 < μ (ConvexLimits.points (C i))) :
    ∃ ρ : Measure (Space d × ℝ), IsFiniteMeasure ρ ∧ ρ ≪ volume ∧
      volume.restrict K ≤ ρ ∧ ρ Kᶜ = 0 ∧ Integrable id ρ ∧ (∫ q, q ∂ρ) = 0 ∧
      ∃ a h : ℝ, 0 < a ∧ 0 < h ∧ h < 1 ∧ solidCylinder a h ⊆ interior K ∧
        ∀ C ∈ s, ∀ i, 0 < ρ (ConvexLimits.points (C i)) ∧
          |⨍ q in ConvexLimits.points (C i), q.2 ∂ρ| < h := by
  let haar := (volume : Measure (Space d)).prod (volume : Measure ℝ)
  obtain ⟨ρ,finite,dom,ac,supp,first,centered⟩ :=
    ConvexLimits.exists_centered_background haar compactK (axis 0 (by norm_num))
  letI := finite
  have positive (C) (hC : C ∈ s) (i : Fin n) : 0 < ρ (ConvexLimits.points (C i)) := by
    have hv : 0 < volume (ConvexLimits.points (C i)) := hμ.pos_mono (mass C hC i)
    have hr : 0 < volume.restrict K (ConvexLimits.points (C i)) := by
      rw [Measure.restrict_apply (C i).val.isCompact.isClosed.measurableSet,
        inter_eq_self_of_subset_left (subsets C hC i)]
      exact hv
    exact (Measure.absolutelyContinuous_of_le dom).pos_mono hr
  let cells : Set (ConvexLimits.ConvexCompact (Space d × ℝ)) :=
    ⋃ i : Fin n, (fun C : Fin n → ConvexLimits.ConvexCompact (Space d × ℝ) => C i) '' s
  have cc : IsCompact cells := isCompact_iUnion fun i => compact.image (continuous_apply i)
  have hp : ∀ C ∈ cells, 0 < ρ (ConvexLimits.points C) := by
    intro C hC
    obtain ⟨i,S,hS,rfl⟩ := mem_iUnion.mp hC
    exact positive S hS i
  have hs : ∀ C ∈ cells, ConvexLimits.points C ⊆ univ ×ˢ Icc (-1 : ℝ) 1 := by
    intro C hC
    obtain ⟨i,S,hS,rfl⟩ := mem_iUnion.mp hC
    exact (subsets S hS i).trans stripK
  obtain ⟨h,hh,h1,height⟩ := ConvexLimits.uniform_centroid_height ρ ac
    ((ContinuousLinearMap.snd ℝ (Space d) ℝ).integrable_comp first) cells cc hp hs
  obtain ⟨a,ha,inner⟩ := exists_innerCylinder axis hh h1
  refine ⟨ρ,finite,ac,dom,supp,first,centered,a,h,ha,hh,h1,inner,?_⟩
  intro C hC i
  exact ⟨positive C hC i,height (C i) (mem_iUnion.mpr ⟨i,C,hC,rfl⟩)⟩

end NRR.Localization
