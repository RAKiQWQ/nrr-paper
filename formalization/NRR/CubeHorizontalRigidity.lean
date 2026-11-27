import NRR.CylinderRigidity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Horizontal rigidity for partitions of the square prism. -/

noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal

namespace NRR.CubeHorizontalRigidity

/-- The transverse square in Euclidean coordinates. -/
def square : Set (Space 2) := {u | ∀ j : Fin 2, u j ∈ Icc (-1 : ℝ) 1}

theorem square_closed : IsClosed (square) := by
  rw [square]
  have heq : ({u : Space 2 | ∀ j : Fin 2, u j ∈ Icc (-1 : ℝ) 1} : Set (Space 2)) =
      ⋂ j : Fin 2, {u : Space 2 | u j ∈ Icc (-1 : ℝ) 1} := by
    ext u
    simp
  rw [heq]
  exact isClosed_iInter fun j => isClosed_Icc.preimage
    (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 2 => ℝ) j)

theorem square_convex : Convex ℝ square := by
  rw [square]
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at hx hy ⊢
  intro j
  constructor <;> dsimp at * <;> nlinarith [hx j |>.1, hx j |>.2, hy j |>.1, hy j |>.2]

theorem square_compact : IsCompact square := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨square_closed, ?_⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : Space 2)]
  refine ⟨2, ?_⟩
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  have hcoord (j : Fin 2) : ‖u j‖ ^ 2 ≤ 1 := by
    have h := hu j
    rw [mem_Icc] at h
    have habs : |u j| ≤ 1 := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (u j)]
  have hsum : (∑ j : Fin 2, ‖u j‖ ^ 2) ≤ 2 := by
    convert add_le_add (hcoord 0) (hcoord 1) using 1 <;> norm_num [Fin.sum_univ_two]
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  calc
    √(u 0 ^ 2 + u 1 ^ 2) ≤ √2 := by
      apply Real.sqrt_le_sqrt
      simpa [Fin.sum_univ_two, Real.norm_eq_abs] using hsum
    _ ≤ 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem square_interior_nonempty : (interior square).Nonempty := by
  have ball_sub : Metric.ball (0 : Space 2) 1 ⊆ square := by
    intro u hu j
    rw [Metric.mem_ball, dist_zero_right] at hu
    have hn := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) u j
    rw [Real.norm_eq_abs] at hn
    have habs : |u j| < 1 := lt_of_le_of_lt hn hu
    rw [mem_Icc]
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  refine ⟨0, interior_maximal ball_sub Metric.isOpen_ball ?_⟩
  simp

/-- Uniform probability measure on the transverse square. -/
def uniformSquare : Measure (Space 2) :=
  (volume square)⁻¹ • volume.restrict square

theorem square_volume_pos : 0 < volume (square) :=
  MeasureTheory.Measure.measure_pos_of_nonempty_interior volume square_interior_nonempty

theorem uniformSquare_probability : IsProbabilityMeasure uniformSquare := by
  constructor
  simp only [uniformSquare, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel square_volume_pos.ne'
    square_compact.measure_lt_top.ne

theorem uniformSquare_ac : uniformSquare ≪ volume :=
  Measure.absolutelyContinuous_restrict.smul_left _

theorem square_dominates : volume.restrict square ≪ uniformSquare :=
  Measure.absolutelyContinuous_smul (by
    exact ENNReal.inv_ne_zero.mpr square_compact.measure_lt_top.ne)

theorem uniformSquare_full : uniformSquare square = 1 := by
  simp only [uniformSquare, Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul]
  exact ENNReal.inv_mul_cancel square_volume_pos.ne' square_compact.measure_lt_top.ne

theorem uniformSquare_prod_restrict :
    uniformSquare.prod volume = (volume square)⁻¹ •
      volume.restrict (square ×ˢ (univ : Set ℝ)) := by
  rw [uniformSquare, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ]
  rfl

theorem uniformSquare_prod_on {S : Set (Space 2 × ℝ)}
    (hS : S ⊆ square ×ˢ (univ : Set ℝ)) :
    (uniformSquare.prod volume).restrict S = (volume square)⁻¹ • volume.restrict S := by
  rw [uniformSquare_prod_restrict, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset hS]

/-- Coordinatewise zero Lebesgue moments force the full vector moment to vanish
for the normalized transverse measure used by cylinder rigidity. -/
theorem normalized_moment_zero {S : Set (Space 2 × ℝ)}
    (hcompact : IsCompact S)
    (hS : S ⊆ square ×ˢ (univ : Set ℝ))
    (hzero : ∀ j : Fin 2, ∫ p in S, p.1 j ∂volume = 0) :
    ∫ p in S, p.1 ∂(uniformSquare.prod volume) = 0 := by
  have hs := uniformSquare_prod_on (S := S) hS
  have hi : Integrable (fun p : Space 2 × ℝ => p.1) (volume.restrict S) :=
    continuous_fst.continuousOn.integrableOn_compact hcompact
  have hbase : ∫ p in S, p.1 ∂volume = 0 := by
    apply PiLp.ext
    intro j
    rw [← PiLp.proj_apply (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j
      (∫ p in S, p.1 ∂volume)]
    rw [← (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).integral_comp_comm hi]
    simpa using hzero j
  apply PiLp.ext
  rw [hs, integral_smul_measure, hbase]
  simp

/-- A convex positive-volume partition of the whole square prism with zero
horizontal coordinate moments consists of horizontal layers. -/
theorem partition_is_slabs {n : ℕ}
    (C : Fin n → Set (Space 2 × ℝ))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hcover : (⋃ i, C i) = square ×ˢ Icc (-1 : ℝ) 1)
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (hm : ∀ i, 0 < (volume (C i)).toReal)
    (centered : ∀ (i : Fin n) (j : Fin 2), ∫ p in C i, p.1 j ∂volume = 0) :
    ∀ i, ∃ a b : ℝ, a < b ∧ C i = square ×ˢ Icc a b := by
  letI := uniformSquare_probability
  have positive (i : Fin n) : 0 < ((uniformSquare.prod volume).real (C i)) := by
    have hsubset : C i ⊆ square ×ˢ (univ : Set ℝ) := by
      have hsub : C i ⊆ ⋃ k, C k := subset_iUnion C i
      rw [hcover] at hsub
      exact fun p hp => ⟨(hsub hp).1, mem_univ _⟩
    have hscale : (uniformSquare.prod volume) (C i) =
        (volume square)⁻¹ * volume (C i) := by
      have h := congrArg (fun μ : Measure (Space 2 × ℝ) => μ univ)
        (uniformSquare_prod_on (S := C i) hsubset)
      simpa [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul] using h
    have hv : 0 < volume (C i) := (ENNReal.toReal_pos_iff.mp (hm i)).1
    have hp : 0 < (uniformSquare.prod volume) (C i) := by
      rw [hscale]
      exact ENNReal.mul_pos
        (ENNReal.inv_ne_zero.mpr square_compact.measure_lt_top.ne) hv.ne'
    exact ENNReal.toReal_pos hp.ne' (hc i).measure_lt_top.ne
  apply Cylinder.partition_is_slabs uniformSquare uniformSquare_ac square_closed square_convex
    square_dominates uniformSquare_full C hc hv hcover disj positive ?_
  intro i
  apply normalized_moment_zero (hc i)
  · have hsub : C i ⊆ ⋃ k, C k := subset_iUnion C i
    rw [hcover] at hsub
    exact fun p hp => ⟨(hsub hp).1, mem_univ _⟩
  · exact centered i

end NRR.CubeHorizontalRigidity
