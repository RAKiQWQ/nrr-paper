import NRR.ConvexCentroids
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! A centered positive background measure on any prescribed compact body.
Adding a suitably weighted small ball corrects its first moment while
preserving domination of ordinary volume on the whole body. -/

noncomputable section
open Set Metric MeasureTheory Topology

namespace NRR.ConvexLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_id_closedBall (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (c : E) (r : ℝ) :
    (∫ x in closedBall c r, x ∂ν) = ν.real (closedBall c r) • c := by
  let T : E → E := fun x => (2 : ℝ) • c - x
  have pre : T ⁻¹' closedBall c r = closedBall c r := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, T]
    have he : (2 : ℝ) • c - x - c = -(x-c) := by rw [two_smul]; abel
    rw [he, norm_neg]
  have mp := (Measure.measurePreserving_sub_left ν ((2 : ℝ) • c)).restrict_preimage
    (isClosed_closedBall.measurableSet : MeasurableSet (closedBall c r))
  change MeasurePreserving T _ _ at mp
  rw [pre] at mp
  have emb : MeasurableEmbedding T :=
    ((Homeomorph.subLeft ((2 : ℝ) • c)).isClosedEmbedding.measurableEmbedding)
  have H := mp.integral_comp emb id
  have hi : IntegrableOn id (closedBall c r) ν :=
    continuous_id.continuousOn.integrableOn_compact (isCompact_closedBall c r)
  haveI : IsFiniteMeasure (ν.restrict (closedBall c r)) :=
    ⟨by simpa using (isCompact_closedBall c r).measure_lt_top⟩
  change (∫ x in closedBall c r, (2 : ℝ) • c - x ∂ν) = _ at H
  have hc : Integrable (fun _ : E => (2 : ℝ) • c) (ν.restrict (closedBall c r)) :=
    integrable_const _
  have hsub : (∫ x in closedBall c r, (2 : ℝ) • c - x ∂ν) =
      (∫ _x in closedBall c r, (2 : ℝ) • c ∂ν) - (∫ x in closedBall c r, x ∂ν) :=
    integral_sub hc hi
  rw [hsub, integral_const] at H
  simp only [Measure.real, Measure.restrict_apply_univ] at H
  apply smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)
  calc
    (2 : ℝ) • (∫ x in closedBall c r, x ∂ν) =
        (∫ x in closedBall c r, x ∂ν) + (∫ x in closedBall c r, x ∂ν) := by rw [two_smul]
    _ = ν.real (closedBall c r) • ((2 : ℝ) • c) := (sub_eq_iff_eq_add.mp H).symm
    _ = (2 : ℝ) • (ν.real (closedBall c r) • c) := smul_comm _ _ _

/-- The auxiliary measure has compact support in K, dominates Haar volume
there, is absolutely continuous, and has exactly zero vector first moment. -/
theorem exists_centered_background (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    {K : Set E} (compact : IsCompact K) (origin : (0 : E) ∈ interior K) :
    ∃ ρ : Measure E, IsFiniteMeasure ρ ∧ ν.restrict K ≤ ρ ∧ ρ ≪ ν ∧
      ρ Kᶜ = 0 ∧ Integrable id ρ ∧ (∫ x, x ∂ρ) = 0 := by
  obtain ⟨r, hr, ballIn⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp origin)
  let M := ∫ x in K, x ∂ν
  let α := r / (4 * (‖M‖ + 1))
  have hα : 0 < α := by dsimp [α]; positivity
  let c := (-α) • M
  let B := closedBall c (r/4)
  have nc : ‖c‖ < r/4 := by
    rw [show ‖c‖ = α * ‖M‖ by simp [c, norm_smul, abs_of_pos hα]]
    dsimp [α]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 4 * (‖M‖+1))]
    nlinarith
  have sub : B ⊆ K := by
    intro x hx
    apply ballIn
    have hd : ‖x-c‖ ≤ r/4 := by simpa only [B, mem_closedBall, dist_eq_norm] using hx
    have hn : ‖x‖ ≤ ‖x-c‖+‖c‖ := by simpa using norm_add_le (x-c) c
    simp only [mem_ball, dist_zero_right]
    linarith
  have cb : IsCompact B := isCompact_closedBall c (r/4)
  have bp : 0 < ν B := Measure.measure_pos_of_nonempty_interior ν (by
    rw [show B = closedBall c (r/4) from rfl, interior_closedBall _ (by positivity : r/4 ≠ 0)]
    exact ⟨c, mem_ball_self (by positivity)⟩)
  have bpr : 0 < ν.real B := ENNReal.toReal_pos bp.ne' cb.measure_lt_top.ne
  let β : ℝ := (ν.real B * α)⁻¹
  have hβ : 0 < β := inv_pos.mpr (mul_pos bpr hα)
  let ρ := ν.restrict K + ENNReal.ofReal β • ν.restrict B
  haveI : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using compact.measure_lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using cb.measure_lt_top⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal β • ν.restrict B) :=
    (ν.restrict B).smul_finite (by simp)
  have hi : Integrable id (ν.restrict K) :=
    continuous_id.continuousOn.integrableOn_compact compact
  have hb : Integrable id (ν.restrict B) :=
    continuous_id.continuousOn.integrableOn_compact cb
  have hbs : Integrable id (ENNReal.ofReal β • ν.restrict B) := hb.smul_measure (by simp)
  refine ⟨ρ, inferInstance, Measure.le_add_right le_rfl,
    Measure.absolutelyContinuous_restrict.add_left
      (Measure.absolutelyContinuous_restrict.smul_left _), ?_, hi.add_measure hbs, ?_⟩
  · change (ν.restrict K + ENNReal.ofReal β • ν.restrict B) Kᶜ = 0
    rw [Measure.add_apply, Measure.smul_apply,
      Measure.restrict_apply compact.isClosed.measurableSet.compl,
      Measure.restrict_apply compact.isClosed.measurableSet.compl]
    have he : Kᶜ ∩ B = ∅ := disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right sub)
    simp [he]
  · change (∫ x, id x ∂(ν.restrict K + ENNReal.ofReal β • ν.restrict B)) = 0
    rw [integral_add_measure hi hbs, integral_smul_measure, ENNReal.toReal_ofReal hβ.le]
    change M + β • (∫ x in closedBall c (r/4), x ∂ν) = 0
    rw [integral_id_closedBall ν c (r/4)]
    change M + β • (ν.real B • ((-α) • M)) = 0
    have he : β * (ν.real B * (-α)) = -1 := by
      dsimp [β]
      field_simp
    rw [smul_smul, smul_smul, mul_assoc, he, neg_one_smul, add_neg_cancel]

end NRR.ConvexLimits
