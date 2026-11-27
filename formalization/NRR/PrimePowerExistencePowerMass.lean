import NRR.PrimePowerExistencePowerCells

/-! Continuity of power-cell masses as the distinct sites and weights vary. -/

noncomputable section
open Set MeasureTheory Filter Topology

namespace NRR.PrimePower

private theorem score_tie_null {d n : ℕ} (x : Configuration d n) (w : Fin n → ℝ)
    (μ : Measure (Space d)) (hμ : μ ≪ volume) {i j : Fin n} (hij : i ≠ j) :
    μ {y | powerScore x w j y = powerScore x w i y} = 0 := by
  let L := innerSL ℝ (x.val j - x.val i)
  have ha : x.val j - x.val i ≠ 0 := sub_ne_zero.mpr (x.property.ne hij.symm)
  have surj : Function.Surjective L := by
    have haa : inner ℝ (x.val j - x.val i) (x.val j - x.val i) ≠ 0 :=
      (real_inner_self_pos.mpr ha).ne'
    intro r
    refine ⟨(r / inner ℝ (x.val j - x.val i) (x.val j - x.val i)) • (x.val j - x.val i), ?_⟩
    change inner ℝ (x.val j - x.val i)
      ((r / inner ℝ (x.val j - x.val i) (x.val j - x.val i)) • (x.val j - x.val i)) = r
    rw [inner_smul_right]
    exact div_mul_cancel₀ r haa
  have heq : {y | powerScore x w j y = powerScore x w i y} = L ⁻¹' {w i - w j} := by
    ext y
    change (powerScore x w j y = powerScore x w i y) ↔ L y = w i - w j
    simp only [powerScore, L, innerSL_apply, inner_sub_left]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact ParallelCuts.hyperplane_null μ L hμ surj (w i - w j)

theorem continuous_powerCell_mass {d n : ℕ} (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (i : Fin n) :
    Continuous (fun p : Configuration d n × (Fin n → ℝ) =>
      μ.real (powerCell K p.1 p.2 i)) := by
  let cell (p : Configuration d n × (Fin n → ℝ)) := powerCell K p.1 p.2 i
  have meas (p) : MeasurableSet (cell p) := (isCompact_powerCell K p.1 p.2 i).isClosed.measurableSet
  have repr (p) : μ.real (cell p) = ∫ y, (cell p).indicator (fun _ => (1 : ℝ)) y ∂μ := by
    rw [integral_indicator (meas p), setIntegral_one_eq_measureReal]
  have cs (j : Fin n) (y : Space d) :
      Continuous (fun p : Configuration d n × (Fin n → ℝ) => powerScore p.1 p.2 j y) := by
    exact (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).inner
      continuous_const).add ((continuous_apply j).comp continuous_snd)
  refine continuous_iff_seqContinuous.mpr ?_
  intro ps p hp
  change Tendsto (fun k => μ.real (cell (ps k))) atTop (𝓝 (μ.real (cell p)))
  simp only [repr]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun k => aestronglyMeasurable_const.indicator (meas (ps k))) (integrable_const 1)
  · intro k
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ cell (ps k) <;> simp [hy]
  · have avoid (j : Fin n) : ∀ᵐ y ∂μ,
        j = i ∨ powerScore p.1 p.2 j y ≠ powerScore p.1 p.2 i y := by
      by_cases hji : j = i
      · exact Eventually.of_forall fun _ => Or.inl hji
      · have ht := compl_mem_ae_iff.mpr (score_tie_null p.1 p.2 μ hμ (Ne.symm hji))
        filter_upwards [ht] with y hy
        exact Or.inr hy
    have all := ae_all_iff.mpr avoid
    filter_upwards [all] with y hy
    have ev (j : Fin n) : ∀ᶠ k in atTop,
        (powerScore (ps k).1 (ps k).2 j y ≤ powerScore (ps k).1 (ps k).2 i y) ↔
          powerScore p.1 p.2 j y ≤ powerScore p.1 p.2 i y := by
      rcases hy j with rfl | hne
      · exact Eventually.of_forall fun _ => iff_of_true le_rfl le_rfl
      · have hd := (((cs j y).tendsto p).comp hp).sub (((cs i y).tendsto p).comp hp)
        simp only [Function.comp_def] at hd
        rcases hne.lt_or_gt with hl | hl
        · filter_upwards [hd.eventually (gt_mem_nhds (sub_neg.mpr hl))] with k hk
          exact iff_of_true (by linarith) hl.le
        · filter_upwards [hd.eventually (lt_mem_nhds (sub_pos.mpr hl))] with k hk
          exact iff_of_false (by linarith) (not_le.mpr hl)
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_all.mpr ev] with k hk
    have hm : y ∈ cell (ps k) ↔ y ∈ cell p := by
      simp only [cell, mem_powerCell_iff]
      exact and_congr_right (fun _ => forall_congr' hk)
    by_cases h : y ∈ cell p
    · simp [h, hm.mpr h]
    · have hnot : y ∉ cell (ps k) := fun h' => h (hm.mp h')
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hnot]

end NRR.PrimePower
