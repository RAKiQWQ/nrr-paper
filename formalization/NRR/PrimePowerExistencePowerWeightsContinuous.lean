import NRR.PrimePowerExistencePowerWeightsUnique
import Mathlib.Topology.MetricSpace.Sequences

/-! Continuous normalized equal-mass power weights for measures with a
positive volume background. Existence is valid even without that background;
it is used only for uniqueness and hence continuity of this choice. -/

noncomputable section
open Set MeasureTheory Filter Topology Metric TopologicalSpace

namespace NRR.PrimePower

variable {d n : ℕ} [NeZero n]

theorem exists_normalized_equalMass_weights (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) :
    ∃ w : Fin n → ℝ, w 0 = 0 ∧ ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n := by
  obtain ⟨w,hw⟩ := exists_equalMass_powerWeights K μ hμ x
  refine ⟨fun i => w i-w 0,sub_self _,fun i => ?_⟩
  have he := powerCell_add_constant K x w (-w 0) i
  simp only [← sub_eq_add_neg] at he
  rw [he]
  exact hw i

def normalizedPowerWeights (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) : Fin n → ℝ :=
  Classical.choose (exists_normalized_equalMass_weights K μ hμ x)

theorem normalizedPowerWeights_zero (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) :
    normalizedPowerWeights K μ hμ x 0 = 0 :=
  (Classical.choose_spec (exists_normalized_equalMass_weights K μ hμ x)).1

theorem normalizedPowerWeights_mass (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) (i : Fin n) :
    μ.real (powerCell K x (normalizedPowerWeights K μ hμ x) i) = μ.real K.points / n :=
  (Classical.choose_spec (exists_normalized_equalMass_weights K μ hμ x)).2 i

theorem positive_powerCell_of_equalMass (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (mass : 0 < μ K.points) (x : Configuration d n) (w : Fin n → ℝ)
    (equal : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n) (i : Fin n) :
    0 < μ (powerCell K x w i) := by
  apply (ENNReal.toReal_pos_iff.mp ?_).1
  change 0 < μ.real (powerCell K x w i)
  rw [equal i]
  exact div_pos (ENNReal.toReal_pos mass.ne' (measure_ne_top _ _))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))

theorem weight_difference_le (K : Body d) (x : Configuration d n) (w : Fin n → ℝ)
    (nonempty : ∀ i, (powerCell K x w i).Nonempty) {B : ℝ}
    (bound : ∀ i y, y ∈ K.points → |inner ℝ (x.val i) y| ≤ B) (i j : Fin n) :
    w j-w i ≤ 2*B := by
  obtain ⟨y,hy⟩ := nonempty i
  have hs := ((mem_powerCell_iff K x w i y).mp hy).2 j
  have bi := (abs_le.mp (bound i y hy.1)).2
  have bj := (abs_le.mp (bound j y hy.1)).1
  dsimp [powerScore] at hs
  linarith

theorem normalized_weights_bound (K : Body d) (x : Configuration d n) (w : Fin n → ℝ)
    (nonempty : ∀ i, (powerCell K x w i).Nonempty) (zero : w 0 = 0)
    {B : ℝ} (hB : 0 ≤ B)
    (bound : ∀ i y, y ∈ K.points → |inner ℝ (x.val i) y| ≤ B) : ‖w‖ ≤ 2*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*B)).mpr
  intro i
  rw [Real.norm_eq_abs,abs_le]
  have hi := weight_difference_le K x w nonempty bound 0 i
  have hz := weight_difference_le K x w nonempty bound i 0
  rw [zero] at hi hz
  constructor <;> linarith

theorem continuous_normalizedPowerWeights (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) : Continuous (normalizedPowerWeights (n := n) K μ hμ) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro xs x near
  let F := normalizedPowerWeights (n := n) K μ hμ
  have normSites : Tendsto (fun k => (xs k).val) atTop (𝓝 x.val) :=
    (continuous_subtype_val.tendsto x).comp near
  obtain ⟨R,hR,boundR⟩ := (Metric.isBounded_range_of_tendsto _ normSites).exists_pos_norm_le
  obtain ⟨T,hT,boundT⟩ := K.val.isCompact.isBounded.exists_pos_norm_le
  let B := R*T+1
  have hB : 0 < B := by dsimp [B]; positivity
  have scoreBound (k) (i) (y) (hy : y ∈ K.points) : |inner ℝ ((xs k).val i) y| ≤ B := by
    calc
      _ ≤ ‖(xs k).val i‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖(xs k).val‖ * T := mul_le_mul (norm_le_pi_norm _ i) (boundT y hy)
        (norm_nonneg _) (norm_nonneg _)
      _ ≤ R*T := mul_le_mul_of_nonneg_right (boundR _ (mem_range_self k)) hT.le
      _ ≤ B := by dsimp [B]; linarith
  have bounded (k) : F (xs k) ∈ closedBall 0 (2*B) := by
    rw [mem_closedBall,dist_zero_right]
    apply normalized_weights_bound K (xs k) (F (xs k)) ?_
      (normalizedPowerWeights_zero K μ hμ (xs k)) hB.le (scoreBound k)
    intro i
    have hp := positive_powerCell_of_equalMass K μ mass (xs k) (F (xs k))
      (normalizedPowerWeights_mass K μ hμ (xs k)) i
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty] at hp
    exact lt_irrefl _ hp
  apply (isCompact_closedBall (0 : Fin n → ℝ) (2*B)).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall bounded)
  intro w _ cluster
  obtain ⟨σ,hσ,limit⟩ := FirstCountableTopology.tendsto_subseq cluster
  have xlimit := near.comp hσ.tendsto_atTop
  have pairLimit : Tendsto (fun k => (xs (σ k),F (xs (σ k)))) atTop (𝓝 (x,w)) :=
    xlimit.prodMk_nhds limit
  have equalW (i) : μ.real (powerCell K x w i) = μ.real K.points / n := by
    have hm := ((continuous_powerCell_mass K μ hμ i).tendsto (x,w)).comp pairLimit
    dsimp only [Function.comp_def] at hm
    apply tendsto_nhds_unique hm
    simpa only [F,normalizedPowerWeights_mass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => μ.real K.points / n) atTop (𝓝 (μ.real K.points / n)))
  have zeroW : w 0 = 0 := by
    have hz := ((continuous_apply (0 : Fin n)).tendsto w).comp limit
    apply tendsto_nhds_unique hz
    simpa only [Function.comp_def,F,normalizedPowerWeights_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact equalMass_weights_unique_normalized K μ hμ background mass x w (F x)
    equalW (normalizedPowerWeights_mass K μ hμ x) zeroW (normalizedPowerWeights_zero K μ hμ x)

end NRR.PrimePower
