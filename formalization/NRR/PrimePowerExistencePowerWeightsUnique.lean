import NRR.PrimePowerExistencePowerWeights
import Mathlib.Topology.Separation.Connected

/-! Uniqueness of positive-density power partitions, via the equality case
in the finite maximum potential. -/

noncomputable section
open Set MeasureTheory Filter Topology

namespace NRR.PrimePower

variable {d n : ℕ} [NeZero n]

theorem envelope_eq_on_powerCell (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (i : Fin n) {y : Space d} (hy : y ∈ powerCell K x w i) :
    powerEnvelope x w y = powerScore x w i y :=
  le_antisymm (envelope_le x w y _ ((mem_powerCell_iff K x w i y).mp hy).2)
    (score_le_envelope x w i y)

theorem integral_powerCells (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (x : Configuration d n) (w : Fin n → ℝ)
    (f : Space d → ℝ) (hf : IntegrableOn f K.points μ) :
    (∫ y in K.points, f y ∂μ) = ∑ i, ∫ y in powerCell K x w i, f y ∂μ := by
  have hd : Pairwise (fun i j => AEDisjoint μ (powerCell K x w i) (powerCell K x w j)) :=
    fun i j hij => powerCells_overlap_null K x w μ hμ hij
  rw [← powerCells_cover (Nat.pos_of_ne_zero (NeZero.ne n)) K x w] at hf ⊢
  rw [integral_iUnion_ae
    (fun i => (isCompact_powerCell K x w i).isClosed.measurableSet.nullMeasurableSet)
    hd hf,tsum_fintype]

def envelopeGap (x : Configuration d n) (w v : Fin n → ℝ)
    (i : Fin n) (y : Space d) : ℝ :=
  powerEnvelope x v y - powerEnvelope x w y - (v i-w i)

theorem continuous_envelopeGap (x : Configuration d n) (w v : Fin n → ℝ) (i : Fin n) :
    Continuous (envelopeGap x w v i) :=
  ((continuous_powerEnvelope x v).sub (continuous_powerEnvelope x w)).sub continuous_const

theorem gap_nonneg (K : Body d) (x : Configuration d n) (w v : Fin n → ℝ)
    (i : Fin n) {y : Space d} (hy : y ∈ powerCell K x w i) :
    0 ≤ envelopeGap x w v i y := by
  have he := envelope_eq_on_powerCell K x w i hy
  have hs := score_le_envelope x v i y
  dsimp [envelopeGap,powerScore] at *
  linarith

theorem gap_integral (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) (w v : Fin n → ℝ) (i : Fin n) :
    (∫ y in powerCell K x w i, envelopeGap x w v i y ∂μ) =
      (∫ y in powerCell K x w i, powerEnvelope x v y - powerEnvelope x w y ∂μ) -
        μ.real (powerCell K x w i) * (v i-w i) := by
  unfold envelopeGap
  rw [integral_sub
    (((continuous_powerEnvelope x v).sub (continuous_powerEnvelope x w)).continuousOn.integrableOn_compact
      (isCompact_powerCell K x w i)) (integrable_const _),setIntegral_const,smul_eq_mul]

theorem sum_gap_integrals (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (x : Configuration d n) (w v : Fin n → ℝ)
    (equal : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n) :
    (∑ i, ∫ y in powerCell K x w i, envelopeGap x w v i y ∂μ) =
      powerPotential K μ x v - powerPotential K μ x w := by
  simp_rw [gap_integral,equal]
  have hc := integral_powerCells K μ hμ x w (fun y => powerEnvelope x v y - powerEnvelope x w y)
    ((integrable_envelope K μ x v).sub (integrable_envelope K μ x w))
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,← hc,
    integral_sub (integrable_envelope K μ x v) (integrable_envelope K μ x w)]
  unfold powerPotential
  ring

theorem potential_minimal_of_equalMass (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (x : Configuration d n) (w : Fin n → ℝ)
    (equal : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n) :
    ∀ v, powerPotential K μ x w ≤ powerPotential K μ x v := by
  intro v
  apply sub_nonneg.mp
  rw [← sum_gap_integrals K μ hμ x w v equal]
  exact Finset.sum_nonneg fun i _ => setIntegral_nonneg
    (isCompact_powerCell K x w i).isClosed.measurableSet (fun _ hy => gap_nonneg K x w v i hy)

/-- Equality in the potential forces each old power cell to remain a
maximizing cell for the second weights almost everywhere. -/
theorem gap_ae_zero_of_equalMass (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (x : Configuration d n) (w v : Fin n → ℝ)
    (equalW : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n)
    (equalV : ∀ i, μ.real (powerCell K x v i) = μ.real K.points / n) (i : Fin n) :
    envelopeGap x w v i =ᵐ[μ.restrict (powerCell K x w i)] 0 := by
  have nn (j) : 0 ≤ ∫ y in powerCell K x w j, envelopeGap x w v j y ∂μ :=
    setIntegral_nonneg (isCompact_powerCell K x w j).isClosed.measurableSet
      (fun _ hy => gap_nonneg K x w v j hy)
  have hs : (∑ j, ∫ y in powerCell K x w j, envelopeGap x w v j y ∂μ) = 0 := by
    rw [sum_gap_integrals K μ hμ x w v equalW]
    exact sub_eq_zero.mpr (le_antisymm
      (potential_minimal_of_equalMass K μ hμ x v equalV w)
      (potential_minimal_of_equalMass K μ hμ x w equalW v))
  have hi : (∫ y in powerCell K x w i, envelopeGap x w v i y ∂μ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => nn j)).mp hs i (Finset.mem_univ i)
  apply (integral_eq_zero_iff_of_nonneg_ae ?_
    ((continuous_envelopeGap x w v i).continuousOn.integrableOn_compact
      (isCompact_powerCell K x w i))).mp hi
  filter_upwards [ae_restrict_mem (isCompact_powerCell K x w i).isClosed.measurableSet] with y hy
  exact gap_nonneg K x w v i hy

theorem powerCell_subset_of_equalMass (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (x : Configuration d n) (w v : Fin n → ℝ)
    (equalW : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n)
    (equalV : ∀ i, μ.real (powerCell K x v i) = μ.real K.points / n) (i : Fin n) :
    powerCell K x w i ⊆ powerCell K x v i := by
  have pos : 0 < μ (powerCell K x w i) := by
    apply (ENNReal.toReal_pos_iff.mp ?_).1
    change 0 < μ.real (powerCell K x w i)
    rw [equalW i]
    exact div_pos (ENNReal.toReal_pos mass.ne' (measure_ne_top _ _))
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  have full := powerCell_interior_nonempty K x w μ hμ i pos
  have dom : volume.restrict (powerCell K x w i) ≪ μ.restrict (powerCell K x w i) := by
    have hd := background.restrict (powerCell K x w i)
    rw [Measure.restrict_restrict_of_subset (show powerCell K x w i ⊆ K.points from
      inter_subset_left)] at hd
    exact hd
  have heq := Measure.eqOn_of_ae_eq
    (dom.ae_eq (gap_ae_zero_of_equalMass K μ hμ x w v equalW equalV i))
    (continuous_envelopeGap x w v i).continuousOn continuous_const.continuousOn
    (by
      rw [(convex_powerCell K x w i).closure_interior_eq_closure_of_nonempty_interior full,
        (isCompact_powerCell K x w i).isClosed.closure_eq])
  intro y hy
  have hg := heq hy
  have hw := envelope_eq_on_powerCell K x w i hy
  have he : powerEnvelope x v y = powerScore x v i y := by
    dsimp [envelopeGap,powerScore] at *
    linarith
  apply (mem_powerCell_iff K x v i y).mpr
  refine ⟨hy.1,fun j => ?_⟩
  rw [← he]
  exact score_le_envelope x v j y

/-- The cell sets are genuinely unique under a positive Haar background;
the conclusion is equality of closed convex bodies, not merely a.e. equality. -/
theorem powerCell_eq_of_equalMass (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (x : Configuration d n) (w v : Fin n → ℝ)
    (equalW : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n)
    (equalV : ∀ i, μ.real (powerCell K x v i) = μ.real K.points / n) (i : Fin n) :
    powerCell K x w i = powerCell K x v i :=
  Subset.antisymm (powerCell_subset_of_equalMass K μ hμ background mass x w v equalW equalV i)
    (powerCell_subset_of_equalMass K μ hμ background mass x v w equalV equalW i)

theorem equalMass_weights_differ_constant (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (x : Configuration d n) (w v : Fin n → ℝ)
    (equalW : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n)
    (equalV : ∀ i, μ.real (powerCell K x v i) = μ.real K.points / n) :
    ∃ c : ℝ, ∀ i, v i-w i = c := by
  have same (i) := powerCell_eq_of_equalMass K μ hμ background mass x w v equalW equalV i
  let f := fun y => powerEnvelope x v y - powerEnvelope x w y
  have cf : Continuous f := (continuous_powerEnvelope x v).sub (continuous_powerEnvelope x w)
  have onCell (i) {y} (hy : y ∈ powerCell K x w i) : f y = v i-w i := by
    have hv : y ∈ powerCell K x v i := same i ▸ hy
    dsimp [f]
    rw [envelope_eq_on_powerCell K x w i hy,envelope_eq_on_powerCell K x v i hv]
    dsimp [powerScore]
    ring
  have finite : (f '' K.points).Finite := by
    apply (Set.finite_range (fun i : Fin n => v i-w i)).subset
    rintro r ⟨y,hy,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((powerCells_cover (Nat.pos_of_ne_zero (NeZero.ne n)) K x w).symm ▸ hy)
    exact mem_range.mpr ⟨i,(onCell i hi).symm⟩
  have connected : IsPreconnected (f '' K.points) := K.property.1.isPreconnected.image f cf.continuousOn
  have ss : (f '' K.points).Subsingleton := by
    by_contra h
    exact finite.not_infinite (connected.infinite_of_nontrivial (not_subsingleton_iff.mp h))
  have cellNonempty (i) : (powerCell K x w i).Nonempty := by
    have pos : 0 < μ (powerCell K x w i) := by
      apply (ENNReal.toReal_pos_iff.mp ?_).1
      change 0 < μ.real (powerCell K x w i)
      rw [equalW i]
      exact div_pos (ENNReal.toReal_pos mass.ne' (measure_ne_top _ _))
        (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h,measure_empty] at pos
    exact lt_irrefl _ pos
  refine ⟨v 0-w 0,fun i => ?_⟩
  obtain ⟨yi,hyi⟩ := cellNonempty i
  obtain ⟨y0,hy0⟩ := cellNonempty 0
  have he := ss (mem_image_of_mem f hyi.1) (mem_image_of_mem f hy0.1)
  rw [onCell i hyi,onCell 0 hy0] at he
  exact he

/-- Fixing one reference weight removes the sole ambiguity. The cell
partition itself remains permutation-equivariant independently of this choice. -/
theorem equalMass_weights_unique_normalized (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (x : Configuration d n) (w v : Fin n → ℝ)
    (equalW : ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n)
    (equalV : ∀ i, μ.real (powerCell K x v i) = μ.real K.points / n)
    (zeroW : w 0 = 0) (zeroV : v 0 = 0) : w = v := by
  obtain ⟨c,hc⟩ := equalMass_weights_differ_constant K μ hμ background mass x w v equalW equalV
  have cz : c = 0 := by simpa only [zeroW,zeroV,sub_self,eq_comm] using hc 0
  ext i
  have hi := hc i
  rw [cz] at hi
  exact (sub_eq_zero.mp hi).symm

end NRR.PrimePower
