import NRR.PrimePowerExistencePowerMass
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.Compact

/-! Existence of equal-mass affine power weights by minimizing their finite
maximum potential. The proof uses finite differences rather than assuming
differentiability of parameter-dependent integrals. -/

noncomputable section
open Set MeasureTheory Filter Topology Metric

namespace NRR.PrimePower

variable {d n : ℕ} [NeZero n]

def powerEnvelope (x : Configuration d n) (w : Fin n → ℝ) (y : Space d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => powerScore x w i y)

theorem score_le_envelope (x : Configuration d n) (w : Fin n → ℝ)
    (i : Fin n) (y : Space d) : powerScore x w i y ≤ powerEnvelope x w y :=
  Finset.le_sup' (fun j => powerScore x w j y) (Finset.mem_univ i)

theorem envelope_le (x : Configuration d n) (w : Fin n → ℝ)
    (y : Space d) (a : ℝ) (ha : ∀ i, powerScore x w i y ≤ a) :
    powerEnvelope x w y ≤ a :=
  Finset.sup'_le _ _ (fun i _ => ha i)

theorem exists_envelope_eq (x : Configuration d n) (w : Fin n → ℝ)
    (y : Space d) : ∃ i, powerEnvelope x w y = powerScore x w i y := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => powerScore x w i y)
  exact ⟨i,hi⟩

theorem continuous_powerEnvelope (x : Configuration d n) (w : Fin n → ℝ) :
    Continuous (powerEnvelope x w) := by
  unfold powerEnvelope
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  exact (continuous_const.inner continuous_id).add continuous_const

theorem envelope_weight_bound (x : Configuration d n) (w v : Fin n → ℝ) (y : Space d) :
    |powerEnvelope x w y - powerEnvelope x v y| ≤ ‖w-v‖ := by
  have bound (a b : Fin n → ℝ) : powerEnvelope x a y ≤ powerEnvelope x b y + ‖a-b‖ := by
    apply envelope_le
    intro i
    have h := norm_le_pi_norm (a-b) i
    have hi : a i - b i ≤ ‖a-b‖ := (le_abs_self _).trans (by simpa using h)
    have hs := score_le_envelope x b i y
    dsimp [powerScore] at *
    linarith
  rw [abs_le]
  exact ⟨by have h := bound v w; rw [norm_sub_rev] at h; linarith, by linarith [bound w v]⟩

def powerPotential (K : Body d) (μ : Measure (Space d)) (x : Configuration d n)
    (w : Fin n → ℝ) : ℝ :=
  (∫ y in K.points, powerEnvelope x w y ∂μ) - (μ.real K.points / n) * ∑ i, w i

theorem integrable_envelope (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) (w : Fin n → ℝ) : IntegrableOn (powerEnvelope x w) K.points μ :=
  (continuous_powerEnvelope x w).continuousOn.integrableOn_compact K.val.isCompact

theorem continuous_powerPotential (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) : Continuous (powerPotential K μ x) := by
  have hL : LipschitzWith ⟨μ.real K.points, measureReal_nonneg⟩
      (fun w : Fin n → ℝ => ∫ y in K.points, powerEnvelope x w y ∂μ) := by
    apply LipschitzWith.of_dist_le_mul
    intro w v
    rw [dist_eq_norm, ← integral_sub (integrable_envelope K μ x w)
      (integrable_envelope K μ x v)]
    have h := norm_integral_le_of_norm_le_const
      (μ := μ.restrict K.points) (f := fun y => powerEnvelope x w y - powerEnvelope x v y)
      (Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using (envelope_weight_bound x w v y))
    simpa only [Measure.real, Measure.restrict_apply_univ, dist_eq_norm, mul_comm] using h
  exact hL.continuous.sub (continuous_const.mul (continuous_finset_sum _ (fun i _ => continuous_apply i)))

theorem envelope_add_constant (x : Configuration d n) (w : Fin n → ℝ)
    (c : ℝ) (y : Space d) :
    powerEnvelope x (fun i => w i+c) y = powerEnvelope x w y+c := by
  obtain ⟨i,hi⟩ := exists_envelope_eq x w y
  apply le_antisymm
  · apply envelope_le
    intro j
    have hj := score_le_envelope x w j y
    dsimp [powerScore] at *
    linarith
  · have hj := score_le_envelope x (fun i => w i+c) i y
    dsimp [powerScore] at *
    linarith

theorem potential_add_constant (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) (w : Fin n → ℝ) (c : ℝ) :
    powerPotential K μ x (fun i => w i+c) = powerPotential K μ x w := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold powerPotential
  simp_rw [envelope_add_constant]
  rw [integral_add (integrable_envelope K μ x w) (integrable_const c), integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem exists_score_bound (K : Body d) (x : Configuration d n) :
    ∃ B : ℝ, 0 < B ∧ ∀ i y, y ∈ K.points → |inner ℝ (x.val i) y| ≤ B := by
  obtain ⟨T,hT,bound⟩ := K.val.isCompact.isBounded.exists_pos_norm_le
  refine ⟨‖x.val‖ * T + 1,by positivity,?_⟩
  intro i y hy
  calc
    |inner ℝ (x.val i) y| ≤ ‖x.val i‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x.val‖ * T := mul_le_mul (norm_le_pi_norm x.val i) (bound y hy) (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := by linarith

/-- Normalization followed by clipping gives a bounded competitor with no
larger potential. It is the compactness step behind actual weight existence. -/
theorem exists_box_competitor (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) {B : ℝ} (hB : 0 < B)
    (bound : ∀ i y, y ∈ K.points → |inner ℝ (x.val i) y| ≤ B)
    (w : Fin n → ℝ) :
    ∃ v : Fin n → ℝ, (∀ i, -(2*B+1) ≤ v i ∧ v i ≤ 0) ∧
      powerPotential K μ x v ≤ powerPotential K μ x w := by
  obtain ⟨j,hj⟩ := Finite.exists_max w
  let z := fun i => w i-w j
  have hz (i) : z i ≤ 0 := sub_nonpos.mpr (hj i)
  have hzj : z j = 0 := sub_self _
  let v := fun i => max (z i) (-(2*B+1))
  have vm (i) : z i ≤ v i := le_max_left _ _
  have henv : ∀ y ∈ K.points, powerEnvelope x v y = powerEnvelope x z y := by
    intro y hy
    apply le_antisymm
    · apply envelope_le
      intro i
      rcases le_total (-(2*B+1)) (z i) with hi | hi
      · have hv : v i = z i := max_eq_left hi
        simpa only [powerScore,hv] using score_le_envelope x z i y
      · have hv : v i = -(2*B+1) := max_eq_right hi
        have lower := score_le_envelope x z j y
        have bi := (abs_le.mp (bound i y hy)).2
        have bj := (abs_le.mp (bound j y hy)).1
        dsimp [powerScore] at lower ⊢
        rw [hv]
        rw [hzj] at lower
        linarith
    · apply envelope_le
      intro i
      exact (show powerScore x z i y ≤ powerScore x v i y from add_le_add_left (vm i) _).trans
        (score_le_envelope x v i y)
  have hpot : powerPotential K μ x v ≤ powerPotential K μ x z := by
    unfold powerPotential
    have heq : (∫ y in K.points, powerEnvelope x v y ∂μ) =
        (∫ y in K.points, powerEnvelope x z y ∂μ) :=
      setIntegral_congr_fun K.val.isCompact.isClosed.measurableSet henv
    rw [heq]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => vm i))
      (div_nonneg measureReal_nonneg (Nat.cast_nonneg _))) _
  refine ⟨v, fun i => ⟨le_max_right _ _,max_le (hz i) (by linarith)⟩,?_⟩
  calc
    powerPotential K μ x v ≤ powerPotential K μ x z := hpot
    _ = powerPotential K μ x w := potential_add_constant K μ x w (-w j)

theorem exists_potential_minimizer (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) : ∃ w : Fin n → ℝ, ∀ v, powerPotential K μ x w ≤ powerPotential K μ x v := by
  obtain ⟨B,hB,bound⟩ := exists_score_bound K x
  let box : Set (Fin n → ℝ) := Icc (fun _ => -(2*B+1)) 0
  have hbox : IsCompact box := isCompact_Icc
  have nonempty : box.Nonempty := ⟨0,by constructor <;> intro i <;> simp <;> linarith⟩
  obtain ⟨w,hw,hmin⟩ := hbox.exists_isMinOn nonempty (continuous_powerPotential K μ x).continuousOn
  refine ⟨w, fun v => ?_⟩
  obtain ⟨z,hz,hcomp⟩ := exists_box_competitor K μ x hB bound v
  exact (hmin (show z ∈ box from ⟨fun i => (hz i).1,fun i => (hz i).2⟩)).trans hcomp

def raiseWeight (w : Fin n → ℝ) (i : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun j => w j + if j = i then t else 0

theorem raiseWeight_self (w : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    raiseWeight w i t i = w i+t := by simp [raiseWeight]

theorem raiseWeight_other (w : Fin n → ℝ) {i j : Fin n} (hji : j ≠ i) (t : ℝ) :
    raiseWeight w i t j = w j := by simp [raiseWeight,hji]

theorem sum_raiseWeight (w : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (∑ j, raiseWeight w i t j) = (∑ j, w j)+t := by
  simp [raiseWeight,Finset.sum_add_distrib]

theorem envelope_raise_le (K : Body d) (x : Configuration d n) (w : Fin n → ℝ)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) (y : Space d) (hy : y ∈ K.points) :
    powerEnvelope x (raiseWeight w i t) y - powerEnvelope x w y ≤
      (powerCell K x (raiseWeight w i t) i).indicator (fun _ => t) y := by
  obtain ⟨j,hj⟩ := exists_envelope_eq x (raiseWeight w i t) y
  have maxj (k) : powerScore x (raiseWeight w i t) k y ≤ powerScore x (raiseWeight w i t) j y := by
    rw [← hj]
    exact score_le_envelope x _ k y
  by_cases hm : y ∈ powerCell K x (raiseWeight w i t) i
  · rw [Set.indicator_of_mem hm]
    rw [hj]
    by_cases hji : j = i
    · subst j
      have he : powerScore x (raiseWeight w i t) i y = powerScore x w i y+t := by
        simp [powerScore,raiseWeight,add_assoc]
      rw [he]
      linarith [score_le_envelope x w i y]
    · have he : powerScore x (raiseWeight w i t) j y = powerScore x w j y := by
        simp [powerScore,raiseWeight,hji]
      rw [he]
      linarith [score_le_envelope x w j y]
  · rw [Set.indicator_of_notMem hm,hj]
    have hji : j ≠ i := by
      intro he
      subst j
      exact hm ((mem_powerCell_iff K x _ i y).mpr ⟨hy,maxj⟩)
    have he : powerScore x (raiseWeight w i t) j y = powerScore x w j y := by
      simp [powerScore,raiseWeight,hji]
    rw [he]
    linarith [score_le_envelope x w j y]

theorem potential_raise_le (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) (w : Fin n → ℝ) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    powerPotential K μ x (raiseWeight w i t) - powerPotential K μ x w ≤
      t * (μ.real (powerCell K x (raiseWeight w i t) i) - μ.real K.points / n) := by
  let A := powerCell K x (raiseWeight w i t) i
  have meas : MeasurableSet A := (isCompact_powerCell K x _ i).isClosed.measurableSet
  have hint : IntegrableOn (A.indicator (fun _ => t)) K.points μ :=
    (integrable_const t).indicator meas
  have hmono := integral_mono_ae
    ((integrable_envelope K μ x (raiseWeight w i t)).sub (integrable_envelope K μ x w))
    hint (by
      filter_upwards [ae_restrict_mem K.val.isCompact.isClosed.measurableSet] with y hy
      exact envelope_raise_le K x w i ht y hy)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (integrable_envelope K μ x (raiseWeight w i t))
    (integrable_envelope K μ x w),setIntegral_indicator meas,
    inter_eq_right.mpr (show A ⊆ K.points from inter_subset_left),setIntegral_const,
    smul_eq_mul] at hmono
  calc
    powerPotential K μ x (raiseWeight w i t) - powerPotential K μ x w =
        ((∫ y in K.points, powerEnvelope x (raiseWeight w i t) y ∂μ) -
          (∫ y in K.points, powerEnvelope x w y ∂μ)) - (μ.real K.points / n)*t := by
      unfold powerPotential
      rw [sum_raiseWeight]
      ring
    _ ≤ t * μ.real A - (μ.real K.points / n)*t :=
      sub_le_sub_right (by simpa only [mul_comm] using hmono) _
    _ = _ := by dsimp [A]; ring

theorem continuous_raiseWeight (w : Fin n → ℝ) (i : Fin n) :
    Continuous (fun t : ℝ => raiseWeight w i t) := by
  refine continuous_pi (fun j => ?_)
  by_cases hji : j = i
  · simpa [raiseWeight,hji] using (continuous_const.add continuous_id :
      Continuous (fun t : ℝ => w i+t))
  · simpa [raiseWeight,hji] using (continuous_const : Continuous (fun _ : ℝ => w j))

theorem raiseWeight_zero (w : Fin n → ℝ) (i : Fin n) : raiseWeight w i 0 = w := by
  ext j
  simp [raiseWeight]

theorem continuous_mass_raiseWeight (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) (w : Fin n → ℝ)
    (i : Fin n) : Continuous (fun t : ℝ => μ.real (powerCell K x (raiseWeight w i t) i)) := by
  have cp : Continuous (fun t : ℝ => (x,raiseWeight w i t)) :=
    continuous_const.prodMk (continuous_raiseWeight w i)
  have hc := (continuous_powerCell_mass K μ hμ i).comp cp
  dsimp only [Function.comp_def] at hc
  exact hc

theorem mass_lower_raised (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (x : Configuration d n) (w : Fin n → ℝ)
    (minimal : ∀ v, powerPotential K μ x w ≤ powerPotential K μ x v) (i : Fin n)
    {t : ℝ} (ht : 0 < t) :
    μ.real K.points / n ≤ μ.real (powerCell K x (raiseWeight w i t) i) := by
  have h := potential_raise_le K μ x w i ht.le
  have hm := minimal (raiseWeight w i t)
  have hn : 0 ≤ t * (μ.real (powerCell K x (raiseWeight w i t) i) - μ.real K.points / n) :=
    (sub_nonneg.mpr hm).trans h
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ht).mp hn)

theorem mass_lower_of_potential_minimizer (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) (w : Fin n → ℝ)
    (minimal : ∀ v, powerPotential K μ x w ≤ powerPotential K μ x v) (i : Fin n) :
    μ.real K.points / n ≤ μ.real (powerCell K x w i) := by
  have limit := ((continuous_mass_raiseWeight K μ hμ x w i).tendsto 0).comp
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h : μ.real K.points / n ≤ μ.real (powerCell K x (raiseWeight w i 0) i) :=
    ge_of_tendsto' limit (fun k => mass_lower_raised K μ x w minimal i
      (show 0 < 1 / ((k : ℝ)+1) by positivity))
  simpa only [raiseWeight_zero] using h

theorem powerCell_mass_sum (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (x : Configuration d n) (w : Fin n → ℝ) :
    (∑ i, μ.real (powerCell K x w i)) = μ.real K.points := by
  have h : Pairwise (fun i j => AEDisjoint μ (powerCell K x w i) (powerCell K x w j)) :=
    fun i j hij => powerCells_overlap_null K x w μ hμ hij
  have H := measure_iUnion₀ h (fun i => (isCompact_powerCell K x w i).isClosed.measurableSet.nullMeasurableSet)
  rw [powerCells_cover (Nat.pos_of_ne_zero (NeZero.ne n)),tsum_fintype] at H
  have hr := congrArg ENNReal.toReal H
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at hr
  exact hr.symm

/-- For arbitrary absolutely continuous finite mass on the prescribed body,
actual equal-mass power weights exist at every distinct-site configuration. -/
theorem exists_equalMass_powerWeights (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : Configuration d n) :
    ∃ w : Fin n → ℝ, ∀ i, μ.real (powerCell K x w i) = μ.real K.points / n := by
  obtain ⟨w,hmin⟩ := exists_potential_minimizer K μ x
  have hl (i) := mass_lower_of_potential_minimizer K μ hμ x w hmin i
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hs : (∑ _i : Fin n, μ.real K.points / n) = ∑ i, μ.real (powerCell K x w i) := by
    rw [powerCell_mass_sum K μ hμ x w]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_div_cancel₀ _ hn
  refine ⟨w,fun i => ?_⟩
  have he := Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hl j)
  exact ((he.mp hs) i (Finset.mem_univ i)).symm

/-- Positive total mass makes the equal-mass power cells genuine bodies;
all convex partition and equal-mass properties refer to the actual cells. -/
theorem exists_equalMass_powerPartition (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (mass : 0 < μ K.points)
    (x : Configuration d n) :
    ∃ w : Fin n → ℝ, ∃ positive : ∀ i, 0 < μ (powerCell K x w i),
      BodyPartition K (powerBody K x w μ hμ positive) ∧
      EqualMass μ (powerBody K x w μ hμ positive) := by
  obtain ⟨w,hw⟩ := exists_equalMass_powerWeights K μ hμ x
  have mpos : 0 < μ.real K.points / n :=
    div_pos (ENNReal.toReal_pos mass.ne' (measure_ne_top _ _))
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  have positive (i) : 0 < μ (powerCell K x w i) :=
    (ENNReal.toReal_pos_iff.mp (by rw [← hw i] at mpos; exact mpos)).1
  refine ⟨w,positive,powerBody_partition (Nat.pos_of_ne_zero (NeZero.ne n)) K x w μ hμ positive,
    fun i j => ?_⟩
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    ((hw i).trans (hw j).symm)

end NRR.PrimePower
