import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Algebraic readout for the two active interfaces of adjacent cube layers.

`cubeFourMoments` is a model with interface parameters as inputs; it does not
identify those parameters with integrals of an arbitrary convex body. -/

noncomputable section

namespace NRR.CubeFourMomentReadout

/-- A horizontal vector in the active coordinate plane. -/
abbrev Plane := ℝ × ℝ

/-- The four normalized moments of the two-plane slab model. `lower` and
`upper` are the horizontal interface parameters `p_{i-1}` and `p_i`; `top`
is `t_i`, and `thickness` is `m`. -/
def cubeFourMoments (thickness top : ℝ) (lower upper : Plane) : Plane × Plane :=
  let w := upper - lower
  let center := top - thickness / 2
  (w,
    (center + 3 * thickness * (lower.1 * w.1 + lower.2 * w.2 +
          (w.1 ^ 2 + w.2 ^ 2) / 2) + thickness * lower.1 + top * w.1,
      thickness * lower.2 + top * w.2))

/-- Global two-moment inverse. The `max` keeps its first denominator positive
even on inputs far outside the small-slope region. -/
def lowerReadout (thickness top : ℝ) (input : Plane × Plane) : Plane :=
  let w := input.1
  let v := input.2
  let lower₂ := (v.2 - top * w.2) / thickness
  let center := top - thickness / 2
  let numerator := v.1 - top * w.1 - center -
    3 * thickness * lower₂ * w.2 -
    (3 * thickness / 2) * (w.1 ^ 2 + w.2 ^ 2)
  (numerator / max (thickness / 2) (thickness * (1 + 3 * w.1)), lower₂)

theorem continuous_lowerReadout (thickness top : ℝ) (hm : 0 < thickness) :
    Continuous (lowerReadout thickness top) := by
  have hm0 : thickness ≠ 0 := ne_of_gt hm
  have hden (x : Plane × Plane) :
      max (thickness / 2) (thickness * (1 + 3 * x.1.1)) ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  unfold lowerReadout
  fun_prop (disch := aesop)

theorem continuous_lowerReadout_at (thickness top : ℝ) (hm : 0 < thickness)
    (input : Plane × Plane) :
    ContinuousAt (lowerReadout thickness top) input :=
  (continuous_lowerReadout thickness top hm).continuousAt

theorem lowerReadout_model (thickness top : ℝ) (lower upper : Plane)
    (hm : 0 < thickness)
    (hslope : (upper.1 - lower.1) > -(1 / 6 : ℝ)) :
    lowerReadout thickness top (cubeFourMoments thickness top lower upper) = lower := by
  dsimp [lowerReadout, cubeFourMoments]
  have hden : max (thickness / 2)
      (thickness * (1 + 3 * (upper.1 - lower.1))) =
      thickness * (1 + 3 * (upper.1 - lower.1)) := by
    apply max_eq_right
    nlinarith
  have hdenpos : thickness * (1 + 3 * (upper.1 - lower.1)) ≠ 0 := by
    apply ne_of_gt
    nlinarith
  apply Prod.ext
  · rw [hden]
    apply (div_eq_iff hdenpos).2
    field_simp [hm.ne']
    ring
  · field_simp [hm.ne']
    ring

theorem upperReadout_model (thickness top : ℝ) (lower upper : Plane)
    (hm : 0 < thickness)
    (hslope : (upper.1 - lower.1) > -(1 / 6 : ℝ)) :
    lowerReadout thickness top (cubeFourMoments thickness top lower upper) +
        (cubeFourMoments thickness top lower upper).1 = upper := by
  rw [lowerReadout_model thickness top lower upper hm hslope]
  dsimp [cubeFourMoments]
  simp

/-- Continuous layer selector: one within `m/8` of a center, and zero from
distance `m/4` onward. -/
def layerWindow (thickness center : ℝ) : C(ℝ, ℝ) :=
  ⟨fun v => max 0 (min 1 (2 - 8 * |v - center| / thickness)), by fun_prop⟩

theorem layerWindow_eq_one (thickness center v : ℝ) (hm : 0 < thickness)
    (hnear : |v - center| ≤ thickness / 8) :
    layerWindow thickness center v = 1 := by
  simp only [layerWindow, ContinuousMap.coe_mk]
  have hfrac : 8 * |v - center| / thickness ≤ 1 :=
    (div_le_iff₀ hm).2 (by nlinarith)
  have h : 1 ≤ 2 - 8 * |v - center| / thickness := by linarith
  rw [min_eq_left h]
  simp

theorem layerWindow_eq_zero (thickness center v : ℝ) (hm : 0 < thickness)
    (hfar : thickness / 4 ≤ |v - center|) :
    layerWindow thickness center v = 0 := by
  simp only [layerWindow, ContinuousMap.coe_mk]
  have hfrac : 2 ≤ 8 * |v - center| / thickness :=
    (le_div_iff₀ hm).2 (by nlinarith)
  have h : 2 - 8 * |v - center| / thickness ≤ 0 := by linarith
  rw [min_eq_right (le_trans h (by norm_num))]
  rw [max_eq_left h]

/-- Distinct horizontal layer centers are separated enough for their windows
to have disjoint positive loci. -/
theorem layerWindows_disjoint (thickness : ℝ) (hm : 0 < thickness)
    {c d v : ℝ} (hsep : thickness ≤ |c - d|)
    (hc : 0 < layerWindow thickness c v) :
    layerWindow thickness d v = 0 := by
  apply layerWindow_eq_zero thickness d v hm
  have hcv : |v - c| < thickness / 4 := by
    by_contra h
    have h' : thickness / 4 ≤ |v - c| := le_of_not_gt h
    rw [layerWindow_eq_zero thickness c v hm h'] at hc
    norm_num at hc
  have htriangle : |c - d| ≤ |c - v| + |v - d| := by
    exact abs_sub_le c v d
  rw [abs_sub_comm c v] at htriangle
  by_contra hfar
  have hnear : |v - d| < thickness / 4 := lt_of_not_ge hfar
  linarith

/-- The readout is exact on every modeled layer whose first moment has small
horizontal slope. The cutoff can be applied independently to identify its
layer index from `V₁`. -/
theorem windowed_lowerReadout_model (thickness top center : ℝ)
    (lower upper : Plane) (hm : 0 < thickness)
    (hslope : (upper.1 - lower.1) > -(1 / 6 : ℝ))
    (hwindow : |(cubeFourMoments thickness top lower upper).2.1 - center| ≤
      thickness / 8) :
    layerWindow thickness center
        (cubeFourMoments thickness top lower upper).2.1 •
      lowerReadout thickness top (cubeFourMoments thickness top lower upper) = lower := by
  rw [layerWindow_eq_one thickness center _ hm hwindow, one_smul,
    lowerReadout_model thickness top lower upper hm hslope]

/-- In the slab model, `V₁` differs from the horizontal layer center by an
explicit quadratic error when both interface parameters are horizontally
small. -/
theorem model_V1_center_bound (thickness top δ : ℝ) (lower upper : Plane)
    (hm : 0 < thickness) (hδ : 0 ≤ δ)
    (hl₁ : |lower.1| ≤ δ) (hl₂ : |lower.2| ≤ δ)
    (hu₁ : |upper.1| ≤ δ) (hu₂ : |upper.2| ≤ δ) :
    |(cubeFourMoments thickness top lower upper).2.1 -
      (top - thickness / 2)| ≤ thickness * δ + 2 * |top| * δ +
        24 * thickness * δ ^ 2 := by
  have hw₁ : |upper.1 - lower.1| ≤ 2 * δ := by
    calc
      |upper.1 - lower.1| ≤ |upper.1| + |lower.1| := by
        simpa using (abs_sub_le upper.1 0 lower.1)
      _ ≤ 2 * δ := by linarith
  have hw₂ : |upper.2 - lower.2| ≤ 2 * δ := by
    calc
      |upper.2 - lower.2| ≤ |upper.2| + |lower.2| := by
        simpa using (abs_sub_le upper.2 0 lower.2)
      _ ≤ 2 * δ := by linarith
  have hcross :
      |lower.1 * (upper.1 - lower.1) + lower.2 * (upper.2 - lower.2)| ≤
        4 * δ ^ 2 := by
    calc
      _ ≤ |lower.1 * (upper.1 - lower.1)| +
          |lower.2 * (upper.2 - lower.2)| := abs_add_le _ _
      _ = |lower.1| * |upper.1 - lower.1| +
          |lower.2| * |upper.2 - lower.2| := by rw [abs_mul, abs_mul]
      _ ≤ δ * (2 * δ) + δ * (2 * δ) := by
        gcongr
      _ = 4 * δ ^ 2 := by ring
  have hsquare :
      |(upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2| ≤
        8 * δ ^ 2 := by
    have hw₁sq : |upper.1 - lower.1| ^ 2 ≤ (2 * δ) ^ 2 := by
      rw [pow_two, pow_two]
      calc
        _ ≤ |upper.1 - lower.1| * (2 * δ) :=
          mul_le_mul_of_nonneg_left hw₁ (abs_nonneg _)
        _ ≤ (2 * δ) * (2 * δ) :=
          mul_le_mul_of_nonneg_right hw₁ (by positivity)
    have hw₂sq : |upper.2 - lower.2| ^ 2 ≤ (2 * δ) ^ 2 := by
      rw [pow_two, pow_two]
      calc
        _ ≤ |upper.2 - lower.2| * (2 * δ) :=
          mul_le_mul_of_nonneg_left hw₂ (abs_nonneg _)
        _ ≤ (2 * δ) * (2 * δ) :=
          mul_le_mul_of_nonneg_right hw₂ (by positivity)
    calc
      _ ≤ |(upper.1 - lower.1) ^ 2| + |(upper.2 - lower.2) ^ 2| := abs_add_le _ _
      _ = _ := by rw [abs_pow, abs_pow]
      _ ≤ 8 * δ ^ 2 := by nlinarith [hw₁sq, hw₂sq]
  have hhalf :
      |((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2| ≤
        4 * δ ^ 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hsquare]
  have hinner :
      |lower.1 * (upper.1 - lower.1) + lower.2 * (upper.2 - lower.2) +
          ((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2| ≤
        8 * δ ^ 2 := by
    calc
      _ ≤ |lower.1 * (upper.1 - lower.1) +
          lower.2 * (upper.2 - lower.2)| +
          |((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2| :=
            abs_add_le _ _
      _ ≤ 8 * δ ^ 2 := by nlinarith [hcross, hhalf]
  have hformula :
      (cubeFourMoments thickness top lower upper).2.1 - (top - thickness / 2) =
        thickness * lower.1 + top * (upper.1 - lower.1) +
          3 * thickness * (lower.1 * (upper.1 - lower.1) +
            lower.2 * (upper.2 - lower.2) +
            ((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2) := by
    dsimp [cubeFourMoments]
    ring
  rw [hformula]
  calc
    _ ≤ |thickness * lower.1| + |top * (upper.1 - lower.1)| +
        |3 * thickness * (lower.1 * (upper.1 - lower.1) +
          lower.2 * (upper.2 - lower.2) +
          ((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2)| := by
      calc
        _ ≤ |thickness * lower.1 + top * (upper.1 - lower.1)| +
            |3 * thickness * (lower.1 * (upper.1 - lower.1) +
              lower.2 * (upper.2 - lower.2) +
              ((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2)| := abs_add_le _ _
        _ ≤ _ := by
          gcongr
          exact abs_add_le _ _
    _ ≤ thickness * δ + 2 * |top| * δ + 24 * thickness * δ ^ 2 := by
      simp only [abs_mul, abs_of_pos hm, abs_of_pos (by norm_num : 0 < (3 : ℝ))]
      have hA : thickness * |lower.1| ≤ thickness * δ :=
        mul_le_mul_of_nonneg_left hl₁ hm.le
      have hB : |top| * |upper.1 - lower.1| ≤ |top| * (2 * δ) :=
        mul_le_mul_of_nonneg_left hw₁ (abs_nonneg top)
      have hC : 3 * thickness * |lower.1 * (upper.1 - lower.1) +
          lower.2 * (upper.2 - lower.2) +
          ((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2| ≤
          24 * thickness * δ ^ 2 := by
        calc
          _ = (3 * thickness) * |lower.1 * (upper.1 - lower.1) +
              lower.2 * (upper.2 - lower.2) +
              ((upper.1 - lower.1) ^ 2 + (upper.2 - lower.2) ^ 2) / 2| := by ring
          _ ≤ (3 * thickness) * (8 * δ ^ 2) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
          _ = 24 * thickness * δ ^ 2 := by ring
      nlinarith [hA, hB, hC]

/-- A concrete horizontal neighborhood gives the exact lower-interface readout.
The smallness condition on `δ` also places the first moment in the region
where the positive max truncation agrees with its untruncated denominator. -/
theorem horizontal_neighborhood_readout (thickness top δ : ℝ)
    (lower upper : Plane) (hm : 0 < thickness) (hδ : 0 ≤ δ)
    (hδsmall : δ < 1 / 12)
    (hl₁ : |lower.1| ≤ δ) (hl₂ : |lower.2| ≤ δ)
    (hu₁ : |upper.1| ≤ δ) (hu₂ : |upper.2| ≤ δ)
    (hindex : thickness * δ + 2 * |top| * δ +
      24 * thickness * δ ^ 2 ≤ thickness / 8) :
    layerWindow thickness (top - thickness / 2)
        (cubeFourMoments thickness top lower upper).2.1 •
      lowerReadout thickness top (cubeFourMoments thickness top lower upper) = lower := by
  have hw₁ : |upper.1 - lower.1| ≤ 2 * δ := by
    calc
      |upper.1 - lower.1| ≤ |upper.1| + |lower.1| := by
        simpa using (abs_sub_le upper.1 0 lower.1)
      _ ≤ 2 * δ := by linarith
  have hslope : (upper.1 - lower.1) > -(1 / 6 : ℝ) := by
    have := neg_le_abs (upper.1 - lower.1)
    linarith
  apply windowed_lowerReadout_model thickness top (top - thickness / 2)
    lower upper hm hslope
  exact (model_V1_center_bound thickness top δ lower upper hm hδ hl₁ hl₂ hu₁ hu₂).trans hindex

end NRR.CubeFourMomentReadout
