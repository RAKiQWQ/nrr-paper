import NRR.Statement
import NRR.PrimePowerLimit

/-!
Analytic regularization for the positive direction, with the exact domain of
characteristics in `Statement.lean`. No prime-power zero theorem is assumed or
asserted by this module.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace NRR.PrimePower

/-- Positive finite rescaling does not change the equal-mass condition. -/
theorem equalMass_smul_iff {d n : ℕ} (μ : Measure (Space d)) (S : Fin n → Body d)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    EqualMass (c • μ) S ↔ EqualMass μ S := by
  simp only [EqualMass, Measure.smul_apply, smul_eq_mul, ENNReal.mul_right_inj hc hct]

/-- Normalizing a finite positive measure changes no fair partition. -/
theorem universalFairness_smul_iff {d n : ℕ} (K : Body d) (μ : Measure (Space d))
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    UniversalFairness n K (c • μ) ↔ UniversalFairness n K μ := by
  constructor
  · intro h φ
    obtain ⟨S, hp, hm, hv⟩ := h φ
    exact ⟨S, hp, (equalMass_smul_iff μ S hc hct).mp hm, hv⟩
  · intro h φ
    obtain ⟨S, hp, hm, hv⟩ := h φ
    exact ⟨S, hp, (equalMass_smul_iff μ S hc hct).mpr hm, hv⟩

/-- A positive amount of any background measure makes that measure absolutely
continuous with respect to the sum. The original measure need not have full
support. -/
theorem background_dominated {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) {c : ℝ≥0} (hc : 0 < c) : ν ≪ μ + c • ν := by
  intro s hs
  have hcs : (c • ν) s = 0 := (add_eq_zero.mp (show μ s + (c • ν) s = 0 from hs)).2
  simpa [Measure.smul_apply, ENNReal.smul_def, hc.ne'] using hcs

/-- Existing compactness removes a positive background without changing the
number or the domain of the given characteristics. This is a reduction lemma,
not the topological existence theorem. -/
theorem universalFairness_of_positive_background {d n : ℕ} (hn : 0 < n)
    (K : Body d) (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ volume) (hν : ν ≪ volume) (hK : 0 < μ K.points)
    (fair : ∀ c : ℝ≥0, 0 < c → UniversalFairness n K (μ + c • ν)) :
    UniversalFairness n K μ := by
  intro φ
  let incl : C(Body d, CompactConvex d) :=
    ⟨Body.toCompactConvex, continuous_subtype_val.subtype_mk _⟩
  apply fairPartition_of_positive_background hn K μ ν hμ hν
    (ENNReal.toReal_pos hK.ne' (measure_ne_top _ _)) (fun k => (φ k).comp incl)
  intro c hc
  obtain ⟨S, hp, hm, hv⟩ := fair c hc φ
  exact ⟨S, hp, hm, hv⟩

/-- Ordinary volume on K is a finite background and fills all density gaps.
Consequently a full-support construction can be regularized before applying
the previous lemma. -/
theorem restricted_volume_background {d : ℕ} (K : Body d)
    (μ : Measure (Space d)) (hμ : μ ≪ volume) {c : ℝ≥0} (hc : 0 < c) :
    (μ + c • volume.restrict K.points) ≪ volume ∧
      volume.restrict K.points ≪ (μ + c • volume.restrict K.points) := by
  exact ⟨hμ.add_left (Measure.absolutelyContinuous_restrict.smul_left c),
    background_dominated μ (volume.restrict K.points) hc⟩

end NRR.PrimePower
