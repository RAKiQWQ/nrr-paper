import NRR.LayerChartModels
import NRR.MomentMeasure

/-! Actual weighted moments supply the two prefix readings of a slab chart. -/

noncomputable section
open Set Topology MeasureTheory Metric TopologicalSpace
open NRR.Coordinates NRR.MomentCoordinates NRR.InterfaceChart

namespace NRR.Localization.MomentCylinder

variable {q r : ℕ} {K : ConvexBody (Space (q+2) × ℝ)}
    {μ : Measure (Space (q+2) × ℝ)} (A : MomentCylinder K μ (r+2))

def capProfile (δ : ℝ) : C(Parameters (q+2),ℂ) :=
  ⟨prefixMoment (A.measure δ) (fun x => complexProjection q x.1),
    continuous_prefixMoment (A.measure δ) (A.measure_ac δ) (A.integrable_complex_measure δ)⟩

/-- The bottom cell and the union of the bottom two cells read exactly the
two affine interfaces. The background measure is the same honest positive
measure used to define the global moment. -/
theorem capProfile_readings {δ : ℝ} (hδ : 0 ≤ δ)
    (S : Fin (r+2) → ConvexLimits.ConvexCompact (Space (q+2) × ℝ))
    (part : ConvexPartition (bodyPoints K) (fun i => (S i).val))
    (p₀ p₁ : Parameters (q+2))
    (lower : prefixCells (fun i => (S i).val) 0 = bodyPoints K ∩ belowGraph p₀)
    (upper : prefixCells (fun i => (S i).val) 1 = bodyPoints K ∩ belowGraph p₁) :
    A.capProfile δ p₀ = complexMoment (A.moment δ) (S 0) ∧
      A.capProfile δ p₁ = complexMoment (A.moment δ) (S 0) +
        complexMoment (A.moment δ) (S 1) := by
  constructor
  · change prefixMoment (A.measure δ) (fun x => complexProjection q x.1) p₀ = _
    rw [prefixMoment_eq_integral_of_cap (A.measure δ) _ (bodyPoints K)
      (A.measure_ae_mem δ) (fun i => (S i).val) 0 p₀ lower,prefixCells_zero,
      A.complexMoment_eq_integral hδ]
  · change prefixMoment (A.measure δ) (fun x => complexProjection q x.1) p₁ = _
    rw [prefixMoment_eq_integral_of_cap (A.measure δ) _ (bodyPoints K)
      (A.measure_ae_mem δ) (fun i => (S i).val) 1 p₁ upper,
      integral_prefix_one (A.measure δ) (A.measure_ac δ) (fun i => (S i).val)
        part.cellConvex part.disjoint _ (A.integrable_complex_measure δ),
      A.complexMoment_eq_integral hδ,A.complexMoment_eq_integral hδ]

end NRR.Localization.MomentCylinder
