import NRR.NormalizedLocalization
import NRR.MomentCoordinates

/-! A single honest positive measure represents the weighted moment.
This lets the interface chart read ordinary prefix-cap integrals. -/

noncomputable section
open Set Topology MeasureTheory Metric
open NRR.Coordinates NRR.MomentCoordinates

namespace NRR.Localization.MomentCylinder

variable {d n : ℕ} {K : ConvexBody (Space d × ℝ)} {μ : Measure (Space d × ℝ)}
    (A : MomentCylinder K μ n)

def measure (δ : ℝ) : Measure (Space d × ℝ) :=
  volume.restrict (solidCylinder A.a A.h) + ENNReal.ofReal δ • A.ρ

theorem measure_ac (δ : ℝ) : A.measure δ ≪ volume :=
  Measure.absolutelyContinuous_restrict.add_left (A.ac.smul_left _)

theorem measure_support (δ : ℝ) : A.measure δ (bodyPoints K)ᶜ = 0 := by
  have empty : (bodyPoints K)ᶜ ∩ solidCylinder A.a A.h = ∅ :=
    disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right
      (A.inner.trans interior_subset))
  rw [measure,Measure.add_apply,Measure.smul_apply,A.support,
    Measure.restrict_apply K.val.isCompact.isClosed.measurableSet.compl,empty]
  simp

theorem measure_ae_mem (δ : ℝ) : ∀ᵐ x ∂A.measure δ,x ∈ bodyPoints K :=
  ae_iff.mpr (A.measure_support δ)

theorem measure_finite (δ : ℝ) : IsFiniteMeasure (A.measure δ) := by
  letI := A.finite
  letI : IsFiniteMeasure (volume.restrict (solidCylinder (d := d) A.a A.h)) :=
    ⟨by simpa using (isCompact_solidCylinder (d := d) A.a A.h).measure_lt_top⟩
  letI : IsFiniteMeasure (ENNReal.ofReal δ • A.ρ) := A.ρ.smul_finite (by simp)
  change IsFiniteMeasure (volume.restrict (solidCylinder (d := d) A.a A.h) + ENNReal.ofReal δ • A.ρ)
  infer_instance

theorem integrable_fst_measure (δ : ℝ) :
    Integrable (fun q : Space d × ℝ => q.1) (A.measure δ) := by
  have h₀ : IntegrableOn (fun q : Space d × ℝ => q.1) (solidCylinder A.a A.h) volume :=
    continuous_fst.continuousOn.integrableOn_compact (isCompact_solidCylinder A.a A.h)
  have h₁ := (ContinuousLinearMap.fst ℝ (Space d) ℝ).integrable_comp A.first
  exact Integrable.add_measure h₀ (h₁.smul_measure (by simp : ENNReal.ofReal δ ≠ ⊤))

theorem moment_eq_integral {δ : ℝ} (hδ : 0 ≤ δ)
    (C : ConvexLimits.ConvexCompact (Space d × ℝ)) :
    A.moment δ C = ∫ q in ConvexLimits.points C, q.1 ∂A.measure δ := by
  have h₀ : IntegrableOn (fun q : Space d × ℝ => q.1) (solidCylinder A.a A.h) volume :=
    continuous_fst.continuousOn.integrableOn_compact (isCompact_solidCylinder A.a A.h)
  have h₁ := (ContinuousLinearMap.fst ℝ (Space d) ℝ).integrable_comp A.first
  have h₀C : IntegrableOn (fun q : Space d × ℝ => q.1) (ConvexLimits.points C)
      (volume.restrict (solidCylinder A.a A.h)) := h₀.integrableOn
  have h₁C : IntegrableOn (fun q : Space d × ℝ => q.1) (ConvexLimits.points C)
      (ENNReal.ofReal δ • A.ρ) :=
    (h₁.smul_measure (by simp : ENNReal.ofReal δ ≠ ⊤)).integrableOn
  change (∫ q in ConvexLimits.points C ∩ solidCylinder A.a A.h, q.1 ∂volume) +
      δ • (∫ q in ConvexLimits.points C, q.1 ∂A.ρ) = _
  rw [measure,Measure.restrict_add,integral_add_measure h₀C h₁C,
    Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal hδ,
    Measure.restrict_restrict C.val.isCompact.isClosed.measurableSet]

variable {q : ℕ} {K' : ConvexBody (Space (q+2) × ℝ)}
    {μ' : Measure (Space (q+2) × ℝ)} (B : MomentCylinder K' μ' n)

theorem integrable_complex_measure (δ : ℝ) :
    Integrable (fun x : Space (q+2) × ℝ => complexProjection q x.1) (B.measure δ) :=
  (complexProjection q).integrable_comp (B.integrable_fst_measure δ)

theorem complexMoment_eq_integral {δ : ℝ} (hδ : 0 ≤ δ)
    (C : ConvexLimits.ConvexCompact (Space (q+2) × ℝ)) :
    complexMoment (B.moment δ) C =
      ∫ x in ConvexLimits.points C, complexProjection q x.1 ∂B.measure δ := by
  change complexProjection q (B.moment δ C) = _
  rw [B.moment_eq_integral hδ C]
  exact ((complexProjection q).integral_comp_comm (B.integrable_fst_measure δ).integrableOn).symm

end NRR.Localization.MomentCylinder
