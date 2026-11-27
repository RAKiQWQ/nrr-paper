import NRR.ConvexLimits
import Mathlib.Analysis.Convex.Integral

/-! Strict interior centroids and a uniform height bound on compact families. -/

noncomputable section
open Set Topology Filter MeasureTheory

namespace NRR.ConvexLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem centroid_mem_interior (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (ρ : Measure E) [IsFiniteMeasure ρ] (hρ : ρ ≪ ν) (C : ConvexCompact E)
    (mass : 0 < ρ (points C)) : (⨍ q in points C, q ∂ρ) ∈ interior (points C) := by
  have aeInt : ∀ᵐ q ∂ρ.restrict (points C), q ∈ interior (points C) := by
    have hf : ∀ᵐ q ∂ρ, q ∉ frontier (points C) :=
      compl_mem_ae_iff.mpr (hρ (C.property.addHaar_frontier ν))
    filter_upwards [ae_restrict_mem C.val.isCompact.isClosed.measurableSet,
      ae_restrict_of_ae hf] with q hq hn
    by_contra h
    exact hn ⟨subset_closure hq,h⟩
  by_contra hout
  obtain ⟨F,hF⟩ := geometric_hahn_banach_open_point C.property.interior isOpen_interior hout
  have hi : IntegrableOn id (points C) ρ :=
    continuous_id.continuousOn.integrableOn_compact C.val.isCompact
  have hu : IntegrableOn F (points C) ρ :=
    F.continuous.continuousOn.integrableOn_compact C.val.isCompact
  have hnonzero : ρ.restrict (points C) ≠ 0 := by
    intro hz
    have h := congrArg (fun m : Measure E => m Set.univ) hz
    exact mass.ne' (by simpa using h)
  obtain ⟨q,hq,hge⟩ := exists_notMem_null_average_le hnonzero hu
    (ae_iff.mp aeInt : (ρ.restrict (points C)) (interior (points C))ᶜ = 0)
  apply (not_le_of_gt (hF q (not_not.mp hq)))
  convert hge using 1
  rw [average_eq, average_eq, F.map_smul]
  exact congrArg (fun z : ℝ => ((ρ.restrict (points C)).real univ)⁻¹ • z)
    (F.integral_comp_comm hi).symm

/-- No tail-volume estimate is required: compactness upgrades the strict
centroid height bound for individual positive-mass cells to a uniform bound. -/
theorem uniform_centroid_height {d : ℕ}
    (ρ : Measure (Space d × ℝ)) [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    (hz : Integrable (fun q : Space d × ℝ => q.2) ρ)
    (s : Set (ConvexCompact (Space d × ℝ))) (compact : IsCompact s)
    (mass : ∀ C ∈ s, 0 < ρ (points C))
    (strip : ∀ C ∈ s, points C ⊆ Set.univ ×ˢ Icc (-1 : ℝ) 1) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ ∀ C ∈ s, |⨍ q in points C, q.2 ∂ρ| < h := by
  let haar := (volume : Measure (Space d)).prod (volume : Measure ℝ)
  let num (C : ConvexCompact (Space d × ℝ)) := ∫ q in points C, q.2 ∂ρ
  let den (C : ConvexCompact (Space d × ℝ)) := ρ.real (points C)
  have hn : Continuous num := continuous_integral haar ρ hρ hz
  have hd : Continuous den := by
    simpa only [setIntegral_one_eq_measureReal] using
      (continuous_integral haar ρ hρ (integrable_const (1 : ℝ)))
  let f (C : ConvexCompact (Space d × ℝ)) := num C / den C
  have avg (C : ConvexCompact (Space d × ℝ)) :
      (⨍ q in points C, q.2 ∂ρ) = f C := by
    rw [setAverage_eq, smul_eq_mul]
    exact (div_eq_inv_mul _ _).symm
  have hf : ContinuousOn f s := hn.continuousOn.div hd.continuousOn (by
    intro C hC
    exact (ENNReal.toReal_pos (mass C hC).ne' (measure_ne_top _ _)).ne')
  have bound (C) (hC : C ∈ s) : |f C| < 1 := by
    have h := centroid_mem_interior haar ρ hρ C (mass C hC)
    have hs := interior_mono (strip C hC) h
    rw [interior_prod_eq, interior_univ, interior_Icc] at hs
    have hx : (⨍ q in points C, q.2 ∂ρ) = (⨍ q in points C, q ∂ρ).2 := by
      have hi : IntegrableOn id (points C) ρ :=
        continuous_id.continuousOn.integrableOn_compact C.val.isCompact
      have first : IntegrableOn (fun q : Space d × ℝ => q.1) (points C) ρ :=
        continuous_fst.continuousOn.integrableOn_compact C.val.isCompact
      have second : IntegrableOn (fun q : Space d × ℝ => q.2) (points C) ρ := hz.integrableOn
      rw [setAverage_eq, setAverage_eq, integral_pair first second]
      rfl
    rw [← avg, hx]
    exact abs_lt.mpr hs.2
  obtain ⟨m,hm,lower⟩ := compact.exists_forall_le' (continuousOn_const.sub hf.abs)
    (fun C hC => sub_pos.mpr (bound C hC))
  let t := min m 1
  have ht : 0 < t := lt_min hm zero_lt_one
  refine ⟨1-t/2, by have := min_le_right m 1; dsimp [t] at *; linarith, by linarith, ?_⟩
  intro C hC
  rw [avg]
  have hlow := lower C hC
  have htm : t ≤ m := min_le_left _ _
  linarith

end NRR.ConvexLimits
