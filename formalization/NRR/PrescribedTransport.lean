import NRR.BodyNormalization
import NRR.ProductPartitions

/-! Transport of the full prescribed counterexample statement from normalized
horizontal-height coordinates.  The original measure is pushed forward and
the actual continuous single-block characteristics are pulled back. -/

noncomputable section
open Set Topology MeasureTheory
open NRR.Coordinates

namespace NRR

local instance productVolumeHaarForTransport {d : ℕ} :
    Measure.IsAddHaarMeasure (volume : Measure (Space d × ℝ)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure (Space d)).prod (volume : Measure ℝ))
  infer_instance

/-- Once counterexamples have been constructed for the normalized product
bodies, no further geometry or measure restriction is needed to obtain the
original pointwise prescribed-body and prescribed-measure conclusion. -/
theorem prescribedCounterexamples_of_normalized
    (normalized : ∀ (q r : ℕ),¬ IsPrimePow (r+2) →
      ∀ (K : ConvexBody (Space (q+2) × ℝ)) (μ : Measure (Space (q+2) × ℝ)),
        IsProbabilityMeasure μ → μ ≪ volume → μ (bodyPoints K) = 1 →
        bodyPoints K ⊆ univ ×ˢ Icc (-1 : ℝ) 1 →
        (∀ z : ℝ,|z| < 1 → ((0 : Space (q+2)),z) ∈ interior (bodyPoints K)) →
        ∃ φ : Fin (q+2) → C(ConvexLimits.ConvexCompact (Space (q+2) × ℝ),ℝ),
          ∀ S ∈ equalMassPartitions (n := r+2) K μ,∃ k i j,
            φ k (bodyToConvexCompact (S i)) ≠ φ k (bodyToConvexCompact (S j))) :
    PrescribedCounterexamples := by
  intro d n hd hn hnp K μ hpr hac hs
  obtain ⟨q,rfl⟩ : ∃ q : ℕ,d = q+3 := ⟨d-3,by omega⟩
  obtain ⟨r,rfl⟩ : ∃ r : ℕ,n = r+2 := ⟨n-2,by omega⟩
  letI : IsProbabilityMeasure μ := hpr
  obtain ⟨e,strip₀,axis₀⟩ := BodyNormalization.exists_normalized_coordinates K
  let K' := Coordinates.Affine.bodiesHomeomorph e K
  let μ' := μ.map e
  have hpr' : IsProbabilityMeasure μ' := Coordinates.Affine.map_isProbabilityMeasure e μ
  have hac' : μ' ≪ volume :=
    Coordinates.Affine.map_absolutelyContinuous_haar e μ volume volume hac
  have hs' : μ' (bodyPoints K') = 1 := by
    change (μ.map e) (bodyPoints (Coordinates.Affine.bodiesHomeomorph e K)) = 1
    rwa [Coordinates.Affine.map_body_mass]
  have strip : bodyPoints K' ⊆ univ ×ˢ Icc (-1 : ℝ) 1 :=
    fun x hx => ⟨mem_univ _,abs_le.mp (strip₀ x hx)⟩
  have axis : ∀ z : ℝ,|z| < 1 → ((0 : Space (q+2)),z) ∈ interior (bodyPoints K') :=
    fun z hz => axis₀ z (abs_lt.mp hz).1 (abs_lt.mp hz).2
  obtain ⟨φ,reject⟩ := normalized q r hnp K' μ' hpr' hac' hs' strip axis
  obtain ⟨ψ,hψ⟩ := Coordinates.Affine.body_counterexample_pullback e K μ φ
    (fun S hp hm => reject S ⟨hp,hm⟩)
  have hdim : q+3-1 = q+2 := by omega
  refine ⟨fun k => ψ (Fin.cast hdim k),fun S hp hm => ?_⟩
  obtain ⟨k,i,j,hij⟩ := hψ S hp hm
  refine ⟨Fin.cast hdim.symm k,i,j,?_⟩
  simpa only [Fin.cast_cast,Fin.cast_eq_self] using hij

end NRR
