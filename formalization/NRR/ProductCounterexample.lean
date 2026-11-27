import NRR.NormalizedLocalization
import NRR.MomentCoordinates

/-! Assembly on product-coordinate bodies, using the actual balanced
moments and the full prescribed equal-mass partition space. -/

noncomputable section
open Set Topology MeasureTheory Metric
open NRR.Coordinates NRR.MomentCoordinates NRR.GlobalAssembly

namespace NRR.Localization

local instance productVolumeHaarForAssembly {d : ℕ} :
    Measure.IsAddHaarMeasure (volume : Measure (Space d × ℝ)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure (Space d)).prod (volume : Measure ℝ))
  infer_instance

def productPartitionCell {d n : ℕ} (i : Fin n) :
    C((Fin n → ConvexBody (Space d × ℝ)),ConvexLimits.ConvexCompact (Space d × ℝ)) :=
  ⟨fun S => bodyToConvexCompact (S i),
    continuous_bodyToConvexCompact.comp (continuous_apply i)⟩

/-- The actual vector moment supplies all balance and scalarization data.
Only the single-cell geometric chart is left as a geometric input here. -/
theorem counterexample_of_moment_chart {q r : ℕ} (hn : ¬ IsPrimePow (r+2))
    (K : ConvexBody (Space (q+2) × ℝ)) (μ : Measure (Space (q+2) × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (A : MomentCylinder K μ (r+2)) (δ : ℝ)
    (U : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space (q+2) × ℝ))) (hU : IsOpen U)
    (localized : ∀ S ∈ equalMassPartitions (n := r+2) K μ,
      (∀ i,A.moment δ (bodyToConvexCompact (S i)) = 0) → convexConfigurations S ∈ U)
    (chart : TwoInterfaceChart (r+1) (ConvexLimits.ConvexCompact (Space (q+2) × ℝ)))
    (models : ∀ S ∈ equalMassPartitions (n := r+2) K μ,convexConfigurations S ∈ U →
      chart.Models productPartitionCell (complexMoment (A.moment δ)) S) :
    ∃ φ : Fin (q+2) → C(ConvexLimits.ConvexCompact (Space (q+2) × ℝ),ℝ),
      ∀ S ∈ equalMassPartitions (n := r+2) K μ,∃ k i j,
        φ k (bodyToConvexCompact (S i)) ≠ φ k (bodyToConvexCompact (S j)) := by
  let s := equalMassPartitions (n := r+2) K μ
  let V := convexConfigurations ⁻¹' U
  have hs : IsCompact s :=
    Coordinates.compact_equalMassPartitions (horizontalHeight (q+2)) K μ hμ hK
  have hv : IsOpen V := hU.preimage continuous_convexConfigurations
  have bw : ∀ S ∈ s,∑ i,complexMoment (A.moment δ) (productPartitionCell i S) = 0 := by
    intro S hS
    exact balanced_complex (A.moment δ) (fun i => bodyToConvexCompact (S i))
      (A.balanced δ S hS.1)
  have bv : ∀ S ∈ s,∑ i,remainingMoment (A.moment δ) (productPartitionCell i S) = 0 := by
    intro S hS
    exact balanced_remaining (A.moment δ) (fun i => bodyToConvexCompact (S i))
      (A.balanced δ S hS.1)
  have loc : ∀ S ∈ s,
      (∀ i,complexMoment (A.moment δ) (productPartitionCell i S) = 0 ∧
        remainingMoment (A.moment δ) (productPartitionCell i S) = 0) → S ∈ V := by
    intro S hS zero
    exact localized S hS (fun i => (moment_zero_iff _ _).mpr (zero i))
  exact real_counterexample_of_chart hn productPartitionCell
    (complexMoment (A.moment δ)) (remainingMoment (A.moment δ)) s V hs hv bw bv loc
    chart models

/-- Uniform geometric charts around the horizontal partitions now imply
an unconditional analytic counterexample on the prescribed normalized body.
The tail weight is chosen by the proved compact localization theorem. -/
theorem counterexample_of_uniform_charts {q r : ℕ} (hn : ¬ IsPrimePow (r+2))
    (K : ConvexBody (Space (q+2) × ℝ)) (μ : Measure (Space (q+2) × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (A : MomentCylinder K μ (r+2))
    (U : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space (q+2) × ℝ))) (hU : IsOpen U)
    (slabsInU : ∀ S ∈ equalMassPartitions (n := r+2) K μ,
      (∀ i, ∃ lo hi : ℝ, lo < hi ∧ bodyPoints (S i) ∩ solidCylinder A.a A.h =
        closedBall 0 A.a ×ˢ Icc lo hi) → convexConfigurations S ∈ U)
    (charts : ∀ δ : ℝ,0 < δ →
      ∃ chart : TwoInterfaceChart (r+1) (ConvexLimits.ConvexCompact (Space (q+2) × ℝ)),
        ∀ S ∈ equalMassPartitions (n := r+2) K μ,convexConfigurations S ∈ U →
          chart.Models productPartitionCell (complexMoment (A.moment δ)) S) :
    ∃ φ : Fin (q+2) → C(ConvexLimits.ConvexCompact (Space (q+2) × ℝ),ℝ),
      ∀ S ∈ equalMassPartitions (n := r+2) K μ,∃ k i j,
        φ k (bodyToConvexCompact (S i)) ≠ φ k (bodyToConvexCompact (S j)) := by
  obtain ⟨δ₀,hδ₀,loc⟩ := A.localizes hμ hK U hU slabsInU
  have hp : 0 < δ₀/2 := by positivity
  obtain ⟨chart,models⟩ := charts (δ₀/2) hp
  exact counterexample_of_moment_chart hn K μ hμ hK A (δ₀/2) U hU
    (loc (δ₀/2) hp (by linarith)) chart models

/-- The assembly changes only the complex coordinate.  Its remaining
coordinates are exactly the original additive moments on every compact
convex set, not merely on the partition space. -/
theorem counterexample_of_moment_chart_with_tail {q r : ℕ} (hn : ¬ IsPrimePow (r+2))
    (K : ConvexBody (Space (q+2) × ℝ)) (μ : Measure (Space (q+2) × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (A : MomentCylinder K μ (r+2)) (δ : ℝ)
    (U : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space (q+2) × ℝ))) (hU : IsOpen U)
    (localized : ∀ S ∈ equalMassPartitions (n := r+2) K μ,
      (∀ i,A.moment δ (bodyToConvexCompact (S i)) = 0) → convexConfigurations S ∈ U)
    (chart : TwoInterfaceChart (r+1) (ConvexLimits.ConvexCompact (Space (q+2) × ℝ)))
    (models : ∀ S ∈ equalMassPartitions (n := r+2) K μ,convexConfigurations S ∈ U →
      chart.Models productPartitionCell (complexMoment (A.moment δ)) S) :
    ∃ G : C(ConvexLimits.ConvexCompact (Space (q+2) × ℝ),ℂ × Space q),
      (∀ C, (G C).2 = remainingMoment (A.moment δ) C) ∧
      ∀ S ∈ equalMassPartitions (n := r+2) K μ,∃ i j,
        G (bodyToConvexCompact (S i)) ≠ G (bodyToConvexCompact (S j)) := by
  let s := equalMassPartitions (n := r+2) K μ
  let V := convexConfigurations ⁻¹' U
  let w := complexMoment (A.moment δ)
  let v := remainingMoment (A.moment δ)
  have hs : IsCompact s :=
    Coordinates.compact_equalMassPartitions (horizontalHeight (q+2)) K μ hμ hK
  have hv : IsOpen V := hU.preimage continuous_convexConfigurations
  have bw : ∀ S ∈ s, ∑ i,w (productPartitionCell i S) = 0 := by
    intro S hS
    exact balanced_complex (A.moment δ) (fun i => bodyToConvexCompact (S i))
      (A.balanced δ S hS.1)
  have bv : ∀ S ∈ s, ∑ i,v (productPartitionCell i S) = 0 := by
    intro S hS
    exact balanced_remaining (A.moment δ) (fun i => bodyToConvexCompact (S i))
      (A.balanced δ S hS.1)
  obtain ⟨h,hzero,_,hh,avoid,M,D,hM,hD,havoid⟩ := LocalModel.exists_planar_correction r hn
  let f := baseTest h w v
  have outside : ∀ S ∈ s \ V, ∃ i j,f (productPartitionCell i S) ≠ f (productPartitionCell j S) := by
    intro S hS
    by_contra! fair
    have zero := fair_base_forces_zero h hzero avoid w v
      (fun i => productPartitionCell i S) (bw S hS.1) (bv S hS.1) fair
    exact hS.2 (localized S hS.1 (fun i => (moment_zero_iff _ _).mpr (zero i)))
  obtain ⟨ε,hε,reject⟩ := Stability.uniform_rejection productPartitionCell f (s \ V)
    (hs.diff hv) outside
  obtain ⟨σ,hσ,hsmall⟩ := exists_small_quadratic
    (TwoInterfaceChart.bound_pos (m := r+1) hM) hε
  obtain ⟨E,hE,fix⟩ := chart.exists_global_patch hσ D hM hD
  let G := perturbFirst f E
  refine ⟨G,fun _ => rfl,fun S hS => ?_⟩
  by_cases hin : S ∈ V
  · obtain ⟨i,j,hij⟩ := chart.rejects_model productPartitionCell w h hh D havoid hσ E fix S
      (bw S hS) (models S hS hin)
    exact ⟨i,j,fun he => hij (congrArg Prod.fst he)⟩
  · exact reject G (fun C => by rw [perturbFirst_dist]; exact (hE C).trans hsmall) S ⟨hS,hin⟩

end NRR.Localization
