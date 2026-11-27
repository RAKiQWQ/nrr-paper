import NRR.MomentChartModels
import NRR.UniformLayerGeometry
import NRR.ProductCounterexample

/-! A geometric layer neighborhood supplies the entire analytic counterexample.
All data in the bundle are independent of the small background weight. -/

noncomputable section
open Set Topology MeasureTheory Metric TopologicalSpace
open NRR.Coordinates NRR.MomentCoordinates NRR.InterfaceChart NRR.GlobalAssembly

namespace NRR.Localization

structure UniformLayerData {d r : ℕ} (K : ConvexBody (Space d × ℝ))
    (μ : Measure (Space d × ℝ)) (A : MomentCylinder K μ (r+2)) where
  ε : ℝ
  a : Fin (r+3) → ℝ
  b : Fin (r+3) → ℝ
  t : Fin (r+2) → ℝ
  ordered : Monotone a
  axis : ∀ i,((0 : Space d),t i) ∈ bodyPoints K
  between : ∀ i,b i.castSucc < t i ∧ t i < a i.succ
  bounds : ∀ p ∈ admissibleBox (bodyPoints K) ε (a 1) (b 1) (a 2) (b 2),
    ∀ u ∈ closedBall (0 : Space d) A.a,
      -A.h ≤ height p.val.1 u ∧ height p.val.1 u ≤ height p.val.2 u ∧
        height p.val.2 u ≤ A.h
  U : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ))
  openU : IsOpen U
  slabsInU : ∀ S ∈ equalMassPartitions (n := r+2) K μ,
    (∀ i,∃ lo hi : ℝ,lo < hi ∧ bodyPoints (S i) ∩ solidCylinder A.a A.h =
      closedBall 0 A.a ×ˢ Icc lo hi) → convexConfigurations S ∈ U
  configurations : ∀ S ∈ equalMassPartitions (n := r+2) K μ,convexConfigurations S ∈ U →
    ∃ σ : Equiv.Perm (Fin (r+2)),
      (∀ i,bodyToConvexCompact (S (σ i)) ∈ slabFamily K.val.isCompact K.property.1 ε
        (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)) ∧
      ∃ p : FeasibleParameters (bodyPoints K),
        p ∈ admissibleBox (bodyPoints K) ε (a 1) (b 1) (a 2) (b 2) ∧
        bodyToConvexCompact (S (σ 1)) = cutConvexCompact K.val.isCompact K.property.1 p ∧
        prefixCells (fun i => (S (σ i)).val) 0 = bodyPoints K ∩ belowGraph p.val.1 ∧
        prefixCells (fun i => (S (σ i)).val) 1 = bodyPoints K ∩ belowGraph p.val.2

namespace MomentCylinder

theorem counterexample_of_layerData {q r : ℕ} (hn : ¬ IsPrimePow (r+2))
    (K : ConvexBody (Space (q+2) × ℝ)) (μ : Measure (Space (q+2) × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (A : MomentCylinder K μ (r+2)) (data : UniformLayerData K μ A) :
    ∃ φ : Fin (q+2) → C(ConvexLimits.ConvexCompact (Space (q+2) × ℝ),ℝ),
      ∀ S ∈ equalMassPartitions (n := r+2) K μ,∃ k i j,
        φ k (bodyToConvexCompact (S i)) ≠ φ k (bodyToConvexCompact (S j)) := by
  have hD : (0 : Space (q+2)) ∈ interior (closedBall (0 : Space (q+2)) A.a) :=
    ball_subset_interior_closedBall (mem_ball_self A.radius_pos)
  have inner : closedBall (0 : Space (q+2)) A.a ×ˢ Icc (-A.h) A.h ⊆ bodyPoints K :=
    A.inner.trans interior_subset
  apply counterexample_of_uniform_charts hn K μ hμ hK A data.U data.openU data.slabsInU
  intro δ hδ
  refine ⟨layerChart K.val.isCompact K.property.1 data.ε data.a data.b data.t
    data.ordered data.axis data.between hD inner data.bounds (A.capProfile δ),?_⟩
  intro S hS hSU
  obtain ⟨σ,members,p,hp,special,lower,upper⟩ := data.configurations S hS hSU
  have part := NRR.HorizontalExtension.convexPartition_reindex (convexPartition_of_partition hS.1) σ
  have readings := A.capProfile_readings hδ.le
    (fun i => bodyToConvexCompact (S (σ i))) part p.val.1 p.val.2 lower upper
  exact layerChart_models K.val.isCompact K.property.1 data.ε data.a data.b data.t
    data.ordered data.axis data.between hD inner data.bounds (A.capProfile δ)
    productPartitionCell (complexMoment (A.moment δ)) S σ members p hp special
    readings.1 readings.2
    (balanced_complex (A.moment δ) (fun i => bodyToConvexCompact (S i)) (A.balanced δ S hS.1))

end MomentCylinder
end NRR.Localization
