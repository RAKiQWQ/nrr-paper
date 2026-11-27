import NRR.LayerWindows
import NRR.ProductPartitions

/-! The common affine neighborhood for the actual prescribed equal-mass
partition space. Its mass-window condition follows from prefix additivity. -/

noncomputable section
open Set Topology Filter Metric TopologicalSpace MeasureTheory
open NRR.Coordinates

namespace NRR.InterfaceChart

local instance productVolumeHaar {d : ℕ} :
    Measure.IsAddHaarMeasure (volume : Measure (Space d × ℝ)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure (Space d)).prod (volume : Measure ℝ))
  infer_instance

theorem convexPartition_of_partition {d n : ℕ} {K : ConvexBody (Space d × ℝ)}
    {S : Fin n → ConvexBody (Space d × ℝ)} (part : Partition K S) :
    ConvexPartition (bodyPoints K) (fun i => (S i).val) :=
  ⟨K.property.1,fun i => (S i).property.1,fun i => (S i).property.2,
    part.covers,part.disjoint⟩

theorem equalMass_prefix_quantiles {d r : ℕ}
    (K : ConvexBody (Space d × ℝ)) (μ : Measure (Space d × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (S : Fin (r+2) → ConvexBody (Space d × ℝ))
    (hS : S ∈ equalMassPartitions K μ) (σ : Equiv.Perm (Fin (r+2)))
    (t : Fin (r+1) → ℝ)
    (caps : ∀ i,prefixCells (fun j => (S (σ j)).val) i.castSucc =
      bodyPoints K ∩ {x | x.2 ≤ t i}) :
    ∀ i,ProductQuantiles.cumulative (bodyPoints K) μ (t i) =
      (i.val+1 : ℝ)*(μ.real (bodyPoints K)/(r+2)) := by
  have part := NRR.HorizontalExtension.convexPartition_reindex (convexPartition_of_partition hS.1) σ
  intro i
  have H := part.prefix_mass_real μ hμ (fun i j => hS.2 (σ i) (σ j)) i.castSucc
  rw [caps i] at H
  simpa only [ProductQuantiles.cumulative,Fin.coe_castSucc,Nat.cast_add,Nat.cast_ofNat] using H

/-- The windowed-chain neighborhood is now unconditional on the prescribed
mass data: all its inputs are the actual body, absolutely continuous
measure, inner cylinder, and the previously proved exact quantile windows. -/
theorem exists_equalMass_windowed_neighborhood {d r : ℕ}
    (K : ConvexBody (Space d × ℝ)) (μ : Measure (Space d × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {L H : ℝ}
    (inner : D ×ˢ Icc L H ⊆ bodyPoints K)
    (a b : Fin (r+1) → ℝ)
    (levels : ∀ i,{t | ProductQuantiles.cumulative (bodyPoints K) μ t =
      (i.val+1 : ℝ)*(μ.real (bodyPoints K)/(r+2))} = Icc (a i) (b i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ)),
      IsOpen U ∧
      (∀ S ∈ equalMassPartitions (n := r+2) K μ,
        (∀ i,∃ lo hi : ℝ,lo < hi ∧ bodyPoints (S i) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc lo hi) →
        convexConfigurations S ∈ U) ∧
      ∀ S ∈ equalMassPartitions (n := r+2) K μ,convexConfigurations S ∈ U →
        WindowedChain (bodyPoints K) a b ε (convexConfigurations S) := by
  let s := convexConfigurations '' equalMassPartitions (n := r+2) K μ
  have parts : ∀ C ∈ s,ConvexPartition (bodyPoints K) (fun i => (C i).val) := by
    rintro C ⟨S,hS,rfl⟩
    exact convexPartition_of_partition hS.1
  have quantiles : ∀ C ∈ s,∀ (σ : Equiv.Perm (Fin (r+2))) (t : Fin (r+1) → ℝ),
      (∀ i,prefixCells (fun j => (C (σ j)).val) i.castSucc = bodyPoints K ∩ {x | x.2 ≤ t i}) →
      ∀ i,t i ∈ Icc (a i) (b i) := by
    rintro C ⟨S,hS,rfl⟩ σ t caps i
    have H := equalMass_prefix_quantiles K μ hμ S hS σ t caps i
    exact (levels i) ▸ H
  obtain ⟨U,hU,slabs,chains⟩ := exists_open_windowedChains hD inner s parts a b hε quantiles
  refine ⟨U,hU,?_,?_⟩
  · intro S hS clips
    exact slabs (convexConfigurations S) (mem_image_of_mem _ hS) clips
  · intro S hS hSU
    exact chains (convexConfigurations S) hSU (convexPartition_of_partition hS.1)

end NRR.InterfaceChart
