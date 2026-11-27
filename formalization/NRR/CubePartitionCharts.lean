import NRR.CubeHorizontalRigidity
import NRR.HorizontalExtension

/-! Local graph charts for convex partitions of the three-dimensional cube. -/

noncomputable section
open Set Topology TopologicalSpace

namespace NRR.CubePartitionCharts

open NRR.CubeHorizontalRigidity NRR.HorizontalExtension NRR.InterfaceChart

/-- A horizontal layering of the cube admits a neighborhood in which every
nearby convex partition has one ordered family of small-slope graph interfaces.
The interval and clipping hypotheses record the exact horizontal-layer
geometry on the transverse square. -/
theorem exists_cube_graph_chart {r : ℕ}
    (S : Fin (r + 2) → NonemptyCompacts (Space 2 × ℝ))
    (part : ConvexPartition (square ×ˢ Icc (-1 : ℝ) 1) S)
    (a b : Fin (r + 2) → ℝ)
    (positive : ∀ i, a i < b i)
    (clips : ∀ i,
      (S i : Set (Space 2 × ℝ)) ∩ (square ×ˢ Icc (-1 : ℝ) 1) =
        square ×ˢ Icc (a i) (b i))
    (η : ℝ) (hη : 0 < η) :
    ∃ σ : Equiv.Perm (Fin (r + 2)),
    ∃ U : Set (Fin (r + 2) → NonemptyCompacts (Space 2 × ℝ)),
      IsOpen U ∧ S ∈ U ∧
      (∀ i : Fin (r + 1),
        prefixCells (fun j => S (σ j)) i.castSucc =
          (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | x.2 ≤ b (σ i.castSucc)}) ∧
      ∀ T ∈ U, ConvexPartition (square ×ˢ Icc (-1 : ℝ) 1) T →
        ∃ P : Fin (r + 1) → Parameters 2,
          ChainPartition (square ×ˢ Icc (-1 : ℝ) 1) (fun i => T (σ i)) ∧
          (∀ i, dist (P i) (0, b (σ i.castSucc)) < η) ∧
          (∀ i, prefixCells (fun j => T (σ j)) i.castSucc =
              (square ×ˢ Icc (-1 : ℝ) 1) ∩
                {x | x.2 ≤ height (P i) x.1}) ∧
          ∀ i, suffixCells (fun j => T (σ j)) i.succ =
              (square ×ˢ Icc (-1 : ℝ) 1) ∩
                {x | height (P i) x.1 ≤ x.2} := by
  have hD : (0 : Space 2) ∈ interior square := by
    have ball_sub : Metric.ball (0 : Space 2) 1 ⊆ square := by
      intro u hu j
      rw [Metric.mem_ball, dist_zero_right] at hu
      have hn := PiLp.norm_apply_le (p := (2 : ENNReal)) u j
      rw [Real.norm_eq_abs] at hn
      exact ⟨(abs_lt.mp (hn.trans_lt hu)).1.le, (abs_lt.mp (hn.trans_lt hu)).2.le⟩
    exact interior_maximal ball_sub Metric.isOpen_ball (by simp)
  obtain ⟨σ,U,hU,memU,caps,chart⟩ :=
    slab_partition_has_unlabelled_chart_with_caps hD S part a b positive clips
      (by intro x hx; exact hx) hη
  refine ⟨σ,U,hU,memU,caps,?_⟩
  intro T hT hpart
  obtain ⟨P,chain,near,hcaps⟩ := chart T hT hpart
  exact ⟨P,chain,near,fun i => (hcaps i).1,fun i => (hcaps i).2⟩

end NRR.CubePartitionCharts
