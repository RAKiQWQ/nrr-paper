import NRR.CubePartitionCharts

/-! Uniform height bounds for graph charts over the transverse square. -/

noncomputable section
open Set Topology TopologicalSpace

namespace NRR.CubeChartBounds

open NRR.CubeHorizontalRigidity NRR.HorizontalExtension NRR.InterfaceChart

private theorem square_norm_le_two (u : Space 2) (hu : u ∈ square) : ‖u‖ ≤ 2 := by
  have hcoord (j : Fin 2) : ‖u j‖ ^ 2 ≤ 1 := by
    have h : |u j| ≤ (1 : ℝ) := abs_le.mpr (hu j)
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (u j)]
  have hsum : (∑ j : Fin 2, ‖u j‖ ^ 2) ≤ 2 := by
    simpa only [Fin.sum_univ_two, one_add_one_eq_two] using add_le_add (hcoord 0) (hcoord 1)
  have hnorm : ‖u‖ ^ 2 ≤ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hsum
  nlinarith [norm_nonneg u]

/-- Every nearby convex partition has small affine graph parameters, and its
graphs remain inside the vertical range of the cube over the whole square.
The margin hypothesis applies only to actual internal prefix cuts, identified
by the reference cap equality. In particular it imposes no bound on a top
endpoint merely because an unrelated permutation moves it into a prefix. -/
theorem exists_bounded_cube_graph_chart {r : ℕ}
    (S : Fin (r + 2) → NonemptyCompacts (Space 2 × ℝ))
    (part : ConvexPartition (square ×ˢ Icc (-1 : ℝ) 1) S)
    (a b : Fin (r + 2) → ℝ)
    (positive : ∀ i, a i < b i)
    (clips : ∀ i,
      (S i : Set (Space 2 × ℝ)) ∩ (square ×ˢ Icc (-1 : ℝ) 1) =
        square ×ˢ Icc (a i) (b i))
    (h : ℝ) (hh : 0 < h)
    (margin : ∀ (σ : Equiv.Perm (Fin (r + 2))) (i : Fin (r + 1)),
      prefixCells (fun j => S (σ j)) i.castSucc =
        (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | x.2 ≤ b (σ i.castSucc)} →
      -1 + h ≤ b (σ i.castSucc) ∧ b (σ i.castSucc) ≤ 1 - h)
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
              (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | x.2 ≤ height (P i) x.1}) ∧
          (∀ i, suffixCells (fun j => T (σ j)) i.succ =
              (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | height (P i) x.1 ≤ x.2}) ∧
          (∀ i u, u ∈ square → ‖(P i).1‖ ≤ η ∧
            -1 ≤ height (P i) u ∧ height (P i) u ≤ 1) := by
  let ε := min (η / 4) (h / 4)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨σ,U,hU,memU,refCaps,chart⟩ :=
    NRR.CubePartitionCharts.exists_cube_graph_chart S part a b positive clips ε hε
  refine ⟨σ,U,hU,memU,refCaps,?_⟩
  intro T hT hpart
  obtain ⟨P,chain,near,pcaps,scaps⟩ := chart T hT hpart
  refine ⟨P,chain,?_,pcaps,scaps,?_⟩
  · intro i
    have heps : ε ≤ η / 4 := min_le_left _ _
    exact (near i).trans_le (heps.trans (by linarith))
  · intro i u hu
    have hd := near i
    have hnorm : ‖(P i).1‖ ≤ dist (P i) (0, b (σ i.castSucc)) := by
      have h := le_max_left (dist (P i).1 (0 : Space 2 →L[ℝ] ℝ)) (dist (P i).2 (b (σ i.castSucc)))
      simpa only [Prod.dist_eq, Prod.fst, Prod.snd, dist_zero_right] using h
    have hsmall : dist (P i) (0, b (σ i.castSucc)) < η / 4 := by
      have : ε ≤ η / 4 := min_le_left _ _
      exact (hd.trans_le this)
    have hn : ‖(P i).1‖ ≤ η := by linarith [hnorm, hsmall]
    have hbase := margin σ i (refCaps i)
    have hdelta : |height (P i) u - b (σ i.castSucc)| ≤
        (‖u‖ + 1) * dist (P i) (0, b (σ i.castSucc)) := by
      simpa [height] using height_dist_le (P i) (0, b (σ i.castSucc)) u
    have hheight : |height (P i) u - b (σ i.castSucc)| ≤ 3 * (h / 4) := by
      have huNorm := square_norm_le_two u hu
      have hcoef : ‖u‖ + 1 ≤ 3 := by linarith
      calc
        _ ≤ (‖u‖ + 1) * dist (P i) (0, b (σ i.castSucc)) := hdelta
        _ ≤ 3 * dist (P i) (0, b (σ i.castSucc)) := by
          exact mul_le_mul_of_nonneg_right hcoef (dist_nonneg)
        _ ≤ 3 * (h / 4) := by
          have hd' : dist (P i) (0, b (σ i.castSucc)) ≤ h / 4 :=
            (near i).le.trans (min_le_right _ _)
          exact mul_le_mul_of_nonneg_left hd' (by norm_num)
    have hhgt := abs_le.mp hheight
    exact ⟨hn, by linarith [hbase.1, hhgt.1], by linarith [hbase.2, hhgt.2]⟩

end NRR.CubeChartBounds
