import NRR.CubePartitionCharts
import NRR.ProductQuantiles

/-! Genuine internal prefix cuts of a horizontal cube partition stay a
positive distance from the two exterior faces. No condition is imposed on
an arbitrary relabelling unless it actually represents a prefix cap. -/

noncomputable section
open Set Topology TopologicalSpace

namespace NRR.CubeInternalMargins

open CubeHorizontalRigidity HorizontalExtension InterfaceChart

private theorem zero_mem_interior_square : (0 : Space 2) ∈ interior square := by
  have sub : Metric.ball (0 : Space 2) 1 ⊆ square := by
    intro u hu j
    rw [Metric.mem_ball, dist_zero_right] at hu
    have hn := PiLp.norm_apply_le (p := (2 : ENNReal)) u j
    rw [Real.norm_eq_abs] at hn
    exact ⟨(abs_lt.mp (hn.trans_lt hu)).1.le,
      (abs_lt.mp (hn.trans_lt hu)).2.le⟩
  exact interior_maximal sub Metric.isOpen_ball (by simp)

/-- The upper endpoint of an actual proper prefix cap is strictly internal.
The missing last cell supplies an interior interval point outside the prefix. -/
theorem internal_prefix_height {r : ℕ}
    (S : Fin (r + 2) → NonemptyCompacts (Space 2 × ℝ))
    (part : ConvexPartition (square ×ˢ Icc (-1 : ℝ) 1) S)
    (a b : Fin (r + 2) → ℝ) (positive : ∀ i, a i < b i)
    (clips : ∀ i, (S i : Set (Space 2 × ℝ)) ∩
      (square ×ˢ Icc (-1 : ℝ) 1) = square ×ˢ Icc (a i) (b i))
    (σ : Equiv.Perm (Fin (r + 2))) (i : Fin (r + 1))
    (cap : prefixCells (fun j => S (σ j)) i.castSucc =
      (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | x.2 ≤ b (σ i.castSucc)}) :
    -1 < b (σ i.castSucc) ∧ b (σ i.castSucc) < 1 := by
  let C := fun j => (S j : Set (Space 2 × ℝ))
  have bounds := endpoint_bounds zero_mem_interior_square C a b positive clips
  have disj := interval_disjoint zero_mem_interior_square C a b clips part.disjoint
  refine ⟨lt_of_le_of_lt (bounds _).1 (positive _), ?_⟩
  by_contra! upper
  let k : Fin (r + 2) := Fin.last (r + 1)
  let z : ℝ := (a (σ k) + b (σ k)) / 2
  have hz : z ∈ Ioo (a (σ k)) (b (σ k)) := by
    constructor <;> dsimp [z] <;> linarith [positive (σ k)]
  have hzCube : z ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bounds _).1.trans hz.1.le, hz.2.le.trans (bounds _).2⟩
  have hp : ((0, z) : Space 2 × ℝ) ∈ prefixCells (fun j => S (σ j)) i.castSucc := by
    rw [cap]
    exact ⟨⟨interior_subset zero_mem_interior_square, hzCube⟩,
      hzCube.2.trans upper⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp
  have hjInterval : z ∈ Icc (a (σ j.val)) (b (σ j.val)) := by
    have hx := (clips (σ j.val)) ▸
      (show ((0,z) : Space 2 × ℝ) ∈ C (σ j.val) ∩
        (square ×ˢ Icc (-1 : ℝ) 1) from
        ⟨hj, interior_subset zero_mem_interior_square, hzCube⟩)
    exact hx.2
  have hne : σ j.val ≠ σ k := by
    apply σ.injective.ne
    intro he
    have hle := j.property
    rw [he] at hle
    change r + 1 ≤ i.val at hle
    omega
  rcases interval_order a b positive disj hne with below | above
  · linarith [hjInterval.2, hz.1]
  · linarith [hjInterval.1, hz.2]

/-- One positive margin works for every ordering and every actual internal
prefix cap of this horizontal reference partition. -/
theorem exists_internal_margin {r : ℕ}
    (S : Fin (r + 2) → NonemptyCompacts (Space 2 × ℝ))
    (part : ConvexPartition (square ×ˢ Icc (-1 : ℝ) 1) S)
    (a b : Fin (r + 2) → ℝ) (positive : ∀ i, a i < b i)
    (clips : ∀ i, (S i : Set (Space 2 × ℝ)) ∩
      (square ×ˢ Icc (-1 : ℝ) 1) = square ×ˢ Icc (a i) (b i)) :
    ∃ h > (0 : ℝ), ∀ (σ : Equiv.Perm (Fin (r + 2))) (i : Fin (r + 1)),
      prefixCells (fun j => S (σ j)) i.castSucc =
        (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | x.2 ≤ b (σ i.castSucc)} →
      -1 + h ≤ b (σ i.castSucc) ∧ b (σ i.castSucc) ≤ 1 - h := by
  classical
  let valid (q : Equiv.Perm (Fin (r + 2)) × Fin (r + 1)) : Prop :=
    prefixCells (fun j => S (q.1 j)) q.2.castSucc =
      (square ×ˢ Icc (-1 : ℝ) 1) ∩ {x | x.2 ≤ b (q.1 q.2.castSucc)}
  let gap (q : Equiv.Perm (Fin (r + 2)) × Fin (r + 1)) : ℝ :=
    if valid q then min (b (q.1 q.2.castSucc) + 1) (1 - b (q.1 q.2.castSucc)) else 1
  have gap_pos (q) : 0 < gap q := by
    dsimp [gap]
    split_ifs with hv
    · have ht := internal_prefix_height S part a b positive clips q.1 q.2 hv
      exact lt_min (by linarith [ht.1]) (by linarith [ht.2])
    · norm_num
  obtain ⟨h, hh, bound⟩ := ProductQuantiles.exists_uniform_positive gap gap_pos
  refine ⟨h, hh, ?_⟩
  intro σ i cap
  have hb := bound (σ,i)
  have hv : valid (σ,i) := cap
  simp only [gap, if_pos hv] at hb
  have hl := hb.trans_le (min_le_left _ _)
  have hu := hb.trans_le (min_le_right _ _)
  constructor <;> linarith

end NRR.CubeInternalMargins
