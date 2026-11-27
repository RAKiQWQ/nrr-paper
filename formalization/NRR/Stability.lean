import NRR.Partitions
import Mathlib.Tactic

open Set MeasureTheory
noncomputable section

namespace NRR.Stability

/-- Sum of all ordered pairwise distances. Vanishing is exactly fairness. -/
def variation {n : ℕ} {E : Type*} [MetricSpace E] (v : Fin n → E) : ℝ :=
  ∑ i, ∑ j, dist (v i) (v j)

theorem variation_pos {n : ℕ} {E : Type*} [MetricSpace E] {v : Fin n → E}
    (h : ∃ i j, v i ≠ v j) : 0 < variation v := by
  obtain ⟨i, j, hij⟩ := h
  apply (dist_pos.mpr hij).trans_le
  calc
    _ ≤ ∑ k, dist (v i) (v k) := Finset.single_le_sum (fun _ _ => dist_nonneg) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun k => ∑ j, dist (v k) (v j))
      (fun k _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
      (Finset.mem_univ i)

/-- The compact complement of the slab chart has a uniform stability
radius, including when the base characteristic depends on multiple coordinates. -/
theorem uniform_rejection {n : ℕ} {X B E : Type*} [TopologicalSpace X]
    [TopologicalSpace B] [MetricSpace E] (cell : Fin n → C(X, B)) (f : C(B, E))
    (s : Set X) (hc : IsCompact s)
    (base : ∀ x ∈ s, ∃ i j, f (cell i x) ≠ f (cell j x)) :
    ∃ ε > (0 : ℝ), ∀ g : B → E, (∀ b, dist (f b) (g b) ≤ ε) →
      ∀ x ∈ s, ∃ i j, g (cell i x) ≠ g (cell j x) := by
  let spread : X → ℝ := fun x => variation (fun i => f (cell i x))
  have hs : Continuous spread := by dsimp [spread, variation]; fun_prop
  obtain ⟨m, hm, hmin⟩ := hc.exists_forall_le' hs.continuousOn
    (fun x hx => variation_pos (base x hx))
  let ε := m / (2 * (n : ℝ)^2 + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, fun g hg x hx => ?_⟩
  by_contra! equal
  have each (i j : Fin n) : dist (f (cell i x)) (f (cell j x)) ≤ 2*ε := calc
    _ ≤ dist (f (cell i x)) (g (cell i x)) + dist (g (cell i x)) (f (cell j x)) :=
      dist_triangle _ _ _
    _ ≤ ε + ε := add_le_add (hg _) (by rw [equal i j, dist_comm]; exact hg _)
    _ = _ := by ring
  have upper : spread x ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2*ε :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => each i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at upper
  have he : ε * (2 * (n : ℝ)^2 + 1) = m := by
    dsimp [ε]
    field_simp
  nlinarith [hmin x hx]

end NRR.Stability
