import NRR.PrefixMoments

/-! Exact conversion of geometric slab membership and two prefix readings
into the globally patched planar model. -/

noncomputable section
open Set Topology Metric TopologicalSpace
open NRR.GlobalAssembly

namespace NRR.InterfaceChart

theorem layerChart_models {d r : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) (ε : ℝ)
    (a b : Fin (r+3) → ℝ) (t : Fin (r+2) → ℝ)
    (ordered : Monotone a) (axis : ∀ i,((0 : Space d),t i) ∈ K)
    (between : ∀ i,b i.castSucc < t i ∧ t i < a i.succ)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (bounds : ∀ s ∈ admissibleBox K ε (a 1) (b 1) (a 2) (b 2),∀ u ∈ D,
      lo ≤ height s.val.1 u ∧ height s.val.1 u ≤ height s.val.2 u ∧ height s.val.2 u ≤ hi)
    (cap : C(Parameters d,ℂ)) {X : Type*} [TopologicalSpace X]
    (cell : Fin (r+2) → C(X,ConvexLimits.ConvexCompact (Space d × ℝ)))
    (w : C(ConvexLimits.ConvexCompact (Space d × ℝ),ℂ)) (x : X)
    (σ : Equiv.Perm (Fin (r+2)))
    (members : ∀ i,cell (σ i) x ∈
      slabFamily compact convex ε (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ))
    (p : FeasibleParameters K) (hp : p ∈ admissibleBox K ε (a 1) (b 1) (a 2) (b 2))
    (special : cell (σ 1) x = cutConvexCompact compact convex p)
    (lower : cap p.val.1 = w (cell (σ 0) x))
    (upper : cap p.val.2 = w (cell (σ 0) x)+w (cell (σ 1) x))
    (balanced : ∑ i,w (cell i x) = 0) :
    (layerChart compact convex ε a b t ordered axis between hD inner bounds cap).Models cell w x := by
  let chart := layerChart compact convex ε a b t ordered axis between hD inner bounds cap
  have mem : ∀ i,cell (σ (secondCellLabels r i)) x ∈ chart.family i :=
    fun i => members (secondCellLabels r i)
  apply models_of_sorted_reading chart cell w x σ mem balanced
  have special' : cell (σ (secondCellLabels r none)) x = cutConvexCompact compact convex p := by
    simpa only [secondCellLabels_none] using special
  have same : (⟨cell (σ (secondCellLabels r none)) x,mem none⟩ : chart.family none) =
      ⟨cutConvexCompact compact convex p,mem_image_of_mem _ hp⟩ := Subtype.ext special'
  rw [same]
  have hS : IsCompact (admissibleBox K ε (a 1) (b 1) (a 2) (b 2)) :=
    compact_admissibleBox_of_axis (axis 1) (between 1).1 (between 1).2
  change slabProfileReadout compact convex hD inner _ hS bounds cap
    ⟨cutConvexCompact compact convex p,mem_image_of_mem _ hp⟩ = _
  rw [slabProfileReadout_apply compact convex hD inner _ hS bounds cap p hp,lower,upper]

end NRR.InterfaceChart
