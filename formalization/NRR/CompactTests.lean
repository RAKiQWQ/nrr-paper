import NRR.Geometry
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.Sequences

/-! Hausdorff compactness with a positive lower bound on cell mass. -/

noncomputable section
open Set MeasureTheory TopologicalSpace Filter Metric
open scoped Topology ENNReal

namespace NRR.CompactTests

private abbrev Carrier (d : ℕ) := NonemptyCompacts (Space d)

private theorem limit_point {d : ℕ} {A : ℕ → Carrier d} {B : Carrier d}
    (h : Tendsto A atTop (𝓝 B)) {u : ℕ → Space d} {x : Space d}
    (hu : Tendsto u atTop (𝓝 x)) (hm : ∀ n, u n ∈ A n) : x ∈ B := by
  apply (B.isCompact.isClosed.mem_iff_infDist_zero B.nonempty).2
  have hz := Metric.lipschitz_infDist.continuous.continuousAt.tendsto.comp (hu.prodMk_nhds h)
  apply tendsto_nhds_unique _ hz |>.symm
  simpa only [Function.comp_def, infDist_zero_of_mem (hm _)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem approximate_point {d : ℕ} {A : ℕ → NonemptyCompacts (Space d)} {B : NonemptyCompacts (Space d)}
    (h : Tendsto A atTop (𝓝 B)) {x : Space d} (hx : x ∈ B) :
    ∃ u : ℕ → Space d, (∀ n, u n ∈ A n) ∧ Tendsto u atTop (𝓝 x) := by
  choose u hu hdist using fun n => (A n).isCompact.exists_infDist_eq_dist (A n).nonempty x
  refine ⟨u, hu, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have ht := (Metric.lipschitz_infDist_set x).continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, infDist_zero_of_mem hx, hdist, dist_comm x] using ht

private theorem closed_convex (d : ℕ) :
    IsClosed {A : Carrier d | Convex ℝ (A : Set (Space d))} := by
  apply isSeqClosed_iff_isClosed.mp
  intro A B hc h x hx y hy a b ha hb hab
  obtain ⟨u, hu, hux⟩ := approximate_point h hx
  obtain ⟨v, hv, hvy⟩ := approximate_point h hy
  exact limit_point h ((hux.const_smul a).add (hvy.const_smul b))
    (fun n => hc n (hu n) (hv n) ha hb hab)

private theorem closed_mass_lower_bound {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (m : ℝ≥0∞) : IsClosed {A : Carrier d | m ≤ μ (A : Set (Space d))} := by
  apply isSeqClosed_iff_isClosed.mp
  intro A B hm h
  have hlim := (tendsto_measure_cthickening_of_isClosed (μ := μ)
    ⟨1, zero_lt_one, measure_ne_top μ _⟩ B.isCompact.isClosed).comp
      (tendsto_iff_dist_tendsto_zero.mp h)
  apply ge_of_tendsto' hlim
  intro n
  refine (hm n).trans (measure_mono fun x hx => ?_)
  obtain ⟨y, hy, hxy⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty x
  apply mem_cthickening_of_dist_le x y _ _ hy
  rw [← hxy]
  exact infDist_le_hausdorffDist_of_mem hx (edist_ne_top (A n) B)

private theorem compact_subsets {d : ℕ} (K : Body d) :
    IsCompact {A : Carrier d | (A : Set (Space d)) ⊆ K.points} := by
  let incl : K.val → Space d := Subtype.val
  let push (A : NonemptyCompacts K.val) : Carrier d :=
    ⟨⟨incl '' (A : Set K.val), A.isCompact.image continuous_subtype_val⟩, A.nonempty.image incl⟩
  have hi : Isometry push := Isometry.of_dist_eq fun _ _ =>
    Metric.hausdorffDist_image (isometry_subtype_coe (s := (K.val : Set (Space d))))
  have hr : range push = {A : Carrier d | (A : Set (Space d)) ⊆ K.points} := by
    ext A
    constructor
    · rintro ⟨T, rfl⟩ _ ⟨y, _, rfl⟩
      exact y.property
    · intro hA
      let T : Set K.val := incl ⁻¹' (A : Set (Space d))
      have hc : IsCompact T := (A.isCompact.isClosed.preimage continuous_subtype_val).isCompact
      obtain ⟨x, hx⟩ := A.nonempty
      let S : NonemptyCompacts K.val := ⟨⟨T, hc⟩, ⟨⟨x, hA hx⟩, hx⟩⟩
      refine ⟨S, NonemptyCompacts.ext ?_⟩
      change incl '' T = (A : Set (Space d))
      exact Subset.antisymm (fun _ ⟨_, hy, h⟩ => h ▸ hy)
        (fun y hy => ⟨⟨y, hA hy⟩, hy, rfl⟩)
  exact hr ▸ isCompact_range hi.continuous

/-- The mass lower bound is positive, so Hausdorff limits stay in the space
of full-dimensional convex bodies. The mass need not have a positive density. -/
theorem compact_cells {d : ℕ} (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) {m : ℝ≥0∞} (hm : 0 < m) :
    IsCompact {C : Body d | C.points ⊆ K.points ∧ m ≤ μ C.points} := by
  let T := {A : Carrier d | (A : Set (Space d)) ⊆ K.points} ∩
    ({A : Carrier d | Convex ℝ (A : Set (Space d))} ∩ {A | m ≤ μ (A : Set (Space d))})
  have ht : IsCompact T := (compact_subsets K).inter_right
    ((closed_convex d).inter (closed_mass_lower_bound μ m))
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert ht using 1
  ext A
  constructor
  · rintro ⟨C, ⟨hs, hc⟩, rfl⟩
    exact ⟨hs, C.property.1, hc⟩
  · rintro ⟨hs, hc, hmA⟩
    have hn : (interior (A : Set (Space d))).Nonempty := by
      by_contra! h
      have hf := hμ (hc.addHaar_frontier volume)
      rw [frontier, A.isCompact.isClosed.closure_eq, h, diff_empty] at hf
      exact (hm.trans_le hmA).ne' hf
    exact ⟨⟨A, hc, hn⟩, ⟨hs, hmA⟩, rfl⟩

end NRR.CompactTests
