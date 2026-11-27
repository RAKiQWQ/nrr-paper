import NRR.PartitionMoments
import NRR.SlabFamilies

/-! Continuous actual prefix-cap moments.  The graph normal always has
vertical coefficient one, so every moving boundary has Haar measure zero. -/

noncomputable section
open Set Filter Topology MeasureTheory Metric

namespace NRR.InterfaceChart

def belowGraph {d : ℕ} (p : Parameters d) : Set (Space d × ℝ) :=
  {x | x.2 ≤ height p x.1}

theorem measurableSet_belowGraph {d : ℕ} (p : Parameters d) :
    MeasurableSet (belowGraph p) := by
  apply (isClosed_le continuous_snd _).measurableSet
  dsimp [height]
  fun_prop

theorem graph_null {d : ℕ} (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    (p : Parameters d) : μ {x | x.2 = height p x.1} = 0 := by
  let F := ContinuousLinearMap.snd ℝ (Space d) ℝ -
    p.1.comp (ContinuousLinearMap.fst ℝ (Space d) ℝ)
  have onto : Function.Surjective F := by
    intro z
    exact ⟨(0,z),by simp [F]⟩
  have H := (convex_halfSpace_le F.toLinearMap.isLinear p.2).addHaar_frontier
    ((volume : Measure (Space d)).prod (volume : Measure ℝ))
  change volume (frontier (F ⁻¹' Iic p.2)) = 0 at H
  rw [F.frontier_preimage onto,frontier_Iic] at H
  have eq : {x | x.2 = height p x.1} = F ⁻¹' {p.2} := by
    ext x
    change x.2 = p.1 x.1+p.2 ↔ x.2-p.1 x.1 = p.2
    constructor <;> intro h <;> linarith
  rw [eq]
  exact hμ H

def prefixMoment {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure (Space d × ℝ)) (f : (Space d × ℝ) → F) (p : Parameters d) : F :=
  ∫ x in belowGraph p, f x ∂μ

theorem continuous_prefixMoment {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    {f : (Space d × ℝ) → F} (hf : Integrable f μ) :
    Continuous (prefixMoment μ f) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro p q near
  have hnull : ∀ᵐ x ∂μ, x.2 ≠ height q x.1 :=
    compl_mem_ae_iff.mpr (graph_null μ hμ q)
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun k => (belowGraph (p k)).indicator f x) atTop
      (𝓝 ((belowGraph q).indicator f x)) := by
    filter_upwards [hnull] with x hx
    have ht := (continuous_height_parameters x.1).continuousAt.tendsto.comp near
    apply tendsto_const_nhds.congr'
    rcases lt_or_gt_of_ne hx with h | h
    · filter_upwards [ht.eventually (lt_mem_nhds h)] with k hk
      change x.2 < height (p k) x.1 at hk
      simp [belowGraph,h.le,hk.le]
    · filter_upwards [ht.eventually (gt_mem_nhds h)] with k hk
      change height (p k) x.1 < x.2 at hk
      simp [belowGraph,not_le.mpr h,not_le.mpr hk]
  change Tendsto (fun k => prefixMoment μ f (p k)) atTop (𝓝 (prefixMoment μ f q))
  simp only [prefixMoment,← integral_indicator (measurableSet_belowGraph _)]
  exact tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun k => hf.aestronglyMeasurable.indicator (measurableSet_belowGraph _)) hf.norm
    (fun k => Eventually.of_forall (fun x => by
      by_cases h : x ∈ belowGraph (p k) <;> simp [Set.indicator,h])) hlim

/-- A genuine continuous moment read from each of the two interfaces of a
single slab. The upper prefix carries the sign required by additivity. -/
def slabMomentReadout {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi)
    (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    {f : (Space d × ℝ) → ℂ} (hf : Integrable f μ) :
    C(cutConvexCompact compact convex '' S,ℂ × ℂ) :=
  let P := slabInterfaceReadout compact convex hD inner S hS bounds
  ⟨fun C => (prefixMoment μ f (P C).1,-prefixMoment μ f (P C).2),
    (((continuous_prefixMoment μ hμ hf).comp (continuous_fst.comp P.continuous)).prodMk
      ((continuous_prefixMoment μ hμ hf).comp (continuous_snd.comp P.continuous)).neg)⟩

@[simp] theorem slabMomentReadout_apply {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi)
    (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    {f : (Space d × ℝ) → ℂ} (hf : Integrable f μ)
    (r : FeasibleParameters K) (hr : r ∈ S) :
    slabMomentReadout compact convex hD inner S hS bounds μ hμ hf
      ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩ =
        (prefixMoment μ f r.val.1,-prefixMoment μ f r.val.2) := by
  change (prefixMoment μ f
    (slabInterfaceReadout compact convex hD inner S hS bounds
      ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩).1,
    -prefixMoment μ f
    (slabInterfaceReadout compact convex hD inner S hS bounds
      ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩).2) = _
  rw [slabInterfaceReadout_apply compact convex hD inner S hS bounds r hr]

end NRR.InterfaceChart
