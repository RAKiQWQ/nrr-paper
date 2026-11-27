import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

open Set Filter Topology TopologicalSpace MeasureTheory Metric

namespace NRR.Localization

/-- If a continuous horizontal coordinate is positive on every contact of
the limit body with a closed cylinder, nearby clipped bodies stay on its
nonnegative side. Empty intersections are included. -/
theorem eventually_positive_on_clip {X : Type} [MetricSpace X]
    {C : NonemptyCompacts X} {Ck : ℕ → NonemptyCompacts X}
    (h : Tendsto Ck atTop (𝓝 C)) {A : Set X} (hA : IsClosed A)
    (l : C(X, ℝ)) (contact : ∀ x ∈ (C : Set X) ∩ A, 0 < l x) :
    ∀ᶠ k in atTop, ∀ x ∈ (Ck k : Set X) ∩ A, 0 < l x := by
  let U := (A ∩ {x | l x ≤ 0})ᶜ
  have hU : IsOpen U := (hA.inter (isClosed_le l.continuous continuous_const)).isOpen_compl
  have hCU : (C : Set X) ⊆ U := by
    intro x hx hbad
    exact (contact x ⟨hx, hbad.1⟩).not_ge hbad.2
  obtain ⟨ε, hε, hsub⟩ := C.isCompact.exists_thickening_subset_open hU hCU
  filter_upwards [(Metric.tendsto_nhds.mp h) ε hε] with k hk
  intro x hx
  have hm : x ∈ Metric.thickening ε (C : Set X) :=
    Metric.mem_thickening_iff.mpr (Metric.exists_dist_lt_of_hausdorffDist_lt hx.1
      (by simpa only [NonemptyCompacts.dist_eq] using hk) (edist_ne_top (Ck k) C))
  exact lt_of_not_ge (fun hle => hsub hm ⟨hx.2, hle⟩)

/-- The closed-cylinder contact argument, expressed as actual restricted
integrals. Even a vanishing sequence of positive tail weights prevents
cancellation. Continuity of the full-body moment is an explicit hypothesis. -/
theorem eventually_positive_weighted_moment {X : Type} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    {C : NonemptyCompacts X} {Ck : ℕ → NonemptyCompacts X} (h : Tendsto Ck atTop (𝓝 C))
    {A : Set X} (hA : IsClosed A) (l : C(X, ℝ))
    (contact : ∀ x ∈ (C : Set X) ∩ A, 0 < l x)
    (δ tail : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (ht : Tendsto tail atTop (𝓝 m))
    (hδ : ∀ k, 0 < δ k) :
    ∀ᶠ k in atTop, 0 < (∫ x in (Ck k : Set X) ∩ A, l x ∂μ) + δ k * tail k := by
  filter_upwards [eventually_positive_on_clip h hA l contact, ht.eventually (lt_mem_nhds hm)]
    with k hc hk
  exact add_pos_of_nonneg_of_pos
    (setIntegral_nonneg ((Ck k).isCompact.isClosed.measurableSet.inter hA.measurableSet)
      (fun x hx => (hc x hx).le)) (mul_pos (hδ k) hk)

/-- The strict horizontal bound obtained by averaging a separating plane.
The same statement applies to a weighted centroid. -/
theorem positive_centroid_of_separation {x z a p b h : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hz : |z| < h)
    (hsep : a*p + h*|b| ≤ x + b*z) : 0 < x := by
  have ht : b*z ≤ h*|b| := calc
    b*z ≤ |b*z| := le_abs_self _
    _ = |b| * |z| := abs_mul _ _
    _ ≤ |b| * h := mul_le_mul_of_nonneg_left hz.le (abs_nonneg _)
    _ = h*|b| := mul_comm _ _
  linarith [mul_pos ha hp]

end NRR.Localization
