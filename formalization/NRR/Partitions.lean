import NRR.CompactTests
import NRR.Moments

open Set Filter Topology TopologicalSpace Metric MeasureTheory
open scoped ENNReal
noncomputable section

namespace NRR

/-- The sum of the masses of closed convex pieces is the mass of the parent.
Their boundaries may overlap; they have zero mass by absolute continuity. -/
theorem BodyPartition.mass_eq_sum {d n : ℕ} {K : Body d} {S : Fin n → Body d}
    (h : BodyPartition K S) {μ : Measure (Space d)} (hμ : μ ≪ volume) :
    μ K.points = ∑ i, μ (S i).points := by
  have nullBoundary (i : Fin n) : μ (frontier (S i).points) = 0 :=
    hμ ((S i).property.1.addHaar_frontier volume)
  have hd : Pairwise (fun i j => AEDisjoint μ (S i).points (S j).points) := by
    intro i j hij
    apply measure_mono_null _ (measure_union_null (nullBoundary i) (nullBoundary j))
    intro x hx
    by_cases hi : x ∈ interior (S i).points
    · exact Or.inr ⟨subset_closure hx.2, fun hj => Set.disjoint_left.mp (h.disjoint hij) hi hj⟩
    · exact Or.inl ⟨subset_closure hx.1, hi⟩
  rw [← h.covers, measure_iUnion₀ hd (fun i =>
    (S i).val.isCompact.isClosed.measurableSet.nullMeasurableSet), tsum_fintype]

/-- The literal fraction of the parent's mass, also valid at infinite mass. -/
theorem BodyPartition.mass_eq_div {d n : ℕ} {K : Body d} {S : Fin n → Body d}
    (h : BodyPartition K S) {μ : Measure (Space d)} (hμ : μ ≪ volume)
    (hm : EqualMass μ S) (j : Fin n) :
    μ (S j).points = μ K.points / n := by
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_le j.val |>.trans_lt j.isLt)
  have sum_eq : μ K.points = (n : ℝ≥0∞) * μ (S j).points := by
    calc
      μ K.points = ∑ i, μ (S i).points := h.mass_eq_sum hμ
      _ = ∑ _i : Fin n, μ (S j).points := Finset.sum_congr rfl (fun i _ => hm i j)
      _ = _ := by simp [nsmul_eq_mul]
  rw [sum_eq, mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast hn) (by simp)]

private theorem contBody : Continuous (Body.toCompactConvex (d := d)) :=
  continuous_subtype_val.subtype_mk _

/-- Membership in the interior of the limiting convex body eventually gives
interior membership in the approximations, with a uniform inner ball. -/
private theorem eventually_interior {d : ℕ} {D : Body d} {A : ℕ → Body d}
    (h : Tendsto A atTop (𝓝 D)) {x : Space d} (hx : x ∈ interior D.points) :
    ∀ᶠ k in atTop, x ∈ interior (A k).points := by
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hc := (continuous_subtype_val.tendsto D).comp h
  filter_upwards [(Metric.tendsto_nhds.mp hc) (r/3) (by linarith)] with k hk
  apply mem_interior_iff_mem_nhds.mpr
  refine Metric.mem_nhds_iff.mpr ⟨r/3, by linarith, ?_⟩
  intro y hy
  apply Moments.mem_of_inner_ball D.toCompactConvex (A k).toCompactConvex (by linarith : 0 < r/3)
  · intro z hz
    apply hB
    exact lt_of_le_of_lt (dist_triangle z y x) (by
      have hz' : dist z y ≤ r/3 := hz
      have hy' : dist y x < r/3 := hy
      linarith)
  · exact (dist_comm D.val (A k).val) ▸ hk

theorem isClosed_bodyPartitions {d n : ℕ} (K : Body d) :
    IsClosed {S : Fin n → Body d | BodyPartition K S} := by
  classical
  refine isSeqClosed_iff_isClosed.mp ?_
  intro A S hA near
  have hp (k : ℕ) : BodyPartition K (A k) := hA k
  have hs (i : Fin n) := tendsto_pi_nhds.mp near i
  have sub (i : Fin n) : (S i).points ⊆ K.points := by
    apply (EMetric.NonemptyCompacts.isClosed_subsets_of_isClosed K.val.isCompact.isClosed).mem_of_tendsto
      ((continuous_subtype_val.tendsto (S i)).comp (hs i))
    apply Eventually.of_forall
    intro k
    change (A k i).points ⊆ K.points
    rw [← (hp k).covers]
    exact subset_iUnion (fun j => (A k j).points) i
  constructor
  · apply Set.Subset.antisymm (Set.iUnion_subset sub)
    intro x hx
    by_contra hn
    have absent (i : Fin n) : x ∉ (S i).points := fun e => hn (mem_iUnion.mpr ⟨i, e⟩)
    have eventual (i : Fin n) : ∀ᶠ k in atTop, x ∉ (A k i).points := by
      have hfront : x ∉ frontier (S i).points := by
        intro h
        exact absent i ((show IsClosed (S i).points from (S i).val.isCompact.isClosed).closure_subset h.1)
      filter_upwards [Moments.eventually_mem_iff ((contBody.tendsto _).comp (hs i)) hfront]
        with k hk using fun e => absent i (hk.mp e)
    obtain ⟨k, hk⟩ := (Filter.eventually_all.mpr eventual).exists
    obtain ⟨i, hi⟩ := mem_iUnion.mp ((hp k).covers.symm ▸ hx)
    exact hk i hi
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    obtain ⟨k, hki, hkj⟩ := ((eventually_interior (hs i) hi).and (eventually_interior (hs j) hj)).exists
    exact Set.disjoint_left.mp ((hp k).disjoint hij) hki hkj

theorem isClosed_equalMass {d n : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) : IsClosed {S : Fin n → Body d | EqualMass μ S} := by
  have hc := (Moments.continuous_integral μ hμ (integrable_const (1 : ℝ))).comp contBody
  have hm : Continuous (fun D : Body d => (μ D.points).toReal) := by
    simpa [Function.comp_def, setIntegral_one_eq_measureReal, measureReal_def,
      Moments.points, Body.toCompactConvex, Body.points] using hc
  have hset : {S : Fin n → Body d | EqualMass μ S} =
      ⋂ (i : Fin n) (j : Fin n), {S : Fin n → Body d | (μ (S i).points).toReal = (μ (S j).points).toReal} := by
    ext S
    simp only [mem_iInter, mem_setOf_eq, EqualMass]
    constructor
    · exact fun h i j => congrArg ENNReal.toReal (h i j)
    · exact fun h i j => (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h i j)
  rw [hset]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (hm.comp (continuous_apply i)) (hm.comp (continuous_apply j))

/-- Compactness for all body partitions, without any ambient extension or
power-diagram requirement. The lower bound on mass excludes degenerate cells. -/
theorem compact_bodyPartitions_of_mass {d n : ℕ} (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) {m : ℝ≥0∞} (hm : 0 < m) :
    IsCompact {S : Fin n → Body d | BodyPartition K S ∧ EqualMass μ S ∧ ∀ i, m ≤ μ (S i).points} := by
  have cells := CompactTests.compact_cells K μ hμ hm
  have compact := ((isCompact_univ_pi (ι := Fin n) (fun _ => cells)).inter_right
      (isClosed_bodyPartitions K)).inter_right (isClosed_equalMass μ hμ)
  convert compact using 1
  ext S
  constructor
  · rintro ⟨hp, he, lower⟩
    refine ⟨⟨fun i _ => ⟨?_, lower i⟩, hp⟩, he⟩
    rw [← hp.covers]
    exact subset_iUnion (fun j => (S j).points) i
  · rintro ⟨⟨hc, hp⟩, he⟩
    exact ⟨hp, he, fun i => (hc i trivial).2⟩

/-- The positive mass of K supplies the lower bound automatically. -/
theorem compact_equalMassPartitions {d n : ℕ} (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ K.points) :
    IsCompact {S : Fin n → Body d | BodyPartition K S ∧ EqualMass μ S} := by
  have cm := compact_bodyPartitions_of_mass (n := n) K μ hμ
    (ENNReal.div_pos hK.ne' (by simp : (n : ℝ≥0∞) ≠ ⊤))
  convert cm using 1
  ext S
  constructor
  · rintro ⟨hp, he⟩
    exact ⟨hp, he, fun i => (hp.mass_eq_div hμ he i).ge⟩
  · exact fun h => ⟨h.1, h.2.1⟩

end NRR
