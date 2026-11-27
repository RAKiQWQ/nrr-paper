import NRR.PrimePowerBorsuk
import NRR.PrimePowerCuts
import NRR.PrimePowerLimit

/-! A Borsuk–Ulam bisection for continuous single-piece characteristics. -/

noncomputable section
open Set MeasureTheory Topology TopologicalSpace Filter Metric
open scoped NNReal ENNReal

namespace NRR.Bisection

abbrev Direction (d : ℕ) := sphere (0 : Space d) 1

private def ordered {d : ℕ} (u : Direction d) (S : Fin 2 → Body d) : Prop :=
  ∀ x ∈ (S 0).points, ∀ y ∈ (S 1).points, inner ℝ (u : Space d) x ≤ inner ℝ (u : Space d) y

private theorem surj {d : ℕ} (u : Direction d) :
    Function.Surjective (innerSL ℝ (u : Space d)) := by
  have hn : ‖(u : Space d)‖ = 1 := by simp
  intro r
  exact ⟨r • u.val, by simp [innerSL_apply, real_inner_self_eq_norm_sq, hn]⟩

variable {d : ℕ} (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]

private abbrev Parts := {S : Fin 2 → Body d // BodyPartition K S ∧ EqualMass μ S}

private theorem exists_ordered (hμ : μ ≪ volume) (hK : 0 < μ.real K.points)
    (u : Direction d) : ∃ S : Parts K μ, ordered u S.val := by
  obtain ⟨t, S, _, hcell, hp, hm⟩ := ParallelCuts.exists_equalMass_slabs K μ
    (innerSL ℝ (u : Space d)) hμ (surj u) hK (show 0 < 2 by decide)
  refine ⟨⟨S, hp, hm⟩, ?_⟩
  intro x hx y hy
  rw [hcell] at hx hy
  exact hx.2.2.trans hy.2.1

private theorem covers_two {S : Fin 2 → Body d} (hp : BodyPartition K S) :
    (S 0).points ∪ (S 1).points = K.points := by
  rw [← hp.covers]
  ext x
  constructor
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨0, hx⟩
    · exact mem_iUnion.mpr ⟨1, hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

private theorem lower_cap (u : Direction d) (A B : Body d) (cover : A.points ∪ B.points = K.points)
    (ord : ∀ x ∈ A.points, ∀ y ∈ B.points, inner ℝ u.val x ≤ inner ℝ u.val y) :
    ∃ t : ℝ, A.points = K.points ∩ (innerSL ℝ u.val) ⁻¹' Iic t := by
  let L := innerSL ℝ u.val
  obtain ⟨x, hx, hmax⟩ := A.val.isCompact.exists_isMaxOn A.val.nonempty L.continuous.continuousOn
  let H := K.points ∩ L ⁻¹' Iic (L x)
  have sub : A.points ⊆ H := fun y hy => ⟨cover ▸ Or.inl hy, hmax hy⟩
  have hconv : Convex ℝ H := K.property.1.inter (convex_halfSpace_le L.toLinearMap.isLinear _)
  have hint : (interior H).Nonempty := A.property.2.mono (interior_mono sub)
  have hclosed : IsClosed H := K.val.isCompact.isClosed.inter (isClosed_Iic.preimage L.continuous)
  have hstrict : interior H ⊆ L ⁻¹' Iio (L x) := by
    rw [← interior_Iic, ← L.interior_preimage (surj u)]
    exact interior_mono inter_subset_right
  have inside : interior H ⊆ A.points := by
    intro y hy
    have hyK := (interior_subset hy).1
    rw [← cover] at hyK
    exact hyK.resolve_right fun hyB => (not_lt_of_ge (ord x hx y hyB)) (hstrict hy)
  refine ⟨L x, sub.antisymm ?_⟩
  change H ⊆ A.points
  rw [← hclosed.closure_eq, ← hconv.closure_interior_eq_closure_of_nonempty_interior hint]
  exact closure_minimal inside A.val.isCompact.isClosed

private theorem eq_of_nested (hvol : volume.restrict K.points ≪ μ)
    (A B : Body d) (hBK : B.points ⊆ K.points) (hAB : A.points ⊆ B.points)
    (hm : μ A.points = μ B.points) : A.points = B.points := by
  have hz : μ (B.points \ A.points) = 0 := by
    rw [measure_diff hAB A.val.isCompact.isClosed.measurableSet.nullMeasurableSet
      (measure_ne_top _ _), hm, tsub_self]
  have hv := hvol hz
  have hmeas : MeasurableSet (B.points \ A.points) :=
    B.val.isCompact.isClosed.measurableSet.diff A.val.isCompact.isClosed.measurableSet
  rw [Measure.restrict_apply hmeas, inter_eq_self_of_subset_left (diff_subset.trans hBK)] at hv
  have openSet : IsOpen (interior B.points \ A.points) := isOpen_interior.sdiff A.val.isCompact.isClosed
  have empty : interior B.points \ A.points = ∅ := (openSet.measure_eq_zero_iff volume).mp
    (measure_mono_null (diff_subset_diff_left interior_subset) hv)
  have innerSub : interior B.points ⊆ A.points := diff_eq_empty.mp empty
  apply hAB.antisymm
  have closedB : IsClosed B.points := B.val.isCompact.isClosed
  have cvxB : Convex ℝ B.points := B.property.1
  rw [← closedB.closure_eq, ← cvxB.closure_interior_eq_closure_of_nonempty_interior B.property.2]
  exact closure_minimal innerSub A.val.isCompact.isClosed

private theorem unique_lower (hvol : volume.restrict K.points ≪ μ) (u : Direction d)
    (A B A' B' : Body d) (cover : A.points ∪ B.points = K.points)
    (cover' : A'.points ∪ B'.points = K.points)
    (ord : ∀ x ∈ A.points, ∀ y ∈ B.points, inner ℝ u.val x ≤ inner ℝ u.val y)
    (ord' : ∀ x ∈ A'.points, ∀ y ∈ B'.points, inner ℝ u.val x ≤ inner ℝ u.val y)
    (mass : μ A.points = μ A'.points) : A = A' := by
  obtain ⟨t, ht⟩ := lower_cap K u A B cover ord
  obtain ⟨s, hs⟩ := lower_cap K u A' B' cover' ord'
  apply Subtype.ext
  apply NonemptyCompacts.ext
  rcases le_total t s with h | h
  · exact eq_of_nested K μ hvol A A' (cover' ▸ subset_union_left)
      (by rw [ht, hs]; exact inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.mpr h))) mass
  · exact (eq_of_nested K μ hvol A' A (cover ▸ subset_union_left)
      (by rw [hs, ht]; exact inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.mpr h))) mass.symm).symm

private theorem reverse_order {u : Direction d} {A B : Body d}
    (h : ∀ x ∈ A.points, ∀ y ∈ B.points, inner ℝ u.val x ≤ inner ℝ u.val y) :
    ∀ y ∈ B.points, ∀ x ∈ A.points, inner ℝ (-u).val y ≤ inner ℝ (-u).val x := by
  intro y hy x hx
  simpa only [coe_neg_sphere, inner_neg_left, neg_le_neg_iff] using h x hx y hy

private theorem unique_ordered (hμ : μ ≪ volume) (hvol : volume.restrict K.points ≪ μ)
    (u : Direction d) (A B : Parts K μ) (ha : ordered u A.val) (hb : ordered u B.val) : A = B := by
  have coverA := covers_two K A.property.1
  have coverB := covers_two K B.property.1
  have mass (i j : Fin 2) : μ (A.val i).points = μ (B.val j).points :=
    (A.property.1.mass_eq_div hμ A.property.2 i).trans
      (B.property.1.mass_eq_div hμ B.property.2 j).symm
  apply Subtype.ext
  funext i
  fin_cases i
  · exact unique_lower K μ hvol u _ _ _ _ coverA coverB ha hb (mass _ _)
  · exact unique_lower K μ hvol (-u) _ _ _ _ ((union_comm _ _).trans coverA)
      ((union_comm _ _).trans coverB) (reverse_order ha) (reverse_order hb) (mass _ _)

omit [IsFiniteMeasure μ] in
private theorem closed_ordered :
    IsClosed {p : Direction d × Parts K μ | ordered p.1 p.2.val} := by
  refine isSeqClosed_iff_isClosed.mp ?_
  intro p q hp near x hx y hy
  have hparts : Tendsto (fun k => (p k).2.val) atTop (𝓝 q.2.val) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto q).comp near
  have hbody (i : Fin 2) : Tendsto (fun k => ((p k).2.val i).val) atTop (𝓝 (q.2.val i).val) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_pi_nhds.mp hparts i)
  have hdir : Tendsto (fun k => (p k).1.val) atTop (𝓝 q.1.val) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto q).comp near
  obtain ⟨a, ha, hax⟩ := CompactTests.approximate_point (hbody 0) hx
  obtain ⟨b, hb, hby⟩ := CompactTests.approximate_point (hbody 1) hy
  exact le_of_tendsto_of_tendsto (hdir.inner hax) (hdir.inner hby)
    (Eventually.of_forall fun k => hp k (a k) (ha _) (b k) (hb _))

/-- Positive mass on every open part of the body makes its oriented
equal-mass halfspace cuts unique and continuous in the normal direction. -/
theorem continuous_half (hμ : μ ≪ volume) (hvol : volume.restrict K.points ≪ μ)
    (hK : 0 < μ.real K.points) :
    ∃ f : C(Direction d, Body d), ∀ u, ∃ S : Fin 2 → Body d, BodyPartition K S ∧
      EqualMass μ S ∧ S 0 = f u ∧ S 1 = f (-u) := by
  choose S hs using exists_ordered K μ hμ hK
  have hmass : 0 < μ K.points := (ENNReal.toReal_pos_iff.mp hK).1
  letI : CompactSpace (Parts K μ) :=
    isCompact_iff_compactSpace.mp (compact_equalMassPartitions (n := 2) K μ hμ hmass)
  have hcont : Continuous S := by
    refine continuous_iff_isClosed.mpr fun F hF => ?_
    have hg := isClosedMap_fst_of_compactSpace _
      ((closed_ordered K μ).inter (hF.preimage (continuous_snd (X := Direction d))))
    convert hg using 1
    ext u
    constructor
    · exact fun hu => ⟨(u, S u), ⟨hs u, hu⟩, rfl⟩
    · rintro ⟨⟨v, A⟩, ⟨hA, hAF⟩, rfl⟩
      exact (unique_ordered K μ hμ hvol v A (S v) hA (hs v)) ▸ hAF
  let f : C(Direction d, Body d) :=
    ⟨fun u => (S u).val 0, (continuous_apply _).comp (continuous_subtype_val.comp hcont)⟩
  refine ⟨f, fun u => ⟨(S u).val, (S u).property.1, (S u).property.2, rfl, ?_⟩⟩
  have coverA := covers_two K (S u).property.1
  have coverB := covers_two K (S (-u)).property.1
  exact unique_lower K μ hvol (-u) _ _ _ _ ((union_comm _ _).trans coverA) coverB
    (reverse_order (hs u)) (hs (-u)) (((S u).property.1.mass_eq_div hμ (S u).property.2 1).trans
      ((S (-u)).property.1.mass_eq_div hμ (S (-u)).property.2 0).symm)

private theorem of_full_support {m : ℕ} (K : Body (m+1)) (μ : Measure (Space (m+1)))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hvol : volume.restrict K.points ≪ μ)
    (hK : 0 < μ.real K.points) (φ : Fin m → C(Body (m+1), ℝ)) :
    AdmitsFairPartition 2 K μ φ := by
  obtain ⟨f, hf⟩ := continuous_half K μ hμ hvol hK
  let g (u : Direction (m+1)) : Space m := WithLp.toLp 2 (fun k => φ k (f u))
  have hg : Continuous g := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun k => (φ k).continuous.comp f.continuous)
  obtain ⟨u, hu⟩ := MathlibExt.Topology.Homotopy.BorsukUlamWanted.borsukUlam g hg
  obtain ⟨S, hp, hm, h0, h1⟩ := hf u
  refine ⟨S, hp, hm, ?_⟩
  intro k i j
  have eq : φ k (S 0) = φ k (S 1) := by
    rw [h0, h1]
    exact congrArg (fun v : Space m => v k) hu
  fin_cases i <;> fin_cases j <;> first | rfl | exact eq | exact eq.symm

/-- Any positive-dimensional compact convex body admits an equal-mass
bisection simultaneously equalizing every one of its d−1 characteristics.
The prescribed density may vanish on open sets. -/
theorem exists_fair_bisection {d : ℕ} (hd : 0 < d) (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ.real K.points)
    (φ : Fin (d - 1) → C(Body d, ℝ)) : AdmitsFairPartition 2 K μ φ := by
  cases d with
  | zero => omega
  | succ m =>
    let ν : Measure (Space (m+1)) := volume.restrict K.points
    letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr K.val.isCompact.measure_lt_top.ne
    have hν : ν ≪ volume := Measure.absolutelyContinuous_restrict
    apply fairPartition_of_positive_background (by decide) K μ ν hμ hν hK φ
    intro c hc
    apply of_full_support K (μ + c • ν) (hμ.add_left (hν.smul_left c))
    · intro s hs
      have hcs : (c • ν) s = 0 := (add_eq_zero.mp (show μ s + (c • ν) s = 0 from hs)).2
      simpa [Measure.smul_apply, ENNReal.smul_def, hc.ne'] using hcs
    · rw [measureReal_add_apply]
      exact add_pos_of_pos_of_nonneg hK measureReal_nonneg

end NRR.Bisection

namespace NRR

/-- The two-piece case of the pointwise classification, with characteristics
on all nonempty compact convex sets as in the classification statement. -/
theorem universalFairness_two {d : ℕ} (hd : 0 < d) (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ K.points) : UniversalFairness 2 K μ := by
  intro φ
  let incl : C(Body d, CompactConvex d) :=
    ⟨Body.toCompactConvex, continuous_subtype_val.subtype_mk _⟩
  exact Bisection.exists_fair_bisection hd K μ hμ (ENNReal.toReal_pos hK.ne' (measure_ne_top _ _))
    (fun k => (φ k).comp incl)

end NRR
