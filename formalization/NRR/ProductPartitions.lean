import NRR.Coordinates
import NRR.Partitions

/-! Compactness of the actual equal-mass partition space in product
coordinates. No positivity assumption on the density is introduced. -/

noncomputable section
open Set Topology MeasureTheory
open scoped ENNReal

namespace NRR.Coordinates

section Compactness

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)]

def equalMassPartitions {n : ℕ} (K : ConvexBody F) (μ : Measure F) :
    Set (Fin n → ConvexBody F) :=
  {S | Partition K S ∧ ∀ i j, μ (bodyPoints (S i)) = μ (bodyPoints (S j))}

/-- A continuous linear coordinate change transfers compactness of the
entire partition space, including every possible closed convex cell. -/
theorem compact_equalMassPartitions {m n : ℕ} (e : Space m ≃L[ℝ] F)
    (K : ConvexBody F) (μ : Measure F) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K)) :
    IsCompact (equalMassPartitions (n := n) K μ) := by
  let K₀ : Body m := bodiesHomeomorph e.symm K
  let μ₀ : Measure (Space m) := μ.map e.symm
  have ac : μ₀ ≪ volume :=
    map_absolutelyContinuous_haar e.symm μ volume volume hμ
  have mass : 0 < μ₀ K₀.points := by
    change 0 < (μ.map e.symm) (bodyPoints (bodiesHomeomorph e.symm K))
    rwa [map_body_mass]
  let H : (Fin n → Body m) ≃ₜ (Fin n → ConvexBody F) :=
    Homeomorph.piCongrRight (fun _ => bodiesHomeomorph e)
  have hc := (NRR.compact_equalMassPartitions (n := n) K₀ μ₀ ac mass).image H.continuous
  convert hc using 1
  ext S
  constructor
  · rintro ⟨hp,hm⟩
    let T : Fin n → Body m := fun i => bodiesHomeomorph e.symm (S i)
    have hpT : BodyPartition K₀ T :=
      (bodyPartition_iff_partition K₀ T).mpr (hp.map e.symm)
    have hmT : EqualMass μ₀ T := (equalMass_map_iff e.symm μ S).mpr hm
    refine ⟨T,⟨hpT,hmT⟩,?_⟩
    funext i
    exact (bodiesHomeomorph e).apply_symm_apply (S i)
  · rintro ⟨T,⟨hp,hm⟩,rfl⟩
    have hpT := ((bodyPartition_iff_partition K₀ T).mp hp).map e
    have parent : bodiesHomeomorph e K₀ = K :=
      (bodiesHomeomorph e).apply_symm_apply K
    refine ⟨parent ▸ hpT,?_⟩
    have hm' := (equalMass_map_iff e μ₀ T).mpr hm
    have μeq : μ₀.map e = μ := by
      rw [show μ₀ = μ.map e.symm from rfl,
        Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
      simpa only [Function.comp_def,e.apply_symm_apply] using (Measure.map_id : μ.map id = μ)
    simpa only [μeq] using hm'

omit [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)] in
/-- Forgetting full dimensionality is a continuous map into the space on
which the requested single-cell characteristics are defined. -/
theorem continuous_bodyToConvexCompact :
    Continuous (bodyToConvexCompact (E := F)) :=
  continuous_subtype_val.subtype_mk _

def convexConfigurations {n : ℕ} (S : Fin n → ConvexBody F) :
    Fin n → ConvexLimits.ConvexCompact F := fun i => bodyToConvexCompact (S i)

omit [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)] in
theorem continuous_convexConfigurations {n : ℕ} :
    Continuous (convexConfigurations (F := F) (n := n)) :=
  continuous_pi fun i => continuous_bodyToConvexCompact.comp (continuous_apply i)

theorem compact_convexConfigurations {m n : ℕ} (e : Space m ≃L[ℝ] F)
    (K : ConvexBody F) (μ : Measure F) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K)) :
    IsCompact (convexConfigurations '' equalMassPartitions (n := n) K μ) :=
  (compact_equalMassPartitions e K μ hμ hK).image continuous_convexConfigurations

theorem Partition.mass_eq_sum {n : ℕ} {K : ConvexBody F} {S : Fin n → ConvexBody F}
    (hp : Partition K S) (μ : Measure F) (hμ : μ ≪ volume) :
    μ (bodyPoints K) = ∑ i, μ (bodyPoints (S i)) := by
  have nullBoundary (i : Fin n) : μ (frontier (bodyPoints (S i))) = 0 :=
    hμ ((S i).property.1.addHaar_frontier volume)
  have hd : Pairwise (fun i j => AEDisjoint μ (bodyPoints (S i)) (bodyPoints (S j))) := by
    intro i j hij
    apply measure_mono_null _ (measure_union_null (nullBoundary i) (nullBoundary j))
    intro x hx
    by_cases hi : x ∈ interior (bodyPoints (S i))
    · exact Or.inr ⟨subset_closure hx.2, fun hj => Set.disjoint_left.mp (hp.disjoint hij) hi hj⟩
    · exact Or.inl ⟨subset_closure hx.1, hi⟩
  rw [← hp.covers, measure_iUnion₀ hd (fun i =>
    (S i).val.isCompact.isClosed.measurableSet.nullMeasurableSet), tsum_fintype]

theorem Partition.mass_eq_div {n : ℕ} {K : ConvexBody F} {S : Fin n → ConvexBody F}
    (hp : Partition K S) (μ : Measure F) (hμ : μ ≪ volume)
    (hm : ∀ i j, μ (bodyPoints (S i)) = μ (bodyPoints (S j))) (j : Fin n) :
    μ (bodyPoints (S j)) = μ (bodyPoints K) / n := by
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_le j.val |>.trans_lt j.isLt)
  have sum_eq : μ (bodyPoints K) = (n : ℝ≥0∞) * μ (bodyPoints (S j)) := by
    calc
      _ = ∑ i, μ (bodyPoints (S i)) := hp.mass_eq_sum μ hμ
      _ = ∑ _i : Fin n, μ (bodyPoints (S j)) := Finset.sum_congr rfl (fun i _ => hm i j)
      _ = _ := by simp [nsmul_eq_mul]
  rw [sum_eq, mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast hn) (by simp)]

end Compactness

end NRR.Coordinates
