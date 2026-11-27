import NRR.PrescribedCounterexamples

/-! Corollaries for finite measures and ambient convex partitions.

The measure may have mass outside the prescribed body. Restricting to the body
and normalizing preserves equal mass of its pieces. Ambient cells need only be
closed and convex; positive mass of their clips supplies full dimensionality.
In the counterexample corollaries the tests are chosen before the partition.
-/

noncomputable section
open Set Topology MeasureTheory
open scoped ENNReal

namespace NRR

/-- Restrict an ambient measure to the prescribed body and normalize its mass. -/
def normalizedRestriction {d : ℕ} (K : Body d) (μ : Measure (Space d)) :
    Measure (Space d) :=
  (μ K.points)⁻¹ • μ.restrict K.points

theorem normalizedRestriction_apply_of_subset {d : ℕ} (K : Body d)
    (μ : Measure (Space d)) {A : Set (Space d)} (hA : A ⊆ K.points) :
    normalizedRestriction K μ A = (μ K.points)⁻¹ * μ A := by
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_eq_self μ hA]

theorem normalizedRestriction_isProbabilityMeasure {d : ℕ} (K : Body d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (hK : 0 < μ K.points) :
    IsProbabilityMeasure (normalizedRestriction K μ) := by
  constructor
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hK.ne' (measure_ne_top _ _)

theorem normalizedRestriction_absolutelyContinuous {d : ℕ} (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume) :
    normalizedRestriction K μ ≪ volume :=
  (Measure.absolutelyContinuous_restrict.trans hac).smul_left _

theorem normalizedRestriction_body_mass {d : ℕ} (K : Body d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (hK : 0 < μ K.points) :
    normalizedRestriction K μ K.points = 1 := by
  rw [normalizedRestriction_apply_of_subset K μ Subset.rfl]
  exact ENNReal.inv_mul_cancel hK.ne' (measure_ne_top _ _)

/-- Restriction and normalization preserve exactly the equal-mass condition
for a partition of the prescribed body. -/
theorem BodyPartition.equalMass_normalizedRestriction_iff {d n : ℕ}
    {K : Body d} {S : Fin n → Body d} (hS : BodyPartition K S)
    {μ : Measure (Space d)} [IsFiniteMeasure μ] (hK : 0 < μ K.points) :
    EqualMass (normalizedRestriction K μ) S ↔ EqualMass μ S := by
  have sub (i : Fin n) : (S i).points ⊆ K.points := by
    rw [← hS.covers]
    exact subset_iUnion (fun j => (S j).points) i
  have mass (i : Fin n) := normalizedRestriction_apply_of_subset K μ (sub i)
  constructor
  · intro hm i j
    have eq := congrArg (fun a : ℝ≥0∞ => μ K.points * a) (hm i j)
    simpa only [mass, ENNReal.mul_inv_cancel_left hK.ne' (measure_ne_top _ _)] using eq
  · intro hm i j
    rw [mass i, mass j, hm i j]

/-- The prescribed counterexample holds for every finite absolutely continuous
ambient measure giving the prescribed body positive mass. Its total mass need
not be one, and its support need not be contained in the body. -/
theorem prescribedCounterexamples_finiteMeasure (d n : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n)
    (hnp : ¬ IsPrimePow n) (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hac : μ ≪ volume) (hK : 0 < μ K.points) :
    ∃ φ : Fin (d - 1) → C(CompactConvex d, ℝ),
      ∀ S : Fin n → Body d, BodyPartition K S → EqualMass μ S →
        ∃ k i j, φ k (S i).toCompactConvex ≠ φ k (S j).toCompactConvex := by
  obtain ⟨φ, reject⟩ := prescribedCounterexamples d n hd hn hnp K
    (normalizedRestriction K μ) (normalizedRestriction_isProbabilityMeasure K μ hK)
    (normalizedRestriction_absolutelyContinuous K μ hac) (normalizedRestriction_body_mass K μ hK)
  exact ⟨φ, fun S hS hm => reject S hS ((hS.equalMass_normalizedRestriction_iff hK).mpr hm)⟩

/-- A finite ambient partition with raw closed convex cells. The cells are
allowed to be unbounded; no clipped bodies are assumed as input. -/
structure AmbientConvexPartition {d n : ℕ} (P : Fin n → Set (Space d)) : Prop where
  closed : ∀ i, IsClosed (P i)
  convex : ∀ i, Convex ℝ (P i)
  covers : (⋃ i, P i) = univ
  disjoint : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))

namespace AmbientConvexPartition

variable {d n : ℕ} {P : Fin n → Set (Space d)}

theorem clipped_covers (hP : AmbientConvexPartition P) (K : Body d) :
    (⋃ i, P i ∩ K.points) = K.points := by
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨i, _, hx⟩
    exact hx
  · intro hx
    obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp hP.covers x
    exact ⟨i, hi, hx⟩

/-- Coverage and equal clipped masses force each mass to be positive. -/
theorem positive_clips_of_equalMass (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hK : 0 < μ K.points)
    (hm : ∀ i j, μ (P i ∩ K.points) = μ (P j ∩ K.points)) :
    ∀ i, 0 < μ (P i ∩ K.points) := by
  intro i
  by_contra! hi
  have hz : μ (P i ∩ K.points) = 0 := le_antisymm hi (zero_le _)
  have hall : ∀ j, μ (P j ∩ K.points) = 0 := fun j => (hm j i).trans hz
  have hnull := measure_iUnion_null hall
  rw [hP.clipped_covers K] at hnull
  exact hK.ne' hnull

/-- Positive absolutely continuous mass makes every closed convex clip a
full-dimensional compact body, even when the ambient cell is unbounded. -/
def clippedBodies (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume)
    (hm : ∀ i, 0 < μ (P i ∩ K.points)) : Fin n → Body d := fun i => by
  have hc : Convex ℝ (P i ∩ K.points) := (hP.convex i).inter K.property.1
  have hclosed : IsClosed (P i ∩ K.points) := (hP.closed i).inter K.val.isCompact.isClosed
  have hi : (interior (P i ∩ K.points)).Nonempty := by
    by_contra! h
    have hf := hac (hc.addHaar_frontier volume)
    rw [frontier, hclosed.closure_eq, h, diff_empty] at hf
    exact (hm i).ne' hf
  exact ⟨⟨⟨P i ∩ K.points, K.val.isCompact.inter_left (hP.closed i)⟩,
    hi.mono interior_subset⟩, hc, hi⟩

@[simp] theorem clippedBodies_points (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume)
    (hm : ∀ i, 0 < μ (P i ∩ K.points)) (i : Fin n) :
    (hP.clippedBodies K μ hac hm i).points = P i ∩ K.points := rfl

theorem clippedBodies_ambientPartition (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume)
    (hm : ∀ i, 0 < μ (P i ∩ K.points)) :
    AmbientPartition K P (hP.clippedBodies K μ hac hm) where
  closed := hP.closed
  convex := hP.convex
  covers := hP.covers
  disjoint := hP.disjoint
  clipped := fun _ => rfl

/-- The actual clipped bodies cover K and have pairwise disjoint interiors. -/
theorem clippedBodies_bodyPartition (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume)
    (hm : ∀ i, 0 < μ (P i ∩ K.points)) :
    BodyPartition K (hP.clippedBodies K μ hac hm) :=
  (hP.clippedBodies_ambientPartition K μ hac hm).toBodyPartition

theorem clippedBodies_equalMass (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume)
    (hpos : ∀ i, 0 < μ (P i ∩ K.points))
    (hm : ∀ i j, μ (P i ∩ K.points) = μ (P j ∩ K.points)) :
    EqualMass μ (hP.clippedBodies K μ hac hpos) := hm

/-- Equal clipped masses suffice to construct a genuine body partition;
positivity follows from the positive mass of K. -/
theorem exists_clipped_partition (hP : AmbientConvexPartition P) (K : Body d)
    (μ : Measure (Space d)) (hac : μ ≪ volume) (hK : 0 < μ K.points)
    (hm : ∀ i j, μ (P i ∩ K.points) = μ (P j ∩ K.points)) :
    ∃ S : Fin n → Body d, AmbientPartition K P S ∧ BodyPartition K S ∧ EqualMass μ S := by
  let hpos := hP.positive_clips_of_equalMass K μ hK hm
  exact ⟨hP.clippedBodies K μ hac hpos, hP.clippedBodies_ambientPartition K μ hac hpos,
    hP.clippedBodies_bodyPartition K μ hac hpos, hP.clippedBodies_equalMass K μ hac hpos hm⟩

end AmbientConvexPartition

/-- One fixed family of tests excludes fairness both for body partitions and
for clips of every ambient finite closed convex partition. The ambient cells
may be unbounded, and no full-dimensionality hypothesis on the clips is needed. -/
theorem prescribedCounterexamples_finiteMeasure_and_ambient (d n : ℕ)
    (hd : 3 ≤ d) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n)
    (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hac : μ ≪ volume) (hK : 0 < μ K.points) :
    ∃ φ : Fin (d - 1) → C(CompactConvex d, ℝ),
      (∀ S : Fin n → Body d, BodyPartition K S → EqualMass μ S →
        ∃ k i j, φ k (S i).toCompactConvex ≠ φ k (S j).toCompactConvex) ∧
      (∀ P : Fin n → Set (Space d), AmbientConvexPartition P →
        (∀ i j, μ (P i ∩ K.points) = μ (P j ∩ K.points)) →
        ∃ S : Fin n → Body d, AmbientPartition K P S ∧ BodyPartition K S ∧
          EqualMass μ S ∧
          ∃ k i j, φ k (S i).toCompactConvex ≠ φ k (S j).toCompactConvex) := by
  obtain ⟨φ, reject⟩ := prescribedCounterexamples_finiteMeasure d n hd hn hnp K μ hac hK
  refine ⟨φ, reject, ?_⟩
  intro P hP hm
  obtain ⟨S, hA, hS, hmass⟩ := hP.exists_clipped_partition K μ hac hK hm
  exact ⟨S, hA, hS, hmass, reject S hS hmass⟩

end NRR
