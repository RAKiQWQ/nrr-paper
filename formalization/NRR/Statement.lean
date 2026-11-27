import NRR.Geometry
import Mathlib.Algebra.IsPrimePow

/-! The statement being verified is kept separate from the individual proof lemmas. -/

open MeasureTheory TopologicalSpace

namespace NRR

/-- All nonempty compact convex sets, with the induced Hausdorff topology.
Lower-dimensional sets are allowed in the domain of each characteristic. -/
abbrev CompactConvex (d : ℕ) :=
  {C : NonemptyCompacts (Space d) // Convex ℝ (C : Set (Space d))}

def Body.toCompactConvex {d : ℕ} (K : Body d) : CompactConvex d := ⟨K.val, K.property.1⟩

/-- The negative direction in the manuscript, including its order of quantification.
This definition specifies the goal and does not assert a proof. -/
def PrescribedCounterexamples : Prop :=
  ∀ (d n : ℕ), 3 ≤ d → 2 ≤ n → ¬ IsPrimePow n →
    ∀ (K : Body d) (μ : Measure (Space d)), IsProbabilityMeasure μ →
      μ ≪ volume → μ K.points = 1 →
      ∃ φ : Fin (d - 1) → C(CompactConvex d, ℝ),
        ∀ S : Fin n → Body d, BodyPartition K S → EqualMass μ S →
          ∃ k i j, φ k (S i).toCompactConvex ≠ φ k (S j).toCompactConvex

/-- For this particular body and probability, all choices of the characteristics
admit a fair partition. -/
def UniversalFairness {d : ℕ} (n : ℕ) (K : Body d) (μ : Measure (Space d)) : Prop :=
  ∀ φ : Fin (d - 1) → C(CompactConvex d, ℝ), ∃ S : Fin n → Body d,
    BodyPartition K S ∧ EqualMass μ S ∧
    ∀ k i j, φ k (S i).toCompactConvex = φ k (S j).toCompactConvex

/-- The classification in dimensions at least three, pointwise in both K and μ. -/
def FullClassification : Prop :=
  ∀ (d n : ℕ), 3 ≤ d → 2 ≤ n →
    ∀ (K : Body d) (μ : Measure (Space d)), IsProbabilityMeasure μ →
      μ ≪ volume → μ K.points = 1 → (UniversalFairness n K μ ↔ IsPrimePow n)

def PrimePowerExistence : Prop :=
  ∀ (d n : ℕ), 3 ≤ d → 2 ≤ n → IsPrimePow n →
    ∀ (K : Body d) (μ : Measure (Space d)), IsProbabilityMeasure μ →
      μ ≪ volume → μ K.points = 1 → UniversalFairness n K μ

theorem classification_iff : FullClassification ↔ PrimePowerExistence ∧ PrescribedCounterexamples := by
  classical
  constructor
  · intro h
    constructor
    · intro d n hd hn hp K μ hpr hac hs
      exact (h d n hd hn K μ hpr hac hs).mpr hp
    · intro d n hd hn hp K μ hpr hac hs
      have hbad := mt (h d n hd hn K μ hpr hac hs).mp hp
      unfold UniversalFairness at hbad
      push_neg at hbad
      simpa only [and_imp] using hbad
  · rintro ⟨pos, neg⟩ d n hd hn K μ hpr hac hs
    refine ⟨fun h => ?_, fun hp => pos d n hd hn hp K μ hpr hac hs⟩
    by_contra hp
    obtain ⟨φ, hφ⟩ := neg d n hd hn hp K μ hpr hac hs
    obtain ⟨S, hS, hm, he⟩ := h φ
    obtain ⟨k, i, j, hij⟩ := hφ S hS hm
    exact hij (he k i j)

end NRR
