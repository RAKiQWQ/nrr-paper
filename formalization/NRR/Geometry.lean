import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Closeds

/-! Euclidean convex equipartitions. The two conjectures below are propositions
specifying the ambient-partition and body-partition formulations. -/

noncomputable section
open Set MeasureTheory TopologicalSpace

namespace NRR

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The subspace of full-dimensional convex bodies with the Hausdorff metric. -/
abbrev Body (d : ℕ) := {s : NonemptyCompacts (Space d) //
  Convex ℝ (s : Set (Space d)) ∧ (interior (s : Set (Space d))).Nonempty}

def Body.points {d : ℕ} (K : Body d) : Set (Space d) := K.val

/-- A convex partition of the body itself. Subset containment follows from coverage. -/
structure BodyPartition {d n : ℕ} (K : Body d) (S : Fin n → Body d) : Prop where
  covers : (⋃ i, (S i).points) = K.points
  disjoint : Pairwise fun i j => Disjoint (interior (S i).points) (interior (S j).points)

/-- An ambient convex partition whose intersections with K are the given parts. -/
structure AmbientPartition {d n : ℕ} (K : Body d)
    (P : Fin n → Set (Space d)) (S : Fin n → Body d) : Prop where
  closed : ∀ i, IsClosed (P i)
  convex : ∀ i, Convex ℝ (P i)
  covers : (⋃ i, P i) = univ
  disjoint : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))
  clipped : ∀ i, (S i).points = P i ∩ K.points

def EqualMass {d n : ℕ} (μ : Measure (Space d)) (S : Fin n → Body d) : Prop :=
  ∀ i j, μ (S i).points = μ (S j).points

def EqualValues {d n : ℕ} (φ : Fin (d - 1) → C(Body d, ℝ)) (S : Fin n → Body d) : Prop :=
  ∀ k i j, φ k (S i) = φ k (S j)

def AdmitsFairPartition {d : ℕ} (n : ℕ) (K : Body d) (μ : Measure (Space d))
    (φ : Fin (d - 1) → C(Body d, ℝ)) : Prop :=
  ∃ S : Fin n → Body d, BodyPartition K S ∧ EqualMass μ S ∧ EqualValues φ S

def AdmitsAmbientFairPartition {d : ℕ} (n : ℕ) (K : Body d) (μ : Measure (Space d))
    (φ : Fin (d - 1) → C(Body d, ℝ)) : Prop :=
  ∃ (P : Fin n → Set (Space d)) (S : Fin n → Body d),
    AmbientPartition K P S ∧ EqualMass μ S ∧ EqualValues φ S

def GeneralizedNRR : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 2 ≤ n → ∀ (K : Body d) (μ : Measure (Space d)),
    IsProbabilityMeasure μ → μ ≪ volume →
    ∀ φ : Fin (d - 1) → C(Body d, ℝ), AdmitsAmbientFairPartition n K μ φ

def BodyGeneralizedNRR : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 2 ≤ n → ∀ (K : Body d) (μ : Measure (Space d)),
    IsFiniteMeasure μ → μ ≠ 0 → μ ≪ volume →
    ∀ φ : Fin (d - 1) → C(Body d, ℝ), AdmitsFairPartition n K μ φ

theorem AmbientPartition.toBodyPartition {d n : ℕ} {K : Body d}
    {P : Fin n → Set (Space d)} {S : Fin n → Body d} (h : AmbientPartition K P S) :
    BodyPartition K S where
  covers := by
    ext x
    simp only [mem_iUnion, h.clipped, mem_inter_iff]
    constructor
    · rintro ⟨i, _, hx⟩
      exact hx
    · intro hx
      obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp h.covers x
      exact ⟨i, hi, hx⟩
  disjoint := by
    intro i j hij
    rw [h.clipped i, h.clipped j]
    exact (h.disjoint hij).mono (interior_mono inter_subset_left) (interior_mono inter_subset_left)

theorem ambient_implies_body {d n : ℕ} {K : Body d} {μ : Measure (Space d)}
    {φ : Fin (d - 1) → C(Body d, ℝ)} :
    AdmitsAmbientFairPartition n K μ φ → AdmitsFairPartition n K μ φ := by
  rintro ⟨P, S, hP, hm, hv⟩
  exact ⟨S, hP.toBodyPartition, hm, hv⟩

end NRR
