import NRR.PrimePowerTopologyMinimalWedge

/-! Continuous retractions of the genuine lowest Fuks stratum onto each
compactified Euclidean cell. These maps are defined on the actual skeleton
by its proved topological quotient presentation. -/

noncomputable section
open Set Topology
open scoped OnePoint
open NRR.PrimePower

namespace NRR.PrimePowerTopology

private def minimalPinchOnSum (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    C(MinimalSphereSum d n, OnePoint (Space d × heightChamber n σ)) := by
  classical
  refine ⟨fun p => if h : p.1 = σ then h ▸ p.2 else ∞, ?_⟩
  apply continuous_sigma
  intro τ
  by_cases h : τ = σ
  · subst τ
    simpa only [dif_pos rfl] using
      (continuous_id : Continuous (fun p : OnePoint (Space d × heightChamber n σ) => p))
  · simpa only [dif_neg h] using
      (continuous_const : Continuous
        (fun _ : OnePoint (Space d × heightChamber n τ) =>
          (∞ : OnePoint (Space d × heightChamber n σ))))

private theorem minimalPinchOnSum_infty (d n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    minimalPinchOnSum d n σ ⟨τ, ∞⟩ = ∞ := by
  classical
  by_cases h : τ = σ
  · subst τ
    simp [minimalPinchOnSum]
  · simp [minimalPinchOnSum, h]

private theorem minimalPinchOnSum_factors {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    Function.FactorsThrough (minimalPinchOnSum d n σ) (minimalWedgeProjection i₀) := by
  intro p q h
  rcases (minimalWedgeProjection_fiber i₀ p q).mp h with rfl | ⟨hp, hq⟩
  · rfl
  · rcases p with ⟨τ,p⟩
    rcases q with ⟨υ,q⟩
    dsimp only at hp hq
    subst p
    subst q
    exact (minimalPinchOnSum_infty d n σ τ).trans
      (minimalPinchOnSum_infty d n σ υ).symm

/-- Collapse every other actual cell to the shared point at infinity. -/
def minimalCellRetraction {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    C(minimalSkeleton d n, OnePoint (Space d × heightChamber n σ)) :=
  (isQuotientMap_minimalWedgeProjection i₀).lift (minimalPinchOnSum d n σ)
    (minimalPinchOnSum_factors i₀ σ)

private theorem minimalCellRetraction_on_sum {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (p : MinimalSphereSum d n) :
    minimalCellRetraction i₀ σ (minimalWedgeProjection i₀ p) =
      minimalPinchOnSum d n σ p := by
  exact congrArg (fun f : C(MinimalSphereSum d n,
    OnePoint (Space d × heightChamber n σ)) => f p)
      ((isQuotientMap_minimalWedgeProjection i₀).lift_comp
        (minimalPinchOnSum d n σ) (minimalPinchOnSum_factors i₀ σ))

@[simp] theorem minimalCellRetraction_same {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (p : OnePoint (Space d × heightChamber n σ)) :
    minimalCellRetraction i₀ σ (minimalCellInclusion i₀ σ p) = p := by
  classical
  change minimalCellRetraction i₀ σ
    (minimalWedgeProjection i₀ ⟨σ,p⟩) = p
  rw [minimalCellRetraction_on_sum]
  simp [minimalPinchOnSum]

@[simp] theorem minimalCellRetraction_other {d n : ℕ}
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) (hne : τ ≠ σ)
    (p : OnePoint (Space d × heightChamber n τ)) :
    minimalCellRetraction i₀ σ (minimalCellInclusion i₀ τ p) = ∞ := by
  classical
  change minimalCellRetraction i₀ σ
    (minimalWedgeProjection i₀ ⟨τ,p⟩) = ∞
  rw [minimalCellRetraction_on_sum]
  simp [minimalPinchOnSum, hne]

theorem minimalCellInclusion_retraction {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (minimalCellRetraction (d := d) i₀ σ).comp (minimalCellInclusion i₀ σ) =
      ContinuousMap.id _ := by
  ext p
  exact minimalCellRetraction_same i₀ σ p

end NRR.PrimePowerTopology
