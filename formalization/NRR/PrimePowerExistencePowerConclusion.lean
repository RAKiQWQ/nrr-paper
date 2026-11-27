import NRR.PrimePowerExistencePowerWeightsPartition
import NRR.PrimePowerExistenceRegularization

/-! Completion of the analytic implication from the configuration-space
zero theorem to the precise fairness statement. The topological zero theorem
remains an explicit hypothesis: it is not asserted by this module. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace NRR.PrimePower

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The usual sphere-valued obstruction has precisely the zero-map form
needed by the analytic construction. Normalization preserves the actual
permutation action and is continuous on the punctured target. -/
theorem configuration_zero_of_no_equivariant_unitMap
    (noMap : ∀ g : C(Configuration d n,UnitValues d n),
      (∀ (σ : Equiv.Perm (Fin n)) (x : Configuration d n),g (σ • x) = σ • g x) → False)
    (f : C(Configuration d n,ReducedValues d n))
    (equivariant : ∀ (σ : Equiv.Perm (Fin n)) (x : Configuration d n),
      f (σ • x) = σ • f x) : ∃ x,f x = 0 := by
  classical
  by_contra! nonzero
  let g : C(Configuration d n,UnitValues d n) :=
    (unitNormalization d n).comp
      ⟨fun x => ⟨f x,nonzero x⟩,f.continuous.subtype_mk nonzero⟩
  apply noMap g
  intro σ x
  have he := equivariant σ x
  have hn : σ • f x ≠ 0 := he ▸ nonzero (σ • x)
  have hs : (⟨f (σ • x),nonzero (σ • x)⟩ : {v : ReducedValues d n // v ≠ 0}) =
      ⟨σ • f x,hn⟩ := Subtype.ext he
  change unitNormalization d n ⟨f (σ • x),nonzero (σ • x)⟩ =
    σ • unitNormalization d n ⟨f x,nonzero x⟩
  rw [hs]
  exact unitNormalization_equivariant σ (f x) (nonzero x) hn

/-- The actual continuous equal-mass power cells turn a configuration zero
theorem into fairness for measures that dominate restricted ordinary volume. -/
theorem universalFairness_of_configuration_zero_fullSupport
    (zero : ∀ f : C(Configuration d n,ReducedValues d n),
      (∀ (σ : Equiv.Perm (Fin n)) (x : Configuration d n),f (σ • x) = σ • f x) →
        ∃ x,f x = 0)
    (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) : UniversalFairness n K μ := by
  intro φ
  obtain ⟨x,hx⟩ := zero (equalMassPowerTest K μ hμ background mass φ)
    (equalMassPowerTest_equivariant K μ hμ background mass φ)
  exact fairPartition_of_equalMassPowerTest_zero K μ hμ background mass φ x hx

/-- Adding and then removing a positive restricted-volume background gives
fairness for the original arbitrary absolutely continuous finite measure.
The configuration theorem is the sole remaining input. -/
theorem universalFairness_of_configuration_zero
    (zero : ∀ f : C(Configuration d n,ReducedValues d n),
      (∀ (σ : Equiv.Perm (Fin n)) (x : Configuration d n),f (σ • x) = σ • f x) →
        ∃ x,f x = 0)
    (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (mass : 0 < μ K.points) : UniversalFairness n K μ := by
  let ν : Measure (Space d) := volume.restrict K.points
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr K.val.isCompact.measure_lt_top.ne
  have ac : ν ≪ volume := Measure.absolutelyContinuous_restrict
  apply universalFairness_of_positive_background (Nat.pos_of_ne_zero (NeZero.ne n)) K μ ν hμ ac mass
  intro c hc
  have background : volume.restrict K.points ≪ μ + c • ν := background_dominated μ ν hc
  have positive : 0 < (μ+c • ν) K.points := by
    rw [Measure.add_apply]
    exact mass.trans_le (le_add_right le_rfl)
  exact universalFairness_of_configuration_zero_fullSupport zero K (μ+c • ν)
    (hμ.add_left (ac.smul_left c)) background positive

/-- The analytic conclusion can equally consume the standard nonexistence
of an equivariant map to the unit sphere in the reduced representation. -/
theorem universalFairness_of_no_equivariant_unitMap
    (noMap : ∀ g : C(Configuration d n,UnitValues d n),
      (∀ (σ : Equiv.Perm (Fin n)) (x : Configuration d n),g (σ • x) = σ • g x) → False)
    (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (mass : 0 < μ K.points) : UniversalFairness n K μ :=
  universalFairness_of_configuration_zero
    (configuration_zero_of_no_equivariant_unitMap noMap) K μ hμ mass

end NRR.PrimePower

namespace NRR

/-- This is the complete reduction of the original positive goal to the
topological configuration-space zero theorem, with no density lower bound,
selection regularity, or geometric partition hypothesis left over. -/
theorem primePowerExistence_of_configuration_zero
    (zero : ∀ (d n : ℕ),3 ≤ d → 2 ≤ n → IsPrimePow n →
      ∀ f : C(PrimePower.Configuration d n,PrimePower.ReducedValues d n),
        (∀ (σ : Equiv.Perm (Fin n)) (x : PrimePower.Configuration d n),
          f (σ • x) = σ • f x) → ∃ x,f x = 0) :
    PrimePowerExistence := by
  intro d n hd hn hp K μ hpr hac hs
  letI : IsProbabilityMeasure μ := hpr
  letI : NeZero n := ⟨by omega⟩
  apply PrimePower.universalFairness_of_configuration_zero (zero d n hd hn hp) K μ hac
  rw [hs]
  exact zero_lt_one

end NRR
