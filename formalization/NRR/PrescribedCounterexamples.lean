import NRR.UniformLayerDataExistence
import NRR.PrescribedTransport

/-! The prescribed-body, prescribed-measure counterexample theorem.
The quantifiers and domain of the characteristics are exactly those of
`NRR.Statement`; no geometric chart or moment hypothesis remains. -/

noncomputable section
open Set Topology MeasureTheory
open NRR.Coordinates NRR.Localization

namespace NRR

theorem prescribedCounterexamples : PrescribedCounterexamples := by
  apply prescribedCounterexamples_of_normalized
  intro q r hn K μ hpr hac hs strip axis
  letI : IsProbabilityMeasure μ := hpr
  have hr : 0 < r := by
    by_contra h
    have eq : r = 0 := by omega
    subst r
    exact hn Nat.prime_two.isPrimePow
  have mass : 0 < μ (bodyPoints K) := by rw [hs]; exact zero_lt_one
  obtain ⟨A,⟨data⟩⟩ := exists_momentCylinder_uniformLayerData hr K μ hac mass strip axis
  exact A.counterexample_of_layerData hn K μ hac mass data

/-- The necessity half of the original pointwise classification is now
unconditional for each prescribed body and measure. -/
theorem universalFairness_implies_primePow (d n : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n)
    (K : Body d) (μ : Measure (Space d)) (hpr : IsProbabilityMeasure μ)
    (hac : μ ≪ volume) (hs : μ K.points = 1) (fair : UniversalFairness n K μ) :
    IsPrimePow n := by
  by_contra hnp
  obtain ⟨φ,reject⟩ := prescribedCounterexamples d n hd hn hnp K μ hpr hac hs
  obtain ⟨S,part,mass,same⟩ := fair φ
  obtain ⟨k,i,j,different⟩ := reject S part mass
  exact different (same k i j)

theorem fullClassification_of_primePowerExistence (positive : PrimePowerExistence) :
    FullClassification :=
  classification_iff.mpr ⟨positive,prescribedCounterexamples⟩

/-- In particular the original six-piece counterexample holds for every
prescribed body and absolutely continuous probability in dimension ≥ 3. -/
theorem prescribedCounterexample_six (d : ℕ) (hd : 3 ≤ d)
    (K : Body d) (μ : Measure (Space d)) (hpr : IsProbabilityMeasure μ)
    (hac : μ ≪ volume) (hs : μ K.points = 1) :
    ∃ φ : Fin (d-1) → C(CompactConvex d,ℝ),
      ∀ S : Fin 6 → Body d,BodyPartition K S → EqualMass μ S →
        ∃ k i j,φ k (S i).toCompactConvex ≠ φ k (S j).toCompactConvex := by
  have hn : ¬ IsPrimePow (6 : ℕ) :=
    (Binomial.halfGcd_eq_one_iff (by norm_num : 2 ≤ 6)).mp (by decide)
  exact prescribedCounterexamples d 6 hd (by norm_num) hn K μ hpr hac hs

end NRR
