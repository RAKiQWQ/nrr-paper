import NRR.BallAdditiveMoments

/-! Two rational polynomials of moments together with `d-3` genuine
rational polynomial volume integrals obstruct every equal-mass partition. -/

noncomputable section
open Set Topology MeasureTheory Metric TopologicalSpace
open scoped ENNReal
open NRR.PolynomialMomentSeparation

namespace NRR.BallAdditiveMoments

/-- Exactly two general moment polynomials, followed by individual
polynomial volume integrals. -/
def mixedPolynomialCharacteristic {q : ℕ}
    (P : Fin 2 → MvPolynomial (MultiIndex (q+3)) ℚ)
    (Q : Fin q → MvPolynomial (Fin (q+3)) ℚ) :
    Fin (q+2) → C(CompactConvex (q+3),ℝ) :=
  Fin.cases (momentPolynomialCharacteristic (P 0))
    (Fin.cases (momentPolynomialCharacteristic (P 1))
      (fun k => ⟨fun C => polynomialMoment (Q k) (C.val : Set (Space (q+3))),
        ConvexLimits.continuous_integral_of_locallyIntegrable volume volume
          Measure.AbsolutelyContinuous.rfl (polynomialEvaluation (Q k)).continuous.locallyIntegrable⟩))

@[simp] theorem mixedPolynomialCharacteristic_tail {q : ℕ}
    (P : Fin 2 → MvPolynomial (MultiIndex (q+3)) ℚ)
    (Q : Fin q → MvPolynomial (Fin (q+3)) ℚ) (k : Fin q) (C : CompactConvex (q+3)) :
    mixedPolynomialCharacteristic P Q k.succ.succ C =
      ∫ x in (C.val : Set (Space (q+3))), polynomialEvaluation (Q k) x ∂volume := rfl

/-- The manuscript's mixed polynomial form holds for every prescribed
body and absolutely continuous probability.  Only the first two tests are
arbitrary polynomials of moments; every remaining test is additive. -/
theorem prescribed_mixedPolynomial_counterexamples (q r : ℕ)
    (hn : ¬ IsPrimePow (r+2)) (K : Body (q+3)) (μ : Measure (Space (q+3)))
    (hpr : IsProbabilityMeasure μ) (hac : μ ≪ volume) (hs : μ K.points = 1) :
    ∃ (P : Fin 2 → MvPolynomial (MultiIndex (q+3)) ℚ)
      (Q : Fin q → MvPolynomial (Fin (q+3)) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ S : Fin (r+2) → Body (q+3), BodyPartition K S → EqualMass μ S →
        ∃ a i j, γ < |mixedPolynomialCharacteristic P Q a (S i).toCompactConvex -
          mixedPolynomialCharacteristic P Q a (S j).toCompactConvex| := by
  classical
  letI : IsProbabilityMeasure μ := hpr
  obtain ⟨φ,f,hfi,tail,reject⟩ := prescribed_integrable_counterexample q r hn K μ hpr hac hs
  let s := {S : Fin (r+2) → Body (q+3) | BodyPartition K S ∧ EqualMass μ S}
  have compactS : IsCompact s := compact_equalMassPartitions K μ hac (by rw [hs]; exact zero_lt_one)
  obtain ⟨ε,hε,gap⟩ := RationalMomentApproximation.continuous_uniform_gap
    (fun i a => (φ a).comp (GlobalAssembly.partitionCell i)) s compactS
    (fun S hS => by
      obtain ⟨a,i,j,hij⟩ := reject S hS.1 hS.2
      exact ⟨i,j,a,hij⟩)
  let m : ℝ≥0∞ := μ K.points / (r+2)
  have hm : 0 < m := ENNReal.div_pos (by rw [hs]; exact one_ne_zero) (by simp)
  let Y : Set (Body (q+3)) := {C | C.points ⊆ K.points ∧ m ≤ μ C.points}
  have compactY : IsCompact Y := CompactTests.compact_cells K μ hac hm
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp compactY
  let toCompact : C(Y,CompactConvex (q+3)) :=
    ⟨fun C => C.val.toCompactConvex,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let coordinates : MultiIndex (q+3) → C(Y,ℝ) := fun α =>
    (ordinaryMomentCharacteristic α).comp toCompact
  have separate : ∀ C D : Y, C ≠ D → ∃ α, coordinates α C ≠ coordinates α D := by
    intro C D hCD
    obtain ⟨α,hα⟩ := exists_ordinaryMoment_ne C.val D.val (fun he => hCD (Subtype.ext he))
    exact ⟨α,hα⟩
  let front : Fin 2 → Fin (q+2) := fun a => ⟨a.val,by omega⟩
  have approximate (a : Fin 2) :=
    RationalMomentApproximation.exists_rational_polynomial_near_coordinates coordinates separate
      ((φ (front a)).comp toCompact) (show 0 < ε/4 by positivity)
  choose P hP using approximate
  choose Q hQ using fun k : Fin q => exists_polynomial_near_integrals K (f k) (hfi k)
    (show 0 < ε/4 by positivity)
  have approximation (a : Fin (q+2)) (C : Y) :
      |mixedPolynomialCharacteristic P Q a C.val.toCompactConvex -
        φ a C.val.toCompactConvex| < ε/4 := by
    refine Fin.cases ?_ (fun b => Fin.cases ?_ (fun k => ?_) b) a
    · exact hP 0 C
    · exact hP 1 C
    · rw [mixedPolynomialCharacteristic_tail,tail]
      exact hQ k C.val.points C.val.val.isCompact.isClosed.measurableSet C.property.1
  refine ⟨P,Q,ε/2,by positivity,fun S part mass => ?_⟩
  have inY (i : Fin (r+2)) : S i ∈ Y := by
    refine ⟨?_,?_⟩
    rw [← part.covers]
    · exact subset_iUnion (fun j => (S j).points) i
    · simpa [m] using (part.mass_eq_div hac mass i).ge
  obtain ⟨i,j,a,hij⟩ := gap S ⟨part,mass⟩
  refine ⟨a,i,j,?_⟩
  have hi := approximation a ⟨S i,inY i⟩
  have hj := approximation a ⟨S j,inY j⟩
  have h₁ := dist_triangle (φ a (S i).toCompactConvex)
    (mixedPolynomialCharacteristic P Q a (S i).toCompactConvex) (φ a (S j).toCompactConvex)
  have h₂ := dist_triangle (mixedPolynomialCharacteristic P Q a (S i).toCompactConvex)
    (mixedPolynomialCharacteristic P Q a (S j).toCompactConvex) (φ a (S j).toCompactConvex)
  simp only [ContinuousMap.comp_apply,GlobalAssembly.partitionCell,ContinuousMap.coe_mk] at hij
  simp only [Real.dist_eq] at h₁ h₂
  rw [abs_sub_comm] at hi
  linarith

/-- On the honest Euclidean unit ball, all actual equal-probability convex
partitions are excluded by the same mixed family and positive gap. -/
theorem unitBall_mixedPolynomial_counterexamples (q r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ (P : Fin 2 → MvPolynomial (MultiIndex (q+3)) ℚ)
      (Q : Fin q → MvPolynomial (Fin (q+3)) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ S : Fin (r+2) → Body (q+3), BodyPartition (ordinaryUnitBall (q+3)) S →
        EqualMass (Localization.uniformBase (d := q+3) 1) S →
        ∃ a i j, γ < |mixedPolynomialCharacteristic P Q a (S i).toCompactConvex -
          mixedPolynomialCharacteristic P Q a (S j).toCompactConvex| :=
  prescribed_mixedPolynomial_counterexamples q r hn (ordinaryUnitBall (q+3))
    (Localization.uniformBase 1) (Localization.uniformBase_probability zero_lt_one)
    (Localization.uniformBase_ac 1) (Localization.uniformBase_full zero_lt_one)

end NRR.BallAdditiveMoments
