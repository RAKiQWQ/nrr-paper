import NRR.PolynomialMomentSeparation
import NRR.RobustCounterexamples

/-! Finite ordinary-volume-moment polynomial counterexamples. The result
holds for every prescribed body and absolutely continuous probability;
the uniform unit-ball statement is a direct specialization. -/

noncomputable section
open Set Topology Metric MeasureTheory TopologicalSpace
open scoped ENNReal

namespace NRR.PolynomialMomentSeparation

/-- A genuine polynomial in finitely many ordinary monomial volume moments,
defined continuously on all nonempty compact convex sets. -/
def momentPolynomialCharacteristic {d : ℕ} (p : MvPolynomial (MultiIndex d) ℚ) :
    C(CompactConvex d, ℝ) :=
  ⟨fun C => RationalMomentApproximation.eval p
    (fun α => ordinaryMoment α (C.val : Set (Space d))),
    (RationalMomentApproximation.continuous_eval p).comp
      (continuous_pi fun α => (ordinaryMomentCharacteristic α).continuous)⟩

/-- The same global characteristic with an explicit finite list of ordinary
moment inputs. -/
def finiteMomentPolynomialCharacteristic {d m : ℕ} (α : Fin m → MultiIndex d)
    (p : MvPolynomial (Fin m) ℚ) : C(CompactConvex d, ℝ) :=
  ⟨fun C => RationalMomentApproximation.eval p
    (fun j => ordinaryMoment (α j) (C.val : Set (Space d))),
    (RationalMomentApproximation.continuous_eval p).comp
      (continuous_pi fun j => (ordinaryMomentCharacteristic (α j)).continuous)⟩

theorem finiteMomentPolynomialCharacteristic_eq_rename {d m : ℕ}
    (α : Fin m → MultiIndex d) (p : MvPolynomial (Fin m) ℚ) :
    finiteMomentPolynomialCharacteristic α p =
      momentPolynomialCharacteristic (MvPolynomial.rename α p) := by
  ext C
  simp only [finiteMomentPolynomialCharacteristic, momentPolynomialCharacteristic,
    ContinuousMap.coe_mk, RationalMomentApproximation.eval, MvPolynomial.eval₂_rename,
    Function.comp_def]

/-- Every finite family uses a single explicitly finite list of distinct
ordinary moment coordinates. -/
theorem exists_finite_momentPresentation {d k : ℕ}
    (P : Fin k → MvPolynomial (MultiIndex d) ℚ) :
    ∃ (m : ℕ) (α : Fin m → MultiIndex d), Function.Injective α ∧
      ∃ Q : Fin k → MvPolynomial (Fin m) ℚ,
        ∀ a, momentPolynomialCharacteristic (P a) = finiteMomentPolynomialCharacteristic α (Q a) := by
  classical
  let s : Finset (MultiIndex d) := Finset.univ.biUnion (fun a => (P a).vars)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let α : Fin (Fintype.card s) → MultiIndex d := fun i => (e.symm i).val
  have hα : Function.Injective α := by
    intro i j he
    apply e.symm.injective
    exact Subtype.ext he
  have hrange (a : Fin k) : ↑(P a).vars ⊆ Set.range α := by
    intro β hβ
    have hsβ : β ∈ s := Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hβ⟩
    refine ⟨e ⟨β, hsβ⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨β, hsβ⟩)
  have hQ (a : Fin k) := MvPolynomial.exists_rename_eq_of_vars_subset_range (P a) α hα (hrange a)
  choose Q hQ using hQ
  refine ⟨Fintype.card s, α, hα, Q, ?_⟩
  intro a
  rw [finiteMomentPolynomialCharacteristic_eq_rename, hQ a]

/-- Every prescribed counterexample can be chosen to consist of rational
polynomials of finitely many ordinary volume moments, while retaining a
strict positive gap over all actual equal-mass convex partitions. -/
theorem prescribed_momentPolynomial_counterexamples (d n : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n)
    (hnp : ¬ IsPrimePow n) (K : Body d) (μ : Measure (Space d))
    (hpr : IsProbabilityMeasure μ) (hac : μ ≪ volume) (hs : μ K.points = 1) :
    ∃ (P : Fin (d-1) → MvPolynomial (MultiIndex d) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ S : Fin n → Body d, BodyPartition K S → EqualMass μ S →
        ∃ a i j, γ < |momentPolynomialCharacteristic (P a) (S i).toCompactConvex -
          momentPolynomialCharacteristic (P a) (S j).toCompactConvex| := by
  classical
  letI : IsProbabilityMeasure μ := hpr
  obtain ⟨φ, ε, hε, gap⟩ := prescribedRobustCounterexamples d n hd hn hnp K μ hpr hac hs
  let m : ℝ≥0∞ := μ K.points / n
  have hm : 0 < m := ENNReal.div_pos (by rw [hs]; exact one_ne_zero) (by simp)
  let Y : Set (Body d) := {C | C.points ⊆ K.points ∧ m ≤ μ C.points}
  have compactY : IsCompact Y := CompactTests.compact_cells K μ hac hm
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp compactY
  let toCompact : C(Y, CompactConvex d) :=
    ⟨fun C => C.val.toCompactConvex,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let coordinates : MultiIndex d → C(Y, ℝ) := fun α =>
    (ordinaryMomentCharacteristic α).comp toCompact
  have separate : ∀ C D : Y, C ≠ D → ∃ α, coordinates α C ≠ coordinates α D := by
    intro C D hCD
    obtain ⟨α, hα⟩ := exists_ordinaryMoment_ne C.val D.val (fun he => hCD (Subtype.ext he))
    exact ⟨α, hα⟩
  have approximate (a : Fin (d-1)) :=
    RationalMomentApproximation.exists_rational_polynomial_near_coordinates
      coordinates separate ((φ a).comp toCompact) (by positivity : 0 < ε/4)
  choose P hP using approximate
  have approximation (a : Fin (d-1)) (C : Y) :
      |momentPolynomialCharacteristic (P a) C.val.toCompactConvex -
        φ a C.val.toCompactConvex| < ε/4 := by
    simpa only [momentPolynomialCharacteristic, ContinuousMap.coe_mk,
      ContinuousMap.comp_apply, coordinates, ordinaryMomentCharacteristic, toCompact,
      Body.toCompactConvex, Body.points] using hP a C
  refine ⟨P, ε/2, by positivity, ?_⟩
  intro S part mass
  have inY (i : Fin n) : S i ∈ Y := by
    refine ⟨?_, (part.mass_eq_div hac mass i).ge⟩
    rw [← part.covers]
    exact subset_iUnion (fun j => (S j).points) i
  have realMass (i : Fin n) : μ.real (S i).points = 1 / (n : ℝ) := by
    simp only [measureReal_def, part.mass_eq_div hac mass i, hs,
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
  obtain ⟨a, i, j, hij⟩ := gap S part (fun i => by rw [realMass i]; simpa using hε)
  refine ⟨a, i, j, ?_⟩
  have hi := approximation a ⟨S i, inY i⟩
  have hj := approximation a ⟨S j, inY j⟩
  have h₁ := dist_triangle (φ a (S i).toCompactConvex)
    (momentPolynomialCharacteristic (P a) (S i).toCompactConvex)
    (φ a (S j).toCompactConvex)
  have h₂ := dist_triangle (momentPolynomialCharacteristic (P a) (S i).toCompactConvex)
    (momentPolynomialCharacteristic (P a) (S j).toCompactConvex)
    (φ a (S j).toCompactConvex)
  simp only [Real.dist_eq] at h₁ h₂
  rw [abs_sub_comm] at hi
  linarith

/-- The honest unit ball as a full-dimensional compact convex body. -/
def ordinaryUnitBall (d : ℕ) : Body d :=
  ⟨⟨⟨closedBall (0 : Space d) 1, isCompact_closedBall _ _⟩,
      ⟨0, mem_closedBall_self zero_le_one⟩⟩,
    convex_closedBall _ _,
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩⟩

/-- The manuscript's ordinary-volume-moment polynomial version on the
uniform unit ball, in every dimension and every non-prime-power cell count. -/
theorem unitBall_momentPolynomial_counterexamples (d n : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n)
    (hnp : ¬ IsPrimePow n) :
    ∃ (P : Fin (d-1) → MvPolynomial (MultiIndex d) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ S : Fin n → Body d, BodyPartition (ordinaryUnitBall d) S →
        EqualMass (Localization.uniformBase (d := d) 1) S →
        ∃ a i j, γ < |momentPolynomialCharacteristic (P a) (S i).toCompactConvex -
          momentPolynomialCharacteristic (P a) (S j).toCompactConvex| :=
  prescribed_momentPolynomial_counterexamples d n hd hn hnp (ordinaryUnitBall d)
    (Localization.uniformBase 1) (Localization.uniformBase_probability zero_lt_one)
    (Localization.uniformBase_ac 1) (Localization.uniformBase_full zero_lt_one)

/-- The ordinary-moment counterexample with all its finite inputs exposed:
the input list and rational polynomials are chosen before the partition. -/
theorem prescribed_finite_momentPolynomial_counterexamples (d n : ℕ)
    (hd : 3 ≤ d) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n)
    (K : Body d) (μ : Measure (Space d))
    (hpr : IsProbabilityMeasure μ) (hac : μ ≪ volume) (hs : μ K.points = 1) :
    ∃ (m : ℕ) (α : Fin m → MultiIndex d) (P : Fin (d-1) → MvPolynomial (Fin m) ℚ)
      (γ : ℝ), Function.Injective α ∧ 0 < γ ∧
      ∀ S : Fin n → Body d, BodyPartition K S → EqualMass μ S →
        ∃ a i j, γ < |finiteMomentPolynomialCharacteristic α (P a) (S i).toCompactConvex -
          finiteMomentPolynomialCharacteristic α (P a) (S j).toCompactConvex| := by
  obtain ⟨P, γ, hγ, reject⟩ := prescribed_momentPolynomial_counterexamples d n hd hn hnp K μ hpr hac hs
  obtain ⟨m, α, hα, Q, hQ⟩ := exists_finite_momentPresentation P
  refine ⟨m, α, Q, γ, hα, hγ, ?_⟩
  intro S part mass
  obtain ⟨a, i, j, hij⟩ := reject S part mass
  exact ⟨a, i, j, by simpa only [hQ a] using hij⟩

theorem unitBall_finite_momentPolynomial_counterexamples (d n : ℕ)
    (hd : 3 ≤ d) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n) :
    ∃ (m : ℕ) (α : Fin m → MultiIndex d) (P : Fin (d-1) → MvPolynomial (Fin m) ℚ)
      (γ : ℝ), Function.Injective α ∧ 0 < γ ∧
      ∀ S : Fin n → Body d, BodyPartition (ordinaryUnitBall d) S →
        EqualMass (Localization.uniformBase (d := d) 1) S →
        ∃ a i j, γ < |finiteMomentPolynomialCharacteristic α (P a) (S i).toCompactConvex -
          finiteMomentPolynomialCharacteristic α (P a) (S j).toCompactConvex| :=
  prescribed_finite_momentPolynomial_counterexamples d n hd hn hnp (ordinaryUnitBall d)
    (Localization.uniformBase 1) (Localization.uniformBase_probability zero_lt_one)
    (Localization.uniformBase_ac 1) (Localization.uniformBase_full zero_lt_one)

end NRR.PolynomialMomentSeparation
