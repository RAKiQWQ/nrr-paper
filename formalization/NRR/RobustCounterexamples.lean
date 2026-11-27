import NRR.PrescribedCounterexamples
import NRR.CylinderPartitionLimits
import NRR.PrimePowerLimit

/-! Unconditional counterexamples to the original conjectures and their
stability under small errors in the prescribed masses. -/

noncomputable section
open Set Topology MeasureTheory Filter Metric
open scoped ENNReal

namespace NRR

/-- The closed unit ball in three-dimensional Euclidean space. -/
def counterexampleUnitBall : Body 3 :=
  ⟨⟨⟨closedBall (0 : Space 3) 1, isCompact_closedBall _ _⟩,
      ⟨0, mem_closedBall_self zero_le_one⟩⟩,
    convex_closedBall _ _,
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩⟩

/-- Restriction of the compact-convex characteristics to full-dimensional bodies. -/
def bodyCharacteristics {d : ℕ} (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) :
    Fin (d - 1) → C(Body d, ℝ) :=
  fun k => (φ k).comp ⟨Body.toCompactConvex, continuous_subtype_val.subtype_mk _⟩

/-- The uniform probability on the three-dimensional unit ball admits a
six-piece obstruction with two continuous characteristics. -/
theorem uniformUnitBall_six_noFairPartition :
    ∃ φ : Fin 2 → C(Body 3, ℝ),
      ¬ AdmitsFairPartition 6 counterexampleUnitBall (Localization.uniformBase 1) φ := by
  let μ := Localization.uniformBase (d := 3) 1
  obtain ⟨φ, reject⟩ := prescribedCounterexample_six 3 (by norm_num)
    counterexampleUnitBall μ (Localization.uniformBase_probability zero_lt_one)
    (Localization.uniformBase_ac 1) (Localization.uniformBase_full zero_lt_one)
  refine ⟨bodyCharacteristics φ, ?_⟩
  rintro ⟨S, hp, hm, hv⟩
  obtain ⟨k, i, j, different⟩ := reject S hp hm
  exact different (hv k i j)

theorem not_bodyGeneralizedNRR : ¬ BodyGeneralizedNRR := by
  intro claim
  let μ := Localization.uniformBase (d := 3) 1
  letI : IsProbabilityMeasure μ := Localization.uniformBase_probability zero_lt_one
  obtain ⟨φ, reject⟩ := uniformUnitBall_six_noFairPartition
  exact reject (claim 3 6 (by norm_num) (by norm_num) counterexampleUnitBall μ inferInstance
    (IsProbabilityMeasure.ne_zero μ) (Localization.uniformBase_ac 1) φ)

theorem not_generalizedNRR : ¬ GeneralizedNRR := by
  intro claim
  obtain ⟨φ, reject⟩ := uniformUnitBall_six_noFairPartition
  exact reject (ambient_implies_body (claim 3 6 (by norm_num) (by norm_num) counterexampleUnitBall
    (Localization.uniformBase 1) (Localization.uniformBase_probability zero_lt_one)
    (Localization.uniformBase_ac 1) φ))

/-- Absence of an exactly fair partition gives one positive tolerance which
separates the characteristic values of every sufficiently mass-balanced partition. -/
theorem robustCounterexample_of_noFairPartition {d n : ℕ} (K : Body d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (φ : Fin (d - 1) → C(Body d, ℝ)) {a : ℝ} (ha : 0 < a)
    (reject : ¬ AdmitsFairPartition n K μ φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S : Fin n → Body d, BodyPartition K S →
      (∀ i, |μ.real (S i).points - a| < ε) →
      ∃ k i j, ε < |φ k (S i) - φ k (S j)| := by
  classical
  by_contra! h
  let e (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  have he (m : ℕ) : 0 < e m := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose A hA hm hv using fun m => h (e m) (he m)
  apply reject
  apply fairPartition_of_convergent_errors K μ hμ φ A hA ha
  · intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using
      squeeze_zero (fun m => abs_nonneg (μ.real (A m i).points - a))
        (fun m => (hm m i).le) he0
  · intro k i j
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using
      squeeze_zero (fun m => abs_nonneg (φ k (A m i) - φ k (A m j)))
        (fun m => hv m k i j) he0

/-- For each prescribed body and absolutely continuous probability, the same
`d - 1` continuous characteristics obstruct every partition whose actual masses
are sufficiently close to `1 / n`, by a uniform positive characteristic gap. -/
theorem prescribedRobustCounterexamples (d n : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n)
    (hnp : ¬ IsPrimePow n) (K : Body d) (μ : Measure (Space d))
    (hpr : IsProbabilityMeasure μ) (hac : μ ≪ volume) (hs : μ K.points = 1) :
    ∃ φ : Fin (d - 1) → C(CompactConvex d, ℝ), ∃ ε : ℝ, 0 < ε ∧
      ∀ S : Fin n → Body d, BodyPartition K S →
        (∀ i, |μ.real (S i).points - 1 / (n : ℝ)| < ε) →
        ∃ k i j, ε < |φ k (S i).toCompactConvex - φ k (S j).toCompactConvex| := by
  letI : IsProbabilityMeasure μ := hpr
  obtain ⟨φ, reject⟩ := prescribedCounterexamples d n hd hn hnp K μ hpr hac hs
  have unfair : ¬ AdmitsFairPartition n K μ (bodyCharacteristics φ) := by
    rintro ⟨S, hp, hm, hv⟩
    obtain ⟨k, i, j, different⟩ := reject S hp hm
    exact different (hv k i j)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨ε, hε, robust⟩ := robustCounterexample_of_noFairPartition K μ hac
    (bodyCharacteristics φ) (one_div_pos.mpr hn') unfair
  exact ⟨φ, ε, hε, robust⟩

end NRR
