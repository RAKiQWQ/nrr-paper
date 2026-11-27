import NRR.PlanarExistence
import Mathlib.Data.Nat.Choose.Factorization

/-!
# The range of total end windings

The algebraic index `totalIndex` is distinguished from the winding of the
actual residual on the square-root surface.  Arbitrary integer half-profiles
are realized by `AngularMap.realize_degreeProfile`; the residual winding
certificate then identifies the two totals on every sufficiently large end
boundary.  Thus the range statement below concerns precisely this family of
constructions, with its even central degree, rather than all plane maps.
-/

open Finset Topology
open scoped unitInterval
noncomputable section

namespace NRR.Binomial

/-- GCD of the entire internal binomial row. -/
def internalChooseGcd (n : ℕ) : ℕ := (Ioo 0 n).gcd n.choose

theorem halfGcd_dvd_internal_choose {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    halfGcd n ∣ n.choose j := by
  by_cases h : j ≤ n / 2
  · exact Finset.gcd_dvd (mem_Icc.mpr ⟨hj, h⟩)
  · rw [← Nat.choose_symm hjn.le]
    exact Finset.gcd_dvd (mem_Icc.mpr ⟨by omega, by omega⟩)

theorem internalChooseGcd_eq_halfGcd (n : ℕ) : internalChooseGcd n = halfGcd n := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro j hj
    obtain ⟨hl, hu⟩ := mem_Icc.mp hj
    exact Finset.gcd_dvd (mem_Ioo.mpr ⟨hl, by omega⟩)
  · exact Finset.dvd_gcd fun j hj =>
      halfGcd_dvd_internal_choose (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2

/-- A prime-power row has GCD exactly the underlying prime, including its
full central coefficient. -/
theorem halfGcd_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    halfGcd (p ^ a) = p := by
  have hn : 2 ≤ p ^ a := (hp.two_le.trans (Nat.le_self_pow ha.ne' p))
  have hdiv : halfGcd (p ^ a) ∣ p ^ a := by
    simpa using (Finset.gcd_dvd (f := (p ^ a).choose)
      (mem_Icc.mpr ⟨by omega, by omega⟩ : 1 ∈ halfIndices (p ^ a)))
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hpd : p ∣ halfGcd (p ^ a) := by
    apply Finset.dvd_gcd
    intro j hj
    obtain ⟨hl, hu⟩ := mem_Icc.mp hj
    exact hp.dvd_choose_pow (by omega) (by omega)
  have hpow : p ^ (a - 1) * p = p ^ a := by
    rw [← pow_succ, Nat.sub_add_cancel ha]
  have hinner : p ^ (a - 1) ∈ halfIndices (p ^ a) := by
    apply mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
    · have h := Nat.mul_le_mul_left (p ^ (a - 1)) hp.two_le
      rw [hpow] at h
      omega
  have hle : p ^ (a - 1) ≤ p ^ a := by
    have := (mem_Icc.mp hinner).2
    omega
  have hval : ((p ^ a).choose (p ^ (a - 1))).factorization p = 1 := by
    rw [Nat.factorization_choose_prime_pow hp hle (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_pow_self hp]
    omega
  have hb1 : b ≤ 1 := by
    rw [← hval]
    apply (hp.pow_dvd_iff_le_factorization (Nat.choose_pos hle).ne').mp
    rw [← hb]
    exact Finset.gcd_dvd hinner
  have hb0 : b ≠ 0 := by
    intro h
    rw [hb, h, pow_zero] at hpd
    exact hp.not_dvd_one hpd
  rw [hb, show b = 1 by omega, pow_one]

theorem internalChooseGcd_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    internalChooseGcd (p ^ a) = p := by
  rw [internalChooseGcd_eq_halfGcd, halfGcd_prime_pow hp ha]

/-- Integer Bezout coefficients for a finite natural row. -/
private theorem exists_gcd_combination (s : Finset ℕ) (b : ℕ → ℕ) :
    ∃ a : ℕ → ℤ, ∑ j ∈ s, a j * b j = (s.gcd b : ℕ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨a, ha⟩ := ih
    let x := Nat.gcdA (b j) (s.gcd b)
    let y := Nat.gcdB (b j) (s.gcd b)
    refine ⟨fun k => if k = j then x else y * a k, ?_⟩
    simp only [sum_insert hj]
    have hs : (∑ k ∈ s, (if k = j then x else y * a k) * b k) =
        y * ∑ k ∈ s, a k * b k := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [if_neg (show k ≠ j from fun e => hj (e ▸ hk)), mul_assoc]
    rw [hs, ha, Finset.gcd_insert]
    simpa [x, y, mul_comm] using (Nat.gcd_eq_gcd_ab (b j) (s.gcd b)).symm

/-- The algebraic total associated with an arbitrary integer half-profile. -/
def totalIndex (n : ℕ) (a : ℕ → ℤ) : ℤ :=
  1 + ∑ j ∈ halfIndices n, a j * n.choose j

theorem totalIndex_mem_coset (n : ℕ) (a : ℕ → ℤ) :
    ∃ k : ℤ, totalIndex n a = 1 + (halfGcd n : ℤ) * k := by
  have hd : (halfGcd n : ℤ) ∣ ∑ j ∈ halfIndices n, a j * (n.choose j : ℤ) := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (Finset.gcd_dvd hj)) _
  obtain ⟨k, hk⟩ := hd
  exact ⟨k, congrArg (1 + ·) hk⟩

theorem exists_totalIndex_eq (n : ℕ) (k : ℤ) :
    ∃ a : ℕ → ℤ, totalIndex n a = 1 + (halfGcd n : ℤ) * k := by
  obtain ⟨a, ha⟩ := exists_gcd_combination (halfIndices n) n.choose
  refine ⟨fun j => k * a j, ?_⟩
  simp only [totalIndex, mul_assoc, ← Finset.mul_sum, ha]
  change 1 + k * (halfGcd n : ℤ) = _
  ring

/-- The index range is the affine lattice `1 + gcd_internal_choose(n) ℤ`. -/
theorem range_totalIndex (n : ℕ) :
    Set.range (totalIndex n) = {z | ∃ k : ℤ, z = 1 + (internalChooseGcd n : ℤ) * k} := by
  rw [internalChooseGcd_eq_halfGcd]
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact totalIndex_mem_coset n a
  · rintro ⟨k, rfl⟩
    exact exists_totalIndex_eq n k

/-- The actual sign representatives have this algebraic total. -/
theorem sum_end_degrees (r : ℕ) (a : ℕ → ℤ) :
    (∑ S : Finset (Fin r),
      (degreeProfile (r+2) a (S.card+1) + degreeProfile (r+2) a (S.card+2))) =
        totalIndex (r+2) a := by
  have h := twice_end_sum r (degreeProfile (r+2) a)
    (fun j hj => degreeProfile_symm (r+2) a hj)
  rw [degreeProfile_sum] at h
  change 2 * _ = 2 * totalIndex (r+2) a at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

end NRR.Binomial

namespace NRR.EndWindingRange

open Surface LocalModel Binomial Filter

/-- A realized member of the angular construction with `r+2` blocks. -/
structure Profile (r : ℕ) (a : ℕ → ℤ) where
  map : ℂ ≃ₜ ℂ
  map_zero : map 0 = 0
  antipodal : ∀ z, map z - map (-z) = 2*z
  homogeneous : ∀ t : ℝ, 0 < t → ∀ z, map ((t : ℂ)*z) = (t : ℂ)*map z
  straight_injective : ∀ t : I, Function.Injective (fun z => straightAction map (t,z))
  avoid : ∀ z ≠ 0, ∀ j ≤ r+2, branchSum map (r+2) j z ≠ 0
  degrees : ∀ j (hj : j ≤ r+2), complexWinding (branchLoop map (r+2) j)
    (fun u => avoid u u.coe_ne_zero j hj) = (degreeProfile (r+2) a j : ℝ)

theorem exists_profile (r : ℕ) (a : ℕ → ℤ) : Nonempty (Profile r a) := by
  obtain ⟨h, avoid, hzero, hdiff, hhom, hinj, degrees⟩ :=
    AngularMap.realize_degreeProfile (by omega : 2 ≤ r+2) a
  exact ⟨⟨h, hzero, hdiff, hhom, hinj, avoid, degrees⟩⟩

/-- The integer prescribed on each actual sign-labelled end, counted once
by fixing its first root positive. -/
def endDegree (r : ℕ) (a : ℕ → ℤ) (c : EndLabel (r+1)) : ℤ :=
  degreeProfile (r+2) a (positiveCount c.val+1) +
    degreeProfile (r+2) a (positiveCount c.val)

theorem sum_endDegree (r : ℕ) (a : ℕ → ℤ) :
    (∑ c : EndLabel (r+1), endDegree r a c) = totalIndex (r+2) a := by
  simp only [endDegree, positiveCount_eq_mask]
  calc
    _ = ∑ S : Finset (Fin r),
        (degreeProfile (r+2) a (S.card+1+1) + degreeProfile (r+2) a (S.card+1)) :=
      (labelMask r).sum_comp _
    _ = ∑ S : Finset (Fin r),
        (degreeProfile (r+2) a (S.card+1) + degreeProfile (r+2) a (S.card+2)) := by
      apply sum_congr rfl
      intro S _
      exact add_comm _ _
    _ = totalIndex (r+2) a := sum_end_degrees r a

/-- The loop is the actual unscaled residual on an actual boundary circle
of the simultaneous-square-root surface with the construction's shifts. -/
def actualEndLoop (r : ℕ) (h : ℂ ≃ₜ ℂ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1)
    (c : EndLabel (r+1)) : C(Circle, ℂ) :=
  ((residual (m := r+1) h).restrict _).comp
    (boundaryCircle (endBoundaryHomeomorph (RootSums.shift (m := r+1)) ht hs) c)

/-- A total of actual nonvanishing end-loop windings.  The real-valued
winding implementation is compared with an integer, without rounding. -/
def HasActualTotal (r : ℕ) (h : ℂ ≃ₜ ℂ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1) (z : ℤ) : Prop :=
  ∃ hn : ∀ c : EndLabel (r+1), ∀ u, actualEndLoop r h ht hs c u ≠ 0,
    (∑ c : EndLabel (r+1), complexWinding (actualEndLoop r h ht hs c) (hn c)) =
      (z : ℝ)

/-- The residual winding certificate applies to every integer profile,
independently of whether its total is zero. -/
theorem Profile.exists_end_certificate {r : ℕ} {a : ℕ → ℤ} (P : Profile r a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε →
      ∀ (hs : ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1)
        (c : EndLabel (r+1)),
      ∃ hn : ∀ u, actualEndLoop r P.map ht hs c u ≠ 0,
        complexWinding (actualEndLoop r P.map ht hs c) hn = (endDegree r a c : ℝ) := by
  obtain ⟨ε, hε, hw⟩ := exists_actual_residual_winding P.map P.map_zero P.homogeneous
    (straightAction P.map) P.straight_injective
    (fun z => by simp [straightAction]) (fun z => by simp [straightAction])
    P.avoid (RootSums.shift (m := r+1))
  refine ⟨ε, hε, fun t ht hsmall hs c => ?_⟩
  obtain ⟨hn, hwind⟩ := hw t ht hsmall c.val (actualEndLoop r P.map ht hs c)
    (fun _ => rfl)
  refine ⟨hn, ?_⟩
  rw [hwind, P.degrees _ (by have := positiveCount_le c.val; omega),
    P.degrees _ (by have := positiveCount_le c.val; omega)]
  exact (Int.cast_add _ _).symm

/-- Every sufficiently small inverse radius gives actual nonvanishing
boundary loops, with total equal to the algebraic index. -/
theorem Profile.exists_actual_total {r : ℕ} {a : ℕ → ℤ} (P : Profile r a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε →
      ∃ hs : ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1,
        HasActualTotal r P.map ht hs (totalIndex (r+2) a) := by
  obtain ⟨ε, hε, hcert⟩ := P.exists_end_certificate
  have near : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuousAt_id.pow 2).mul continuousAt_const).eventually_lt
      continuousAt_const (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨min ε δ, lt_min hε hδ, fun t ht hsmall => ?_⟩
  have hs : ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1 :=
    hball (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using
      hsmall.trans_le (min_le_right ε δ))
  have hc := hcert t ht (hsmall.trans_le (min_le_left ε δ)) hs
  choose hn hw using hc
  refine ⟨hs, hn, ?_⟩
  rw [sum_congr rfl (fun c _ => hw c), ← Int.cast_sum, sum_endDegree]

/-- The eventual total on actual boundaries for some member of the
construction.  The radius condition requires actual nonvanishing loops
for every sufficiently large boundary, so this is not an abstract index set. -/
def actualTotals (r : ℕ) : Set ℤ :=
  {z | ∃ (a : ℕ → ℤ) (P : Profile r a),
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε →
      ∃ hs : ∀ i : Fin (r+1), t^2 * ‖RootSums.shift i‖ < 1,
        HasActualTotal r P.map ht hs z}

/-- The geometric range and the algebraic range coincide. -/
theorem actualTotals_eq_range (r : ℕ) :
    actualTotals r = Set.range (totalIndex (r+2)) := by
  ext z
  constructor
  · rintro ⟨a, P, ε, hε, hactual⟩
    obtain ⟨δ, hδ, hindex⟩ := P.exists_actual_total
    let t := min ε δ / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hsmall : t < min ε δ := by dsimp [t] at ht ⊢; linarith
    obtain ⟨hs, hn, hz⟩ := hactual t ht (hsmall.trans_le (min_le_left ε δ))
    obtain ⟨hs', hn', ha⟩ := hindex t ht (hsmall.trans_le (min_le_right ε δ))
    have he : (totalIndex (r+2) a : ℝ) = (z : ℝ) := ha.symm.trans hz
    exact ⟨a, Int.cast_injective he⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨P⟩ := exists_profile r a
    exact ⟨a, P, P.exists_actual_total⟩

/-- All and only the integers in `1 + gcd_internal_choose(r+2) ℤ`
occur as actual total end windings in this construction. -/
theorem actualTotals_eq_coset (r : ℕ) :
    actualTotals r =
      {z | ∃ k : ℤ, z = 1 + (internalChooseGcd (r+2) : ℤ) * k} := by
  rw [actualTotals_eq_range, range_totalIndex]

theorem actualTotals_eq_coset_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    actualTotals (n-2) =
      {z | ∃ k : ℤ, z = 1 + (internalChooseGcd n : ℤ) * k} := by
  simpa only [Nat.sub_add_cancel hn] using actualTotals_eq_coset (n-2)

theorem actualTotals_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    actualTotals (p^a-2) = {z | ∃ k : ℤ, z = 1 + (p : ℤ) * k} := by
  rw [actualTotals_eq_coset_of_two_le (hp.two_le.trans (Nat.le_self_pow ha.ne' p)),
    internalChooseGcd_prime_pow hp ha]

theorem actualTotals_non_prime_pow (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    actualTotals r = Set.univ := by
  rw [actualTotals_eq_coset, internalChooseGcd_eq_halfGcd,
    (halfGcd_eq_one_iff (by omega : 2 ≤ r+2)).mpr hn]
  ext z
  simp only [Set.mem_setOf_eq, Nat.cast_one, one_mul, Set.mem_univ, iff_true]
  exact ⟨z-1, by ring⟩

theorem zero_mem_actualTotals_iff (r : ℕ) :
    0 ∈ actualTotals r ↔ ¬ IsPrimePow (r+2) := by
  constructor
  · intro hz hpow
    obtain ⟨p, a, hp, ha, he⟩ := (isPrimePow_nat_iff _).mp hpow
    rw [actualTotals_eq_coset, ← he, internalChooseGcd_prime_pow hp ha] at hz
    obtain ⟨k, hk⟩ := hz
    have hd : (p : ℤ) ∣ 1 := ⟨-k, by nlinarith only [hk]⟩
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hd)
  · intro hn
    rw [actualTotals_non_prime_pow r hn]
    exact Set.mem_univ _

/-- The concrete half-profile from the six-block example. -/
def sixProfile (j : ℕ) : ℤ := if j = 3 then 1 else -1

theorem six_degree_row :
    (List.range 7).map (degreeProfile 6 sixProfile) = [1,-1,-1,2,-1,-1,1] := by
  decide

theorem six_totalIndex : totalIndex 6 sixProfile = 0 := by
  decide

/-- These are the sixteen actual sign representatives, with their prescribed
end degrees.  Their realization as actual windings follows from the end
certificate, without identifying a formal degree with winding by definition. -/
theorem six_end_multiplicities :
    ((univ : Finset (EndLabel 5)).filter (fun c => endDegree 4 sixProfile c = -2)).card = 5 ∧
    ((univ : Finset (EndLabel 5)).filter (fun c => endDegree 4 sixProfile c = 1)).card = 10 ∧
    ((univ : Finset (EndLabel 5)).filter (fun c => endDegree 4 sixProfile c = 0)).card = 1 := by
  decide

/-- The six-block multiplicities hold for actual residual windings on
every sufficiently large boundary of a constructed surface. -/
theorem six_actual_multiplicities :
    ∃ P : Profile 4 sixProfile, ∃ ε : ℝ, 0 < ε ∧
      ∀ (t : ℝ) (ht : 0 < t), t < ε →
        ∃ (hs : ∀ i : Fin 5, t^2 * ‖RootSums.shift i‖ < 1)
          (hn : ∀ c : EndLabel 5, ∀ u, actualEndLoop 4 P.map ht hs c u ≠ 0),
          ((univ : Finset (EndLabel 5)).filter (fun c =>
            complexWinding (actualEndLoop 4 P.map ht hs c) (hn c) = -2)).card = 5 ∧
          ((univ : Finset (EndLabel 5)).filter (fun c =>
            complexWinding (actualEndLoop 4 P.map ht hs c) (hn c) = 1)).card = 10 ∧
          ((univ : Finset (EndLabel 5)).filter (fun c =>
            complexWinding (actualEndLoop 4 P.map ht hs c) (hn c) = 0)).card = 1 := by
  classical
  obtain ⟨P⟩ := exists_profile 4 sixProfile
  obtain ⟨ε, hε, hc⟩ := P.exists_end_certificate
  obtain ⟨δ, hδ, htots⟩ := P.exists_actual_total
  refine ⟨P, min ε δ, lt_min hε hδ, fun t ht hsmall => ?_⟩
  obtain ⟨hs, _⟩ := htots t ht (hsmall.trans_le (min_le_right ε δ))
  choose hn hw using hc t ht (hsmall.trans_le (min_le_left ε δ)) hs
  have hfilter (k : ℤ) :
      ((univ : Finset (EndLabel 5)).filter (fun c =>
        complexWinding (actualEndLoop 4 P.map ht hs c) (hn c) = (k : ℝ))) =
      ((univ : Finset (EndLabel 5)).filter (fun c => endDegree 4 sixProfile c = k)) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hw, Int.cast_inj]
  refine ⟨hs, hn, ?_⟩
  have hneg := congrArg Finset.card (hfilter (-2))
  have hone := congrArg Finset.card (hfilter 1)
  have hzero := congrArg Finset.card (hfilter 0)
  norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero] at hneg hone hzero
  rw [hneg, hone, hzero]
  exact six_end_multiplicities

end NRR.EndWindingRange
