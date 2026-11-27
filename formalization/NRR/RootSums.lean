import NRR.Surface
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A polynomial certificate for the exceptional fibers of a block reading.
Choose shifts with square roots 1, 2, 4, ... above the origin. With a plane
map satisfying h(z) - h(-z) = 2z, every coincidence forces a nonempty
subsum of the roots to vanish. -/

noncomputable section
open Polynomial Finset Set
open scoped Polynomial.Bivariate

namespace NRR.RootSums

private theorem separate (p : ℂ[X][Y]) (b : ℂ) :
    ∃ u v : ℂ[X][Y], ∀ q y z : ℂ, z ^ 2 = q + b →
      p.evalEval q (y + z) = u.evalEval q y + z * v.evalEval q y := by
  induction p using Polynomial.induction_on with
  | C a => exact ⟨C a, 0, by simp [evalEval_C]⟩
  | add p r hp hr =>
    obtain ⟨u, v, hu⟩ := hp
    obtain ⟨a, c, ha⟩ := hr
    exact ⟨u + a, v + c, fun q y z hz => by
      simp only [evalEval_add, hu q y z hz, ha q y z hz]
      ring⟩
  | monomial n a ih =>
    obtain ⟨u, v, hu⟩ := ih
    refine ⟨Y * u + C (X + C b) * v, u + Y * v, ?_⟩
    intro q y z hz
    rw [pow_succ, ← mul_assoc, evalEval_mul, hu q y z hz]
    simp [evalEval_C]
    linear_combination v.evalEval q y * hz

private theorem eliminate (p : ℂ[X][Y]) (b : ℂ) :
    ∃ r : ℂ[X][Y], ∀ q y z : ℂ, z ^ 2 = q + b →
      r.evalEval q y = p.evalEval q (y + z) * p.evalEval q (y - z) := by
  obtain ⟨u, v, hu⟩ := separate p b
  refine ⟨u ^ 2 - C (X + C b) * v ^ 2, fun q y z hz => ?_⟩
  rw [sub_eq_add_neg y z, hu q y z hz, hu q y (-z) (by simpa using hz)]
  simp only [evalEval_sub, evalEval_pow, evalEval_mul, evalEval_C, eval_add, eval_X, eval_C]
  linear_combination (v.evalEval q y)^2 * hz

variable {ι : Type*}

/-- All sums obtained by independently choosing the signs of the square roots. -/
def IsRootSum (b : ι → ℂ) (s : Finset ι) (q y : ℂ) : Prop :=
  ∃ w : ι → ℂ, (∀ i ∈ s, w i ^ 2 = q + b i) ∧ ∑ i ∈ s, w i = y

private theorem insert_rootSum [DecidableEq ι] {b : ι → ℂ} {s : Finset ι}
    {i : ι} (hi : i ∉ s) {q y z : ℂ} (hz : z ^ 2 = q + b i) :
    IsRootSum b (insert i s) q y ↔ IsRootSum b s q (y + z) ∨ IsRootSum b s q (y - z) := by
  constructor
  · rintro ⟨w, hw, hsum⟩
    rw [sum_insert hi] at hsum
    have hrest := fun j (hj : j ∈ s) => hw j (mem_insert_of_mem hj)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((hw i (mem_insert_self ..)).trans hz.symm) with he | he
    · exact Or.inr ⟨w, hrest, by linear_combination hsum - he⟩
    · exact Or.inl ⟨w, hrest, by linear_combination hsum - he⟩
  · intro h
    have extend (t : ℂ) (ht : t^2 = q + b i) (h : IsRootSum b s q (y - t)) :
        IsRootSum b (insert i s) q y := by
      obtain ⟨w, hw, hsum⟩ := h
      let v := Function.update w i t
      have hv (j : ι) (hj : j ∈ s) : v j = w j :=
        Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
      refine ⟨v, ?_, ?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · simpa [v] using ht
        · rw [hv j hj, hw j hj]
      · rw [sum_insert hi, sum_congr rfl hv, hsum]
        simp [v]
    rcases h with hp | hm
    · exact extend (-z) (by simpa using hz) (by simpa using hp)
    · exact extend z hz hm

/-- Eliminate every square root, keeping the common value and the sum as
indeterminates. The equivalence includes both signs at every step. -/
theorem exists_polynomial (b : ι → ℂ) (s : Finset ι) :
    ∃ p : ℂ[X][Y], ∀ q y, p.evalEval q y = 0 ↔ IsRootSum b s q y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Y, by intro q y; simp [IsRootSum, eq_comm]⟩
  | @insert i s hi ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨r, hr⟩ := eliminate p (b i)
    refine ⟨r, fun q y => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (q + b i) zero_lt_two
    rw [hr q y z hz, mul_eq_zero, hp, hp, insert_rootSum hi hz]

theorem finite_zero_sums (b : ι → ℂ) (s : Finset ι) {q₀ : ℂ}
    (h₀ : ¬ IsRootSum b s q₀ 0) : {q | IsRootSum b s q 0}.Finite := by
  obtain ⟨p, hp⟩ := exists_polynomial b s
  let r : ℂ[X] := p.eval 0
  have hr (q : ℂ) : r.IsRoot q ↔ IsRootSum b s q 0 := by
    simpa [r, Polynomial.IsRoot, evalEval] using hp q 0
  have hne : r ≠ 0 := fun h => h₀ ((hr q₀).mp (by simp [h]))
  exact (finite_setOf_isRoot hne).subset fun q hq => (hr q).mpr hq

/-- The roots at the common value zero have strictly dominating largest magnitude
in every nonempty subcollection. -/
def realShift {m : ℕ} (i : Fin m) : ℝ := ((2 : ℝ) ^ i.val) ^ 2

def shift {m : ℕ} (i : Fin m) : ℂ := (realShift i : ℂ)

private theorem geometric_sum (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 : ℝ)^j = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

theorem zero_not_rootSum {m : ℕ} {s : Finset (Fin m)} (hs : s.Nonempty) :
    ¬ IsRootSum shift s 0 0 := by
  classical
  rintro ⟨w, hw, hsum⟩
  let k := s.max' hs
  have hk : k ∈ s := s.max'_mem hs
  have mags (i : Fin m) (hi : i ∈ s) : ‖w i‖ = (2 : ℝ)^i.val := by
    have he : w i ^ 2 = ((2 : ℂ)^i.val) ^ 2 := by simpa [shift, realShift] using hw i hi
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h <;> simp [h, norm_pow]
  let t := s.erase k
  have ht : t.image Fin.val ⊆ Finset.range k.val := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (s.lt_max'_of_mem_erase_max' hs hi)
  have hsmall : (∑ i ∈ t, ‖w i‖) ≤ 2^k.val - 1 := calc
    ∑ i ∈ t, ‖w i‖ = ∑ i ∈ t, (2 : ℝ)^i.val :=
      sum_congr rfl fun i hi => mags i (mem_of_mem_erase hi)
    _ = ∑ j ∈ t.image Fin.val, (2 : ℝ)^j :=
      (sum_image (f := fun j : ℕ => (2 : ℝ)^j) (fun _ _ _ _ h => Fin.ext h)).symm
    _ ≤ ∑ j ∈ Finset.range k.val, (2 : ℝ)^j :=
      sum_le_sum_of_subset_of_nonneg ht fun _ _ _ => by positivity
    _ = _ := geometric_sum _
  have hneg : (∑ i ∈ t, w i) = - w k := by
    have := sum_erase_add s w hk
    rw [hsum] at this
    exact eq_neg_of_add_eq_zero_left this
  have hle := norm_sum_le t w
  rw [hneg, norm_neg, mags k hk] at hle
  linarith

variable {m : ℕ} [NeZero m]

def rootValue (z : Surface.locus (shift (m := m))) : ℂ := z.val 0 ^ 2 - shift (0 : Fin m)

theorem rootValue_eq (z : Surface.locus (shift (m := m))) (i : Fin m) :
    z.val i ^ 2 = rootValue z + shift i := by
  change _ = (z.val 0 ^ 2 - shift (0 : Fin m)) + shift i
  linear_combination z.property i

private theorem finite_fiber (q : ℂ) :
    (rootValue (m := m) ⁻¹' {q}).Finite := by
  have h (i : Fin m) : {z : ℂ | z^2 = q + shift i}.Finite := by
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (q + shift i) zero_lt_two
    exact ((Set.finite_singleton v).insert (-v)).subset fun z hz => by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans hv.symm) with h | h <;> simp [h]
  have box := (Set.Finite.pi' h).preimage
    (f := (Subtype.val : Surface.locus (shift (m := m)) → Fin m → ℂ)) Subtype.val_injective.injOn
  apply box.subset
  intro z hz i
  exact (rootValue_eq z i).trans (congrArg (· + shift i) hz)

/-- The total of all roots after applying the same angular map. Subtracting
the first summand gives the second coordinate of the block reading. -/
def restSum (h : ℂ ≃ₜ ℂ) : C(Surface.locus (shift (m := m)), ℂ) :=
  ⟨fun z => (∑ i, h (z.val i)) - h (z.val 0), by
    have hc (i : Fin m) : Continuous (fun z : Surface.locus (shift (m := m)) => h (z.val i)) :=
      h.continuous.comp ((continuous_apply i).comp continuous_subtype_val)
    exact (continuous_finset_sum _ fun i _ => hc i).sub (hc 0)⟩

private theorem coincidence_zero_sum (h : ℂ ≃ₜ ℂ) (hodd : ∀ z, h z - h (-z) = 2*z)
    {x y : Surface.locus (shift (m := m))} (hxy : x ≠ y)
    (he : Surface.reading h (restSum h) x = Surface.reading h (restSum h) y) :
    ∃ s : Finset (Fin m), s.Nonempty ∧ IsRootSum shift s (rootValue x) 0 := by
  classical
  have hfirst : h (x.val 0) = h (y.val 0) := congrArg Prod.fst he
  have hq : rootValue x = rootValue y := by unfold rootValue; rw [h.injective hfirst]
  have hrest : (∑ i, h (x.val i)) - h (x.val 0) =
      (∑ i, h (y.val i)) - h (y.val 0) := congrArg Prod.snd he
  have htotal : ∑ i, (h (x.val i) - h (y.val i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    linear_combination hrest + hfirst
  let s := univ.filter (fun i => x.val i ≠ y.val i)
  have hs : s.Nonempty := by
    by_contra! he
    exact hxy (Subtype.ext (funext fun i => by
      by_contra hi
      exact he ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩))
  have hd (i : Fin m) (hi : i ∈ s) : h (x.val i) - h (y.val i) = 2 * x.val i := by
    have hsq := (rootValue_eq x i).trans ((congrArg (· + shift i) hq).trans (rootValue_eq y i).symm)
    have hn := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left (mem_filter.mp hi).2
    rw [show y.val i = -x.val i by rw [hn, neg_neg], hodd]
  have hsums : (∑ i ∈ s, (h (x.val i) - h (y.val i))) = ∑ i, (h (x.val i) - h (y.val i)) :=
    sum_subset (subset_univ s) fun i _ hi => sub_eq_zero.mpr (congrArg h (by
      by_contra hne
      exact hi (mem_filter.mpr ⟨mem_univ _, hne⟩)))
  rw [← hsums, sum_congr rfl hd, ← Finset.mul_sum] at htotal
  exact ⟨s, hs, x.val, fun i _ => rootValue_eq x i, (mul_eq_zero.mp htotal).resolve_left (by norm_num)⟩

/-- For these explicit shifts the exceptional preimages of the two-interface
reading form a finite set, without any generic choice of perturbation. -/
theorem finite_multiple_readings (h : ℂ ≃ₜ ℂ) (hodd : ∀ z, h z - h (-z) = 2*z) :
    {x : Surface.locus (shift (m := m)) | ∃ y, x ≠ y ∧
      Surface.reading h (restSum h) x = Surface.reading h (restSum h) y}.Finite := by
  let A := ⋃ s : {s : Finset (Fin m) // s.Nonempty}, {q | IsRootSum shift s.val q 0}
  have hA : A.Finite := Set.finite_iUnion fun s =>
    finite_zero_sums shift s.val (zero_not_rootSum s.property)
  apply (hA.preimage' (fun q _ => finite_fiber q)).subset
  rintro x ⟨y, hxy, he⟩
  obtain ⟨s, hs, hsum⟩ := coincidence_zero_sum h hodd hxy he
  exact mem_iUnion.mpr ⟨⟨s, hs⟩, hsum⟩

end NRR.RootSums
