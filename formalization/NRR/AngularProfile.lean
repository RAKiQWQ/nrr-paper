import NRR.AngularLoops

/-! Actual antipodal half-paths with prescribed indices at finitely many punctures. -/

open Set Topology
open scoped unitInterval Classical
noncomputable section

namespace NRR.AngularLoops

open Surface

/-- The two affine copies of the interval used in an antipodal doubling. -/
def firstHalf (t : I) : I := ⟨t.val/2, by constructor <;> linarith [t.2.1,t.2.2]⟩

def secondHalf (t : I) : I := ⟨(t.val+1)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩

theorem periodPath_secondHalf (t : I) :
    (periodPath (secondHalf t) : ℂ) = -(periodPath (firstHalf t) : ℂ) := by
  change (Circle.exp (2*Real.pi*((t.val+1)/2)) : ℂ) =
    -(Circle.exp (2*Real.pi*(t.val/2)) : ℂ)
  rw [show 2*Real.pi*((t.val+1)/2) = Real.pi + 2*Real.pi*(t.val/2) by ring,
    Circle.exp_add, Circle.coe_mul]
  rw [show (Circle.exp Real.pi : ℂ) = -1 from Complex.exp_pi_mul_I, neg_one_mul]

/-- Each circle point has a parameter in one of the two half-period copies. -/
theorem exists_half_parameter (u : Circle) :
    ∃ t : I, u = periodPath (firstHalf t) ∨ u = periodPath (secondHalf t) := by
  obtain ⟨s, rfl⟩ := periodPath_surjective u
  by_cases hs : s.val ≤ 1/2
  · let t : I := ⟨2*s.val, by constructor <;> linarith [s.2.1]⟩
    refine ⟨t, Or.inl (congrArg periodPath (Subtype.ext ?_))⟩
    change s.val = (2*s.val)/2
    ring
  · let t : I := ⟨2*s.val-1, by constructor <;> linarith [s.2.2]⟩
    refine ⟨t, Or.inr (congrArg periodPath (Subtype.ext ?_))⟩
    change s.val = ((2*s.val-1)+1)/2
    ring

theorem doubled_firstHalf {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {a : region Q}
    (p : Path a (reflect hQ a)) (t : I) :
    doubled hQ p (firstHalf t) = p t := by
  let q := (p.map (reflect hQ).continuous).cast rfl (Subtype.ext (neg_neg _).symm)
  have h := Path.extend_trans_of_le_half p q (t := t.val/2)
    (by linarith [t.2.2])
  rw [show 2*(t.val/2) = t.val by ring] at h
  change (p.trans q).extend (firstHalf t).val = p.extend t.val at h
  rw [Path.extend_extends _ (firstHalf t).property, Path.extend_extends _ t.property] at h
  exact h

theorem doubled_secondHalf {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {a : region Q}
    (p : Path a (reflect hQ a)) (t : I) :
    doubled hQ p (secondHalf t) = reflect hQ (p t) := by
  let q := (p.map (reflect hQ).continuous).cast rfl (Subtype.ext (neg_neg _).symm)
  have h := Path.extend_trans_of_half_le p q (t := (t.val+1)/2)
    (by linarith [t.2.1])
  rw [show 2*((t.val+1)/2)-1 = t.val by ring] at h
  change (p.trans q).extend (secondHalf t).val = q.extend t.val at h
  rw [Path.extend_extends _ (secondHalf t).property, Path.extend_extends _ t.property] at h
  exact h

private theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i ∈ S, δ < f i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1/2, by norm_num, by norm_num, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨δ, hδ, h1, hd⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hmin : 0 < min δ (f i) := lt_min hδ hfi
    have hhalf : min δ (f i) / 2 < min δ (f i) := by linarith
    refine ⟨min δ (f i) / 2, by positivity,
      (hhalf.trans_le (min_le_left _ _)).trans h1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hhalf.trans_le (min_le_right _ _)
    · exact (hhalf.trans_le (min_le_left _ _)).trans (hd j hj)

/-- A single positive radius works for all access paths, all small turning
circles, and the central closing half-turn. -/
theorem exists_profile_radius (Q S : Finset ℝ) (inside : ∀ c ∈ S, |c| < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (∀ c ∈ S, |c| + δ < 1) ∧
      (∀ c ∈ S, ∀ q ∈ Q, q ≠ c → δ < |q-c|) ∧
      (∀ q ∈ Q, q ≠ 0 → δ < |q|) := by
  obtain ⟨a, ha, ha1, hA⟩ := finite_positive_lower_bound S (fun c => 1 - |c|)
    (fun c hc => sub_pos.mpr (inside c hc))
  let sep (p : ℝ × ℝ) : ℝ := if p.2 = p.1 then 1 else |p.2-p.1|
  have sep_pos (p : ℝ × ℝ) (_ : p ∈ S ×ˢ Q) : 0 < sep p := by
    dsimp [sep]
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨b, hb, _, hB⟩ := finite_positive_lower_bound (S ×ˢ Q) sep sep_pos
  let gap (q : ℝ) : ℝ := if q = 0 then 1 else |q|
  have gap_pos (q : ℝ) (_ : q ∈ Q) : 0 < gap q := by
    dsimp [gap]
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr h
  obtain ⟨c, hc, _, hC⟩ := finite_positive_lower_bound Q gap gap_pos
  let δ := min a (min b c)
  have δa : δ ≤ a := min_le_left _ _
  have δb : δ ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have δc : δ ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, by dsimp [δ]; positivity, δa.trans_lt ha1, ?_, ?_, ?_⟩
  · intro x hx
    have := δa.trans_lt (hA x hx)
    linarith
  · intro x hx y hy hne
    have h := δb.trans_lt (hB (x,y) (Finset.mem_product.mpr ⟨hx,hy⟩))
    simpa [sep, hne] using h
  · intro q hq hne
    have h := δc.trans_lt (hC q hq)
    simpa [gap, hne] using h

/-- Insert the chosen based excursions before the closing half-turn.  Doubling
the resulting half-path realizes the reflected sum of the local prescriptions,
with one clockwise turn at the central puncture. -/
theorem exists_half_profile (Q S : Finset ℝ) (hQ : ∀ q ∈ Q, -q ∈ Q)
    (w : ℝ → ℤ) (δ : ℝ) (hδ : 0 < δ) (h1 : δ < 1)
    (inside : ∀ c ∈ S, |c| + δ < 1)
    (sep : ∀ c ∈ S, ∀ q ∈ Q, q ≠ c → δ < |q-c|)
    (sep0 : ∀ q ∈ Q, q ≠ 0 → δ < |q|) :
    ∃ p : Path (top Q 0 δ (by norm_num) hδ)
        (reflect hQ (top Q 0 δ (by norm_num) hδ)),
      ∀ q (hq : q ∈ Q), increment (probe q hq) (doubled hQ p) =
        (if q ∈ S then (w q : ℝ) else 0) +
        (if -q ∈ S then (w (-q) : ℝ) else 0) -
        (if q = 0 then 1 else 0) := by
  obtain ⟨g, hg⟩ := exists_based_profile Q S w δ hδ inside sep
  let c := closingHalf hQ hδ h1 sep0
  refine ⟨g.trans c, fun q hq => ?_⟩
  rw [increment_doubled, increment_trans, increment_trans,
    hg q hq, hg (-q) (hQ q hq)]
  have hc := closingHalf_index hQ hδ h1 sep0 q hq
  rw [increment_doubled] at hc
  change increment (probe q hq) c + increment (probe (-q) (hQ q hq)) c =
    (if q = 0 then -1 else 0) at hc
  change _ + increment (probe q hq) c +
      (_ + increment (probe (-q) (hQ q hq)) c) = _
  by_cases h0 : q = 0 <;> simp only [h0, if_true, if_false] at hc ⊢ <;> linarith

/-- Finite puncture and support sets suffice: the common radius and the
entire half-path are constructed, rather than supplied as hypotheses. -/
theorem exists_finite_half_profile (Q S : Finset ℝ) (hQ : ∀ q ∈ Q, -q ∈ Q)
    (w : ℝ → ℤ) (inside : ∀ c ∈ S, |c| < 1) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < 1 ∧
      ∃ p : Path (top Q 0 δ (by norm_num) hδ)
          (reflect hQ (top Q 0 δ (by norm_num) hδ)),
        ∀ q (hq : q ∈ Q), increment (probe q hq) (doubled hQ p) =
          (if q ∈ S then (w q : ℝ) else 0) +
          (if -q ∈ S then (w (-q) : ℝ) else 0) -
          (if q = 0 then 1 else 0) := by
  obtain ⟨δ, hδ, h1, hin, hsep, hsep0⟩ := exists_profile_radius Q S inside
  exact ⟨δ, hδ, h1, exists_half_profile Q S hQ w δ hδ h1 hin hsep hsep0⟩

/-- Every symmetric integer index prescription supported inside the strip,
with odd central index, is realized by an actual doubled half-path.  In
particular the two exterior punctures may be included with index zero. -/
theorem exists_symmetric_half_profile (Q : Finset ℝ) (hQ : ∀ q ∈ Q, -q ∈ Q)
    (w : ℝ → ℤ) (symm : ∀ q ∈ Q, w (-q) = w q)
    (outside : ∀ q ∈ Q, 1 ≤ |q| → w q = 0)
    (k : ℤ) (central : w 0 = 2*k-1) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < 1 ∧
      ∃ p : Path (top Q 0 δ (by norm_num) hδ)
          (reflect hQ (top Q 0 δ (by norm_num) hδ)),
        ∀ q (hq : q ∈ Q), increment (probe q hq) (doubled hQ p) = (w q : ℝ) := by
  let S := Q.filter (fun q => |q| < 1 ∧ 0 ≤ q)
  let a (q : ℝ) : ℤ := if q = 0 then k else w q
  obtain ⟨δ, hδ, h1, p, hp⟩ := exists_finite_half_profile Q S hQ a (by
    intro q hq
    exact (Finset.mem_filter.mp hq).2.1)
  refine ⟨δ, hδ, h1, p, fun q hq => ?_⟩
  rw [hp q hq]
  by_cases h0 : q = 0
  · subst q
    simp only [S, a, Finset.mem_filter, hq, abs_zero, zero_lt_one, le_refl,
      and_self, if_true, neg_zero]
    have hc : (w 0 : ℝ) = 2*(k:ℝ)-1 := by exact_mod_cast central
    linarith
  · have hnq := hQ q hq
    by_cases hin : |q| < 1
    · rcases lt_or_gt_of_ne h0 with hn | hp
      · simp [S, a, hq, hnq, abs_neg, hin, not_le_of_gt hn,
          (neg_pos.mpr hn).le, h0, neg_ne_zero.mpr h0, symm q hq]
      · simp [S, a, hq, hnq, abs_neg, hin, hp.le,
          not_le_of_gt (neg_neg_of_pos hp), h0]
    · simp only [S, Finset.mem_filter, hin, abs_neg, false_and, and_false,
        if_false, h0, sub_zero, add_zero]
      exact_mod_cast (outside q hq (le_of_not_gt hin)).symm

end NRR.AngularLoops
