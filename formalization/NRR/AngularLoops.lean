import NRR.SurfaceResidualWinding
import Mathlib.Analysis.Convex.PathConnected

open Set Topology
open scoped unitInterval Classical
noncomputable section

namespace NRR.AngularLoops

open Surface

/-- Additivity for paths whose endpoint phases may be arbitrary. -/
theorem phaseChange_trans {x y z : Circle} (p : Path x y) (q : Path y z) :
    phaseChange (p.trans q).toContinuousMap =
      phaseChange p.toContinuousMap + phaseChange q.toContinuousMap := by
  let a := pathArgument p.toContinuousMap
  let b := pathArgument q.toContinuousMap
  let P : Path (a 0) (a 1) := ⟨a, rfl, rfl⟩
  let Q : Path (a 1) (b 1 + (a 1 - b 0)) :=
    ⟨⟨fun s => b s + (a 1 - b 0), by fun_prop⟩, by dsimp; ring, rfl⟩
  have hab : Circle.exp (a 1 - b 0) = 1 := by
    rw [Circle.exp_sub, exp_pathArgument, exp_pathArgument]
    simp
  have hl (s : I) : Circle.exp ((P.trans Q) s) = (p.trans q) s := by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact exp_pathArgument _ _
    · change Circle.exp (b _ + (a 1 - b 0)) = _
      rw [Circle.exp_add, hab, mul_one]
      exact exp_pathArgument _ _
  rw [phaseChange_eq _ (P.trans Q).toContinuousMap hl]
  change (((P.trans Q) 1 - (P.trans Q) 0) / _) = _
  rw [Path.target, Path.source]
  change (b 1 + (a 1 - b 0) - a 0) / _ = (a 1 - a 0) / _ + (b 1 - b 0) / _
  ring

theorem phaseChange_reverse {x y : Circle} (p : Path x y) :
    phaseChange p.symm.toContinuousMap = -phaseChange p.toContinuousMap := by
  let a := pathArgument p.toContinuousMap
  let L : C(I,ℝ) := ⟨fun s => a (unitInterval.symm s), a.continuous.comp unitInterval.continuous_symm⟩
  rw [phaseChange_eq _ L (fun s => exp_pathArgument _ _)]
  simp [L, a, phaseChange]
  ring

/-- The strip in which the real coordinate of the angular data moves, with
all specified real punctures removed. -/
abbrev region (Q : Finset ℝ) := {z : ℂ // |z.re| < 1 ∧ ∀ q ∈ Q, z ≠ (q : ℂ)}

def probe {Q : Finset ℝ} (q : ℝ) (hq : q ∈ Q) : C(region Q, Circle) :=
  phaseOf ⟨fun z => z.val - q, continuous_subtype_val.sub continuous_const⟩
    (fun z => sub_ne_zero.mpr (z.property.2 q hq))

def increment {X : Type} [TopologicalSpace X] {a b : X} (f : C(X,Circle)) (p : Path a b) : ℝ :=
  phaseChange (p.map f.continuous).toContinuousMap

theorem increment_trans {X : Type} [TopologicalSpace X] {a b c : X}
    (f : C(X,Circle)) (p : Path a b) (q : Path b c) :
    increment f (p.trans q) = increment f p + increment f q := by
  simp only [increment, Path.map_trans, phaseChange_trans]

theorem increment_reverse {X : Type} [TopologicalSpace X] {a b : X}
    (f : C(X,Circle)) (p : Path a b) : increment f p.symm = -increment f p :=
  phaseChange_reverse (p.map f.continuous)

theorem increment_refl {X : Type} [TopologicalSpace X] (f : C(X,Circle)) (a : X) :
    increment f (Path.refl a) = 0 := by
  unfold increment
  rw [phaseChange_eq ((Path.refl a).map f.continuous).toContinuousMap
    (ContinuousMap.const I (Complex.arg (f a))) (fun _ => Circle.exp_arg _)]
  simp

theorem increment_excursion {X : Type} [TopologicalSpace X] {a b : X} (f : C(X,Circle))
    (lead : Path a b) (loop : Path b b) :
    increment f ((lead.trans loop).trans lead.symm) = increment f loop := by
  simp only [increment_trans, increment_reverse]
  ring

private def plane (x y : ℝ) : ℂ := ⟨x,y⟩

def top (Q : Finset ℝ) (x δ : ℝ) (hx : |x| < 1) (hδ : 0 < δ) : region Q :=
  ⟨plane x δ, hx, fun _ _ h => hδ.ne' (congrArg Complex.im h)⟩

/-- The horizontal access path remains at positive height. -/
def approach (Q : Finset ℝ) (c δ : ℝ) (hc : |c| < 1) (hδ : 0 < δ) :
    Path (top Q 0 δ (by norm_num) hδ) (top Q c δ hc hδ) where
  toFun t := ⟨plane (t.val*c) δ, by
    change |t.val * c| < 1
    rw [abs_mul, abs_of_nonneg t.property.1]
    exact lt_of_le_of_lt (by simpa using mul_le_mul_of_nonneg_right t.property.2 (abs_nonneg c)) hc,
    fun _ _ h => hδ.ne' (congrArg Complex.im h)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h (t : I) : plane (t.val*c) δ = ((t.val*c : ℝ) : ℂ) + (δ : ℂ)*Complex.I :=
      (Complex.re_add_im _).symm
    simp_rw [h]
    fun_prop
  source' := by apply Subtype.ext; simp [top, plane]
  target' := by apply Subtype.ext; simp [top, plane]

private def turning (k : ℤ) (t : I) : Circle := Circle.exp (2 * Real.pi * k * t.val)

private def orbit (c δ : ℝ) (k : ℤ) (t : I) : ℂ :=
  (c : ℂ) + (δ : ℂ) * Complex.I * (turning k t : ℂ)

private theorem orbit_dist (c δ : ℝ) (k : ℤ) (t : I) (hδ : 0 < δ) :
    ‖orbit c δ k t - (c : ℂ)‖ = δ := by
  simp [orbit, Complex.norm_real, abs_of_pos hδ]

/-- A based loop entirely in the strip, going k full turns around c. -/
def circleLoop (Q : Finset ℝ) (c δ : ℝ) (k : ℤ) (hc : |c| + δ < 1) (hδ : 0 < δ)
    (sep : ∀ q ∈ Q, q ≠ c → δ < |q-c|) :
    Path (top Q c δ (by linarith) hδ) (top Q c δ (by linarith) hδ) where
  toFun t := ⟨orbit c δ k t, by
    have hr := Complex.abs_re_le_norm (orbit c δ k t - (c : ℂ))
    rw [orbit_dist c δ k t hδ, Complex.sub_re, Complex.ofReal_re] at hr
    exact lt_of_le_of_lt (by linarith [abs_sub_abs_le_abs_sub (orbit c δ k t).re c]) hc,
    fun q hq he => by
      have dist := orbit_dist c δ k t hδ
      rw [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at dist
      by_cases h : q = c
      · exact hδ.ne (by simpa [h] using dist)
      · exact (sep q hq h).ne dist.symm⟩
  continuous_toFun := by unfold orbit turning; fun_prop
  source' := by
    apply Subtype.ext
    apply Complex.ext <;> simp [top, orbit, turning, plane, Complex.mul_re, Complex.mul_im]
  target' := by
    apply Subtype.ext
    apply Complex.ext <;>
      simp [top, orbit, turning, plane, Circle.exp_two_pi_mul_int, Complex.mul_re, Complex.mul_im]

private theorem phaseChange_zero_halfPlane (γ : C(I,Circle)) (cl : γ 1 = γ 0) (v : Circle)
    (hv : ∀ t, 0 < ((v * γ t : Circle) : ℂ).re) : phaseChange γ = 0 := by
  have cv : Continuous (fun t : I => ((v * γ t : Circle) : ℂ)) :=
    continuous_subtype_val.comp (continuous_const.mul γ.continuous)
  have carg : Continuous (fun t : I => Complex.arg (v * γ t : Circle)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Complex.continuousAt_arg (Or.inl (hv t))).comp (f := fun t : I => ((v * γ t : Circle) : ℂ)) cv.continuousAt
  let a : C(I,ℝ) := ⟨fun t => Complex.arg (v * γ t : Circle) - Complex.arg v,
    carg.sub continuous_const⟩
  have ha (t : I) : Circle.exp (a t) = γ t := by
    change Circle.exp (Complex.arg (v * γ t : Circle) - Complex.arg v) = _
    rw [Circle.exp_sub, Circle.exp_arg (v * γ t), Circle.exp_arg]
    simp
  rw [phaseChange_eq _ _ ha]
  simp [a, cl]

/-- The literal circle traverses its own puncture k times and all the
remaining punctures zero times. -/
theorem increment_circleLoop (Q : Finset ℝ) (c δ : ℝ) (k : ℤ)
    (hc : |c| + δ < 1) (hδ : 0 < δ) (sep : ∀ q ∈ Q, q ≠ c → δ < |q-c|)
    (q : ℝ) (hq : q ∈ Q) :
    increment (probe q hq) (circleLoop Q c δ k hc hδ sep) = if q = c then (k : ℝ) else 0 := by
  let p := circleLoop Q c δ k hc hδ sep
  let γ := (p.map (probe q hq).continuous).toContinuousMap
  have hz (t : I) : (γ t : ℂ) = (orbit c δ k t - q) / (‖orbit c δ k t - q‖ : ℂ) := rfl
  change phaseChange γ = _
  split_ifs with eq
  · subst q
    let l : C(I,ℝ) := ⟨fun t => Real.pi/2 + 2*Real.pi*k*t.val, by fun_prop⟩
    rw [phaseChange_eq γ l (by
      intro t
      apply Circle.ext
      change (Circle.exp (Real.pi/2 + 2*Real.pi*k*t.val) : ℂ) = _
      rw [Circle.exp_add, Circle.coe_mul, Circle.coe_exp, hz, orbit_dist _ _ _ _ hδ]
      have hI : (Circle.exp (Real.pi/2) : ℂ) = Complex.I := by
        rw [Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
      change Complex.exp (((Real.pi/2 : ℝ) : ℂ)*Complex.I) * (turning k t : ℂ) =
        (orbit c δ k t - c) / δ
      change (Circle.exp (Real.pi/2) : ℂ) * _ = _
      rw [hI]
      unfold orbit
      field_simp [hδ.ne']
      ring)]
    simp [l]
  · have hs := sep q hq eq
    have close : γ 1 = γ 0 := by
      change probe q hq (p 1) = probe q hq (p 0)
      rw [Path.target, Path.source]
    have hbound (t : I) : |(orbit c δ k t).re - c| ≤ δ := by
      simpa only [Complex.sub_re, Complex.ofReal_re, orbit_dist c δ k t hδ] using
        Complex.abs_re_le_norm (orbit c δ k t - c)
    have hden (t : I) : 0 < ‖orbit c δ k t - q‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr ((p t).property.2 q hq))
    have hRe (t : I) : (γ t : ℂ).re = ((orbit c δ k t).re - q) / ‖orbit c δ k t - q‖ := by
      rw [hz, Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]
    rcases lt_or_gt_of_ne eq with h | h
    · rw [abs_of_neg (sub_neg.mpr h)] at hs
      apply phaseChange_zero_halfPlane γ close 1
      intro t
      simp only [one_mul, hRe]
      exact div_pos (by linarith [(abs_le.mp (hbound t)).1]) (hden t)
    · rw [abs_of_pos (sub_pos.mpr h)] at hs
      apply phaseChange_zero_halfPlane γ close (Circle.exp Real.pi)
      intro t
      rw [Circle.coe_mul, Circle.coe_exp, Complex.exp_pi_mul_I, neg_one_mul, Complex.neg_re, hRe]
      exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith [(abs_le.mp (hbound t)).2]) (hden t))

/-- A generator and its access path have the same index at every puncture. -/
theorem exists_based_generator (Q : Finset ℝ) (c δ : ℝ) (k : ℤ)
    (hc : |c| + δ < 1) (hδ : 0 < δ) (sep : ∀ q ∈ Q, q ≠ c → δ < |q-c|) :
    ∃ p : Path (top Q 0 δ (by norm_num) hδ) (top Q 0 δ (by norm_num) hδ),
      ∀ q (hq : q ∈ Q), increment (probe q hq) p = if q = c then (k : ℝ) else 0 := by
  let lead := approach Q c δ (by linarith) hδ
  let circle := circleLoop Q c δ k hc hδ sep
  refine ⟨(lead.trans circle).trans lead.symm, fun q hq => ?_⟩
  rw [increment_excursion]
  exact increment_circleLoop Q c δ k hc hδ sep q hq

/-- Combine independent local turns into one actual loop based at iδ. -/
theorem exists_based_profile (Q S : Finset ℝ) (w : ℝ → ℤ) (δ : ℝ) (hδ : 0 < δ)
    (inside : ∀ c ∈ S, |c| + δ < 1) (sep : ∀ c ∈ S, ∀ q ∈ Q, q ≠ c → δ < |q-c|) :
    ∃ p : Path (top Q 0 δ (by norm_num) hδ) (top Q 0 δ (by norm_num) hδ),
      ∀ q (hq : q ∈ Q), increment (probe q hq) p = if q ∈ S then (w q : ℝ) else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨Path.refl _, by simp [increment_refl]⟩
  | @insert c S hc ih =>
    obtain ⟨p, hp⟩ := ih (fun x hx => inside x (Finset.mem_insert_of_mem hx))
      (fun x hx => sep x (Finset.mem_insert_of_mem hx))
    obtain ⟨g, hg⟩ := exists_based_generator Q c δ (w c)
      (inside c (Finset.mem_insert_self _ _)) hδ (sep c (Finset.mem_insert_self _ _))
    refine ⟨p.trans g, fun q hq => ?_⟩
    rw [increment_trans, hp q hq, hg q hq]
    by_cases h : q = c
    · subst q; simp [hc]
    · simp [h]

def reflect {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) : C(region Q, region Q) :=
  ⟨fun z => ⟨-z.val, by simpa using z.property.1, fun q h e => z.property.2 (-q) (hQ q h)
      (by rw [Complex.ofReal_neg, ← e, neg_neg])⟩, continuous_subtype_val.neg.subtype_mk _⟩

private theorem exp_pi_coe : (Circle.exp Real.pi : ℂ) = -1 := Complex.exp_pi_mul_I

theorem increment_reflect {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q)
    {a b : region Q} (p : Path a b) (q : ℝ) (hq : q ∈ Q) :
    increment (probe q hq) (p.map (reflect hQ).continuous) = increment (probe (-q) (hQ q hq)) p := by
  let γ := (p.map (probe (-q) (hQ q hq)).continuous).toContinuousMap
  have eq : ((p.map (reflect hQ).continuous).map (probe q hq).continuous).toContinuousMap =
      ContinuousMap.const I (Circle.exp Real.pi) * γ := by
    ext t
    change (-((p t).val) - q) / (‖-((p t).val) - q‖ : ℂ) =
      (Circle.exp Real.pi : ℂ) * (((p t).val - ((-q : ℝ) : ℂ)) / _)
    simp only [Complex.ofReal_neg, sub_neg_eq_add, exp_pi_coe, neg_one_mul]
    rw [show -((p t).val) - (q : ℂ) = -((p t).val + q) by abel, norm_neg, neg_div]
    rfl
  change phaseChange _ = phaseChange γ
  rw [eq, phaseChange_mul, phaseChange_eq (ContinuousMap.const I (Circle.exp Real.pi))
    (ContinuousMap.const I Real.pi) (fun _ => rfl)]
  simp

/-- Reflect the second half about the origin to close the path. -/
def doubled {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {a : region Q}
    (p : Path a (reflect hQ a)) : Path a a :=
  p.trans ((p.map (reflect hQ).continuous).cast rfl (Subtype.ext (neg_neg _).symm))

theorem increment_doubled {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {a : region Q}
    (p : Path a (reflect hQ a)) (q : ℝ) (hq : q ∈ Q) :
    increment (probe q hq) (doubled hQ p) =
      increment (probe q hq) p + increment (probe (-q) (hQ q hq)) p := by
  unfold doubled
  rw [increment_trans]
  exact congrArg (_ + ·) (increment_reflect hQ p q hq)

private def halfValue (δ : ℝ) (t : I) : ℂ :=
  (δ : ℂ) * Complex.I * (Circle.exp (-Real.pi * t.val) : ℂ)

private theorem norm_halfValue {δ : ℝ} (hδ : 0 < δ) (t : I) : ‖halfValue δ t‖ = δ := by
  unfold halfValue
  rw [norm_mul, norm_mul, Circle.norm_coe, Complex.norm_I, mul_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ]

/-- The clockwise half-turn from the upper to the lower base point. -/
def closingHalf {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {δ : ℝ} (hδ : 0 < δ)
    (h1 : δ < 1) (sep : ∀ q ∈ Q, q ≠ 0 → δ < |q|) :
    Path (top Q 0 δ (by norm_num) hδ) (reflect hQ (top Q 0 δ (by norm_num) hδ)) where
  toFun t := ⟨halfValue δ t, (Complex.abs_re_le_norm _).trans_lt ((norm_halfValue hδ t).trans_lt h1),
    fun q hq eq => by
      have h := norm_halfValue hδ t
      rw [eq, Complex.norm_real, Real.norm_eq_abs] at h
      by_cases hq0 : q = 0
      · exact hδ.ne (by simpa [hq0] using h)
      · exact (sep q hq hq0).ne h.symm⟩
  continuous_toFun := by unfold halfValue; fun_prop
  source' := by apply Subtype.ext; apply Complex.ext <;> simp [top, plane, halfValue, Complex.mul_im, Complex.mul_re]
  target' := by
    apply Subtype.ext
    change halfValue δ 1 = -plane 0 δ
    change (δ : ℂ) * Complex.I * (Circle.exp (-Real.pi * 1) : ℂ) = -plane 0 δ
    rw [mul_one, Circle.exp_neg, Circle.coe_inv, exp_pi_coe]
    apply Complex.ext <;> simp [plane, Complex.mul_im, Complex.mul_re]

theorem closingHalf_index {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {δ : ℝ} (hδ : 0 < δ)
    (h1 : δ < 1) (sep : ∀ q ∈ Q, q ≠ 0 → δ < |q|)
    (q : ℝ) (hq : q ∈ Q) :
    increment (probe q hq) (doubled hQ (closingHalf hQ hδ h1 sep)) = if q = 0 then -1 else 0 := by
  let p := closingHalf hQ hδ h1 sep
  by_cases hq0 : q = 0
  · subst q
    rw [increment_doubled]
    simp only [neg_zero, if_true]
    let γ := (p.map (probe 0 hq).continuous).toContinuousMap
    have hh : increment (probe 0 hq) p = -1/2 := by
      let l : C(I,ℝ) := ⟨fun t => Real.pi/2 - Real.pi*t.val, by fun_prop⟩
      change phaseChange γ = _
      rw [phaseChange_eq γ l (by
        intro t
        apply Circle.ext
        change (Circle.exp (Real.pi/2 - Real.pi*t.val) : ℂ) =
          (halfValue δ t - (0 : ℝ)) / (‖halfValue δ t - (0 : ℝ)‖ : ℂ)
        simp only [Complex.ofReal_zero, sub_zero, norm_halfValue hδ]
        rw [sub_eq_add_neg, Circle.exp_add, Circle.coe_mul]
        have hi : (Circle.exp (Real.pi/2) : ℂ) = Complex.I := by
          rw [Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
        rw [hi]
        unfold halfValue
        rw [neg_mul]
        field_simp [hδ.ne'])]
      simp [l]
      field_simp [Real.pi_ne_zero]
    rw [hh]
    norm_num
  · let γ := ((doubled hQ p).map (probe q hq).continuous).toContinuousMap
    rw [if_neg hq0]
    change phaseChange γ = 0
    have cl : γ 1 = γ 0 := by
      change probe q hq ((doubled hQ p) 1) = probe q hq ((doubled hQ p) 0)
      rw [Path.source, Path.target]
    have norm_eq (t : I) : ‖((doubled hQ p) t).val‖ = δ := by
      unfold doubled
      rw [Path.trans_apply]
      split_ifs
      · exact norm_halfValue hδ _
      · change ‖-halfValue δ _‖ = δ
        rw [norm_neg, norm_halfValue hδ]
    have bound (t : I) : |((doubled hQ p) t).val.re| ≤ δ := (Complex.abs_re_le_norm _).trans (norm_eq t).le
    have hphase (t : I) : (γ t : ℂ).re = (((doubled hQ p) t).val.re - q) / ‖((doubled hQ p) t).val - q‖ := by
      change (((_ : ℂ) - (q : ℂ)) / (_ : ℝ)).re = _
      rw [Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]
      rfl
    have nonzero (t : I) := norm_pos_iff.mpr (sub_ne_zero.mpr (((doubled hQ p) t).property.2 q hq))
    have gap := sep q hq hq0
    rcases lt_or_gt_of_ne hq0 with h | h
    · apply phaseChange_zero_halfPlane γ cl 1
      intro t
      rw [one_mul, hphase]
      rw [abs_of_neg h] at gap
      exact div_pos (by linarith [(abs_le.mp (bound t)).1]) (nonzero t)
    · apply phaseChange_zero_halfPlane γ cl (Circle.exp Real.pi)
      intro t
      rw [Circle.coe_mul, exp_pi_coe, neg_one_mul, Complex.neg_re, hphase]
      rw [abs_of_pos h] at gap
      exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith [(abs_le.mp (bound t)).2]) (nonzero t))

end NRR.AngularLoops
