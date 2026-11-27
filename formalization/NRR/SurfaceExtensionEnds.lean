import NRR.SurfaceStripHomotopy

open Set Topology Filter
open scoped Classical unitInterval
noncomputable section

namespace NRR.Surface

variable {m : ℕ} [NeZero m]

/-- Limiting strip formula on a sign-labelled end, with normalized width η. -/
def modelStripValue (i : Fin m) (s : Finset (Fin m)) (η : ℝ) (signs : Fin m → Bool) (u : Circle) :
    Circle :=
  if ∀ j, j ≠ i → (0 < ((1-Complex.I) * withSign (signs j) (u : ℂ)).re ↔ j ∈ s) then
    stripPhase η ((1-Complex.I) * withSign (signs i) (u : ℂ)).im else 1

private def rot (u : Circle) : ℂ := (1 - Complex.I) * (u : ℂ)

private theorem sign_rotation (u : Circle) {η : ℝ} (hη : η < 1) (hstrip : |(rot u).im| ≤ η) :
    (0 ≤ (u : ℂ).im → 0 < (rot u).re) ∧ ((u : ℂ).im ≤ 0 → (rot u).re < 0) := by
  have hr : (rot u).re = (u : ℂ).re + (u : ℂ).im := by simp [rot, Complex.mul_re]
  have hi : (rot u).im = (u : ℂ).im - (u : ℂ).re := by simp [rot, Complex.mul_im]; ring
  have hnorm := Complex.sq_norm_sub_sq_re (u : ℂ)
  rw [Circle.norm_coe] at hnorm
  have hsmall := abs_lt.mp (hstrip.trans_lt hη)
  have hbig : 1 < (rot u).re ^ 2 := by
    have hs : (rot u).im ^ 2 < 1 := by
      nlinarith [mul_pos (by linarith only [hsmall.1] : 0 < 1 + (rot u).im)
        (by linarith only [hsmall.2] : 0 < 1 - (rot u).im)]
    rw [hr, hi] at *
    nlinarith
  have hsum : (rot u).re + (rot u).im = 2 * (u : ℂ).im := by rw [hr, hi]; ring
  constructor
  · intro h
    by_contra! h'
    have hl : -1 < (rot u).re := by linarith [hsmall.2]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (rot u).re + 1) (by linarith : 0 ≤ 1 - (rot u).re)]
  · intro h
    by_contra! h'
    have hl : (rot u).re < 1 := by linarith [hsmall.1]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (rot u).re + 1) (by linarith : 0 ≤ 1 - (rot u).re)]

private theorem signed_im_abs (u : Circle) (e : Bool) :
    |((1-Complex.I) * withSign e (u : ℂ)).im| = |(rot u).im| := by
  cases e
  · rfl
  · simp only [rot, withSign, ite_true, mul_neg, Complex.neg_im, abs_neg]

/-- Above the real axis the chosen strip contributes exactly when all free
sheet signs match the requested pattern. Below it the fixed positive zeroth
sign prevents a crossing of the same strip. -/
theorem modelStripWinding (i : Fin m) (hi : i ≠ 0) (s : Finset (Fin m)) (hs : 0 ∈ s)
    (signs : EndLabel m) {η : ℝ} (hη : 0 < η) (hη' : η < 1) (g : C(Circle,Circle))
    (hg : ∀ u, g u = modelStripValue i s η signs.val u) :
    winding g = if ∀ j, j ≠ i → (signs.val j = false ↔ j ∈ s) then
      (if signs.val i then -1 else 1) else 0 := by
  let c : I := ⟨1/2, by constructor <;> norm_num⟩
  let y (t : I) := ((1 - Complex.I) * withSign (signs.val i) (periodPath t : ℂ)).im
  let matchS := ∀ j, j ≠ i → (signs.val j = false ↔ j ∈ s)
  let a : C(I, ℝ) := ⟨fun t => if matchS then 2 * Real.pi * stripHeight η (y t) else 0, by
    have cy : Continuous y := Complex.continuous_im.comp (continuous_const.mul
      ((continuous_withSign _).comp (continuous_subtype_val.comp periodPath.continuous)))
    apply Continuous.if_const
    · unfold stripHeight
      fun_prop
    · exact continuous_const⟩
  have hangle (t : I) : ((periodPath t : Circle) : ℂ).im = Real.sin (2 * Real.pi * t.val) :=
    Complex.exp_ofReal_mul_I_im _
  have hu (t : I) (ht : t ≤ c) : 0 ≤ ((periodPath t : Circle) : ℂ).im := by
    rw [hangle]
    change t.val ≤ 1 / 2 at ht
    exact Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (by positivity) t.property.1)
      (by nlinarith [mul_le_mul_of_nonneg_left ht Real.pi_pos.le])
  have hd (t : I) (ht : c ≤ t) : ((periodPath t : Circle) : ℂ).im ≤ 0 := by
    rw [hangle, ← Real.sin_sub_two_pi]
    change 1 / 2 ≤ t.val at ht
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [mul_le_mul_of_nonneg_left t.property.2 Real.pi_pos.le])
      (by nlinarith [mul_le_mul_of_nonneg_left ht Real.pi_pos.le])
  let signTest (u : Circle) := ∀ j, j ≠ i →
    (0 < ((1-Complex.I) * withSign (signs.val j) (u : ℂ)).re ↔ j ∈ s)
  have upper (t : I) (ht : t ≤ c) : Circle.exp (a t) = g (periodPath t) := by
    rw [hg]
    change Circle.exp (if matchS then _ else 0) =
      if signTest (periodPath t) then stripPhase η (y t) else 1
    by_cases h : |y t| ≤ η
    · have hstrip : |(rot (periodPath t)).im| ≤ η := (signed_im_abs _ _).symm ▸ h
      have hr := (sign_rotation _ hη' hstrip).1 (hu t ht)
      have he : signTest (periodPath t) ↔ matchS := by
        apply forall_congr' fun j => forall_congr' fun _ => iff_congr ?_ Iff.rfl
        cases hj : signs.val j
        · simpa only [withSign, Bool.false_eq_true, ↓reduceIte, iff_true] using hr
        · simpa only [withSign, ite_true, mul_neg, Complex.neg_re, Bool.true_eq_false,
            iff_false, not_lt, neg_nonpos] using hr.le
      rw [if_congr he rfl rfl]
      split_ifs <;> simp [stripPhase]
    · have hone := stripPhase_eq_one hη (not_le.mp h).le
      rw [hone, ite_self]
      split_ifs
      · exact hone
      · exact Circle.exp_zero
  have lower (t : I) (ht : c ≤ t) : Circle.exp (0 : ℝ) = g (periodPath t) := by
    rw [hg, Circle.exp_zero]
    change 1 = if signTest (periodPath t) then stripPhase η (y t) else 1
    by_cases h : |y t| ≤ η
    · have hstrip : |(rot (periodPath t)).im| ≤ η := (signed_im_abs _ _).symm ▸ h
      have hr := (sign_rotation _ hη' hstrip).2 (hd t ht)
      apply (if_neg ?_).symm
      intro hm
      have bad := (hm 0 (Ne.symm hi)).mpr hs
      exact hr.not_gt (by simpa [signs.property, withSign, rot] using bad)
    · simp [stripPhase_eq_one hη (not_le.mp h).le]
  rw [winding, phaseChange_split (g.comp periodPath) c a 0 upper (fun t ht => lower t ht)]
  have hp0 : ((periodPath 0 : Circle) : ℂ) = 1 := by simp [periodPath]
  have hpc : ((periodPath c : Circle) : ℂ) = -1 := by
    change Complex.exp (((2 * Real.pi * (1/2) : ℝ) : ℂ) * Complex.I) = -1
    rw [show 2 * Real.pi * (1/2) = Real.pi by ring, Complex.exp_pi_mul_I]
  by_cases hm : matchS
  · have hm' : ∀ j, j ≠ i → (signs.val j = false ↔ j ∈ s) := hm
    cases hsi : signs.val i <;>
      simp [a, hm, y, hpc, hp0, withSign, hsi, stripHeight_hi hη hη'.le,
        stripHeight_lo hη (neg_le_neg hη'.le), Real.pi_ne_zero] <;> exact hm'
  · change ¬ ∀ j, j ≠ i → (signs.val j = false ↔ j ∈ s) at hm
    simp [a, matchS, hm]

/-- Direct one edge away from the all-positive label. -/
def endStep (a b : EndLabel m) : Prop :=
  ∃ i : Fin m, i ≠ 0 ∧ a.val i = false ∧ b.val i = true ∧ ∀ j, j ≠ i → a.val j = b.val j

def labelOfSet (S : Finset (Fin m)) : EndLabel m :=
  ⟨fun i => decide (i ≠ 0 ∧ i ∈ S), by simp⟩

theorem endStep_reachable (a : EndLabel m) : Relation.ReflTransGen endStep (labelOfSet ∅) a := by
  have reach (S : Finset (Fin m)) : Relation.ReflTransGen endStep (labelOfSet ∅) (labelOfSet S) := by
    induction S using Finset.induction_on with
    | empty => exact .refl
    | @insert i S hi ih =>
      by_cases hi0 : i = 0
      · subst i
        have h : labelOfSet (insert 0 S) = labelOfSet S := by
          apply Subtype.ext; funext j; by_cases hj : j = 0 <;> simp [labelOfSet, hj]
        rwa [h]
      · apply ih.tail
        refine ⟨i, hi0, by simp [labelOfSet, hi], by simp [labelOfSet, hi0], ?_⟩
        intro j hj
        simp [labelOfSet, hj]
  let S := Finset.univ.filter (fun i => a.val i = true)
  have he : labelOfSet S = a := by
    apply Subtype.ext; funext i
    by_cases hi : i = 0
    · subst i; simp [labelOfSet, a.property]
    · cases h : a.val i <;> simp [S, labelOfSet, hi, h]
  rw [← he]
  exact reach S

def positiveMask (a : EndLabel m) : Finset (Fin m) := Finset.univ.filter fun i => a.val i = false

theorem edgeProfile {a b : EndLabel m} {i : Fin m}
    (ha : a.val i = false) (hb : b.val i = true) (rest : ∀ j, j ≠ i → a.val j = b.val j)
    (c : EndLabel m) :
    (if ∀ j, j ≠ i → (c.val j = false ↔ j ∈ positiveMask a) then
      (if c.val i then -1 else 1 : ℝ) else 0) =
    (Pi.single a (1 : ℝ) - Pi.single b 1 : EndLabel m → ℝ) c := by
  let matchRest : Prop := ∀ j, j ≠ i → (c.val j = false ↔ j ∈ positiveMask a)
  have ab : a ≠ b := by intro h; rw [h, hb] at ha; contradiction
  have hmatch : matchRest ↔ ∀ j, j ≠ i → c.val j = a.val j := by
    apply forall_congr' fun j => forall_congr' fun _ => ?_
    cases hc : c.val j <;> cases h : a.val j <;> simp [positiveMask, h]
  change (if matchRest then _ else _) = _
  by_cases hm : matchRest
  · rw [if_pos hm]
    cases hc : c.val i
    · have e : c = a := Subtype.ext (funext fun j => by
        by_cases hj : j = i
        · subst j; exact hc.trans ha.symm
        · exact hmatch.mp hm j hj)
      simp [e, ab]
    · have e : c = b := Subtype.ext (funext fun j => by
        by_cases hj : j = i
        · subst j; exact hc.trans hb.symm
        · exact (hmatch.mp hm j hj).trans (rest j hj))
      simp [e, ab.symm]
  · have hca : c ≠ a := by intro h; exact hm (hmatch.mpr fun j _ => congrArg (fun w : EndLabel m => w.val j) h)
    have hcb : c ≠ b := by
      intro h
      exact hm (hmatch.mpr fun j hj => (congrArg (fun w : EndLabel m => w.val j) h).trans (rest j hj).symm)
    simp [hm, hca, hcb]

/-- With the actual strip maps identified up to homotopy on the ends, every
integral charge of total zero is the boundary winding of a global unit. -/
theorem realizeEndWindings {X : Type} [TopologicalSpace X] (loops : EndLabel m → C(Circle, X))
    (representatives : ∀ (i : Fin m), i ≠ 0 → ∀ a : EndLabel m, ∃ (u : C(X,Circle)),
      ∀ c : EndLabel m, winding (u.comp (loops c)) =
        if ∀ j, j ≠ i → (c.val j = false ↔ j ∈ positiveMask a) then
          (if c.val i then -1 else 1) else 0)
    (q : EndLabel m → ℤ) (hzero : ∑ a, q a = 0) :
    ∃ u : C(X,Circle), ∀ c, winding (u.comp (loops c)) = (q c : ℝ) := by
  apply realizeBalancedProfile loops (labelOfSet ∅) endStep endStep_reachable _ q hzero
  rintro a b ⟨i, hi, ha, hb, rest⟩
  obtain ⟨u, hu⟩ := representatives i hi a
  have h : Pi.single a (1 : ℝ) - Pi.single b 1 ∈ windingProfiles loops :=
    ⟨u, fun c => (hu c).trans (edgeProfile ha hb rest c)⟩
  simpa only [neg_sub] using (windingProfiles loops).neg_mem h

omit [NeZero m] in
private theorem exists_stripWidth (b : Fin m → ℝ) (hb : Function.Injective b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, j ≠ i → δ^2 < |b j - b i| := by
  have small : ∀ᶠ s : ℝ in 𝓝 0, ∀ (i j : Fin m), j ≠ i → s^2 < |b j - b i| := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases h : j = i
    · exact Eventually.of_forall fun _ hh => (hh h).elim
    · have hc : Continuous (fun s : ℝ => s^2) := by fun_prop
      filter_upwards [hc.continuousAt.eventually_lt continuousAt_const
        (show (0 : ℝ)^2 < |b j - b i| by simpa using abs_pos.mpr (sub_ne_zero.mpr (hb.ne h)))]
        with s hs using fun _ => hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp small
  refine ⟨r/2, by positivity, hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hr] using hr

/-- The winding of the old boundary values on the indicated end. -/
def boundaryWinding (b : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ i, t^2 * ‖(b i : ℂ)‖ < 1) (old : C(realLocus b, ℂ))
    (hn : ∀ x : endBoundary (fun i => (b i : ℂ)) t, old x.val ≠ 0) (a : EndLabel m) : ℝ :=
  winding ((phaseOf (old.restrict _) hn).comp (boundaryCircle (endBoundaryHomeomorph _ ht hs) a))

/-- Zero total winding suffices on the actual simultaneous square-root
surface. For every sufficiently large radius, an arbitrary prescribed
nonvanishing exterior residual extends without zeros, exactly, if its
oriented end windings sum to zero. -/
theorem fillDiskOfZeroTotalWinding (b : Fin m → ℝ) (hb : Function.Injective b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε →
    ∃ hs : ∀ i, t^2 * ‖(b i : ℂ)‖ < 1,
    ∀ (old : C(realLocus b, ℂ))
      (hn : ∀ x : realLocus b, (t⁻¹)^2 ≤ ‖projection b x‖ → old x ≠ 0),
      (∑ a, boundaryWinding b ht hs old (fun x => hn x.val x.property.ge) a) = 0 →
      ∃ G : C(realLocus b, ℂ), (∀ x, G x ≠ 0) ∧
        ∀ x ∉ interior (diskCore b ((t⁻¹)^2)), G x = old x := by
  obtain ⟨δ, hδ, sep⟩ := exists_stripWidth b hb
  obtain ⟨ε, hε, hom⟩ := exists_strip_end_homotopy b hδ
  have small : ∀ᶠ t : ℝ in 𝓝 0, (∀ i, t^2 * ‖(b i : ℂ)‖ < 1) ∧ t * δ < 1 := by
    apply Eventually.and
    · apply eventually_all.mpr
      intro i
      have hc : Continuous fun t : ℝ => t^2 * ‖(b i : ℂ)‖ := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    · have hc : Continuous (fun t : ℝ => t * δ) := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨v, hv, hball⟩ := Metric.mem_nhds_iff.mp small
  refine ⟨min ε v, lt_min hε hv, ?_⟩
  intro t ht ht'
  obtain ⟨hs, hη⟩ := hball (show t ∈ Metric.ball 0 v by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using lt_of_lt_of_le ht' (min_le_right _ _))
  refine ⟨hs, ?_⟩
  intro old hn zero
  let B := endBoundary (fun i => (b i : ℂ)) t
  let e := endBoundaryHomeomorph (fun i => (b i : ℂ)) ht hs
  let loops (a : EndLabel m) : C(Circle, realLocus b) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(B,realLocus b)).comp (boundaryCircle e a)
  let degrees := boundaryWinding b ht hs old (fun x => hn x.val x.property.ge)
  have intDeg (a : EndLabel m) : ∃ k : ℤ, degrees a = k := by
    unfold degrees boundaryWinding
    exact winding_integer _
  choose q hq using intDeg
  have total : (∑ a, q a : ℤ) = 0 := by
    have hreal : (∑ a, (q a : ℝ)) = 0 := by simpa only [← hq] using zero
    exact_mod_cast hreal
  obtain ⟨u, hu⟩ := realizeEndWindings loops (fun i hi a => by
    let U := stripUnit i (positiveMask a) δ hδ (sep i)
    refine ⟨U, fun c => ?_⟩
    obtain ⟨H, h0, h1⟩ := hom t ht (ht'.trans_le (min_le_left _ _)) i (positiveMask a) c.val (sep i)
    let g : C(Circle,Circle) := ⟨fun z => H (0,z), by fun_prop⟩
    have eq := winding_homotopy g (U.comp (loops c)) H (fun _ => rfl) h1
    exact eq.symm.trans (modelStripWinding i hi _ (by simp [positiveMask,a.property])
      c (mul_pos ht hδ) hη g h0)) q total
  refine replaceInsideCore (diskCore b ((t⁻¹)^2)) B (isClosed_endBoundary _ _)
    (frontier_diskCore_subset_endBoundary b ht) e u old ?_ (fun x => hn x.val x.property.ge) ?_
  · intro x hx
    apply hn
    by_contra! h
    apply hx
    apply preimage_interior_subset_interior_preimage (projection b).continuous
    rw [mem_preimage, interior_closedBall _ (by positivity), Metric.mem_ball, dist_zero_right]
    exact h
  · intro a
    exact (hq a).trans (hu a).symm

end NRR.Surface
