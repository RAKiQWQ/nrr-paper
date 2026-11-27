import NRR.SurfaceEnds
import NRR.SurfaceExtension

/-! Deforming the shifted roots to their values at infinity preserves the
circle-valued strip function on the parametrized boundary. -/

open Set Topology Filter
open scoped unitInterval Classical
noncomputable section

namespace NRR.Surface

private def rotateEnd (b : ℝ) (e : Bool) (p : ℝ × Circle) : ℂ :=
  (1 - Complex.I) * withSign e (endRoot b p)

private theorem continuousAt_rotateEnd (b : ℝ) (e : Bool) {p : ℝ × Circle}
    (hs : p.1^2 * ‖(b : ℂ)‖ < 1) : ContinuousAt (rotateEnd b e) p :=
  continuousAt_const.mul ((continuous_withSign e).continuousAt.comp (continuousAt_endRoot b hs))

private theorem tube_eventually {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (good : ℝ × X → Prop) (h : ∀ x, ∀ᶠ p in 𝓝 (0,x), good p) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x, good (t,x) := by
  obtain ⟨U,V,hU,_,hu,hv,sub⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) (isCompact_univ (X := X))
    (isOpen_interior (s := {p | good p})) (fun ⟨t,x⟩ hx => by
      obtain rfl : t = 0 := hx.1
      exact mem_interior_iff_mem_nhds.mpr (h x))
  filter_upwards [hU.mem_nhds (hu (mem_singleton _))] with t ht x
  exact interior_subset (sub ⟨ht,hv (mem_univ x)⟩)

private theorem imaginary_or_real (a b : ℝ) (e d : Bool) (u : Circle) :
    0 < |(rotateEnd a e (0,u)).im| ∨ (rotateEnd b d (0,u)).re ≠ 0 := by
  by_contra! h
  have hi := abs_nonpos_iff.mp h.1
  have im : ((1 - Complex.I) * (u : ℂ)).im = 0 := by
    cases e <;> simp [rotateEnd, withSign] at hi ⊢ <;> linarith
  have re : ((1 - Complex.I) * (u : ℂ)).re = 0 := by
    have hr := h.2
    cases d <;> simp [rotateEnd, withSign] at hr ⊢ <;> linarith
  have hn : (1 - Complex.I : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num at this
  exact mul_ne_zero hn u.coe_ne_zero (Complex.ext re im)

private def movingRoot (b : ℝ) (e : Bool) (p : ℝ × (I × Circle)) :=
  rotateEnd b e (p.1 * p.2.1.val, p.2.2)

private theorem continuousAt_movingRoot_zero (b : ℝ) (e : Bool) (v : I × Circle) :
    ContinuousAt (movingRoot b e) (0,v) := by
  let scale (p : ℝ × (I × Circle)) := (p.1 * p.2.1.val, p.2.2)
  have hc : Continuous scale := by unfold scale; fun_prop
  exact (continuousAt_rotateEnd b e (p := scale (0,v)) (by simp [scale])).comp hc.continuousAt

/-- On a sufficiently distant annulus a crossing of strip i cannot meet
the imaginary axis of any other rotated root, even while the shifts
contract to zero. Uniformity includes the angle and the homotopy time. -/
private theorem moving_strip_separation (a b δ : ℝ) (e d : Bool) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ v : I × Circle,
      t*δ < |(movingRoot a e (t,v)).im| ∨ (movingRoot b d (t,v)).re ≠ 0 := by
  apply tube_eventually (fun p => p.1*δ < |(movingRoot a e p).im| ∨ (movingRoot b d p).re ≠ 0)
  intro v
  rcases imaginary_or_real a b e d v.2 with hi | hr
  · have hlt : (0 : ℝ)*δ < |(movingRoot a e (0,v)).im| := by simpa [movingRoot] using hi
    have c₁ : ContinuousAt (fun p : ℝ × (I × Circle) => p.1 * δ) (0,v) := by fun_prop
    have c₂ := (Complex.continuous_im.continuousAt.comp (continuousAt_movingRoot_zero a e v)).abs
    exact (c₁.eventually_lt c₂ hlt).mono (fun _ h => Or.inl h)
  · have hn : (movingRoot b d (0,v)).re ≠ 0 := by simpa [movingRoot] using hr
    exact ((Complex.continuous_re.continuousAt.comp (continuousAt_movingRoot_zero b d v)).eventually_ne hn).mono
      (fun _ h => Or.inr h)

private def matchesStrip {m : ℕ} (s : Finset (Fin m)) (i : Fin m) (z : Fin m → ℂ) : Prop :=
  ∀ j, j ≠ i → (0 < (z j).re ↔ j ∈ s)

private theorem continuous_stripValue {X : Type*} [TopologicalSpace X] {m : ℕ}
    (R : Fin m → X → ℂ) (cR : ∀ j, Continuous (R j)) (i : Fin m) (s : Finset (Fin m))
    {η : ℝ} (hη : 0 < η)
    (sep : ∀ x j, η < |(R i x).im| ∨ (R j x).re ≠ 0) :
    Continuous (fun x => if matchesStrip s i (fun j => R j x) then stripPhase η (R i x).im else 1) := by
  classical
  let y (x : X) := (R i x).im
  have cy : Continuous y := Complex.continuous_im.comp (cR i)
  have cp : Continuous fun x => stripPhase η (y x) := by
    unfold stripPhase stripHeight
    exact Circle.exp.continuous.comp (by fun_prop)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : η < |y x|
  · apply continuousAt_const (y := (1 : Circle)) |>.congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt cy.abs.continuousAt hx] with w hw
    simp [stripPhase_eq_one hη hw.le, y] at *
  · have each (j : Fin m) : ∀ᶠ w in 𝓝 x, 0 < (R j w).re ↔ 0 < (R j x).re := by
      have cj := (Complex.continuous_re.comp (cR j)).continuousAt (x := x)
      rcases lt_or_gt_of_ne ((sep x j).resolve_left hx) with h | h
      · filter_upwards [cj.eventually_lt continuousAt_const h] with w hw
        exact iff_of_false (not_lt.mpr hw.le) (not_lt.mpr h.le)
      · filter_upwards [continuousAt_const.eventually_lt cj h] with w hw
        exact iff_of_true hw h
    have signs : ∀ᶠ w in 𝓝 x,
        matchesStrip s i (fun j => R j w) ↔ matchesStrip s i (fun j => R j x) :=
      (eventually_all.mpr each).mono fun w hw =>
        forall_congr' fun j => forall_congr' fun _ => iff_congr (hw j) Iff.rfl
    by_cases hm : matchesStrip s i (fun j => R j x)
    · apply cp.continuousAt.congr_of_eventuallyEq
      filter_upwards [signs] with w hw
      simp [hw.mpr hm, y]
    · apply continuousAt_const (y := (1 : Circle)) |>.congr_of_eventuallyEq
      filter_upwards [signs] with w hw
      simp [show ¬ matchesStrip s i (fun j => R j w) from fun hh => hm (hw.mp hh)]

private theorem stripPhase_scaled {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (y : ℝ) :
    stripPhase (t*δ) y = stripPhase δ (y/t) := by
  unfold stripPhase stripHeight
  rw [show (y + t*δ) / (2*(t*δ)) = (y/t + δ) / (2*δ) by field_simp]

variable {m : ℕ} [NeZero m]

/-- One common collar works for all strips and ends. Each actual strip loop
is homotopic to its model on unshifted signed roots; the latter is evaluated
with half-width `t * δ`. -/
theorem exists_strip_end_homotopy (b : Fin m → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε → ∀ (i : Fin m)
      (s : Finset (Fin m)) (signs : Fin m → Bool) (gap : ∀ j, j ≠ i → δ^2 < |b j - b i|),
      ∃ H : C(I × Circle, Circle),
        (∀ u, H (0,u) = if (∀ j, j ≠ i →
           (0 < ((1 - Complex.I) * withSign (signs j) (u : ℂ)).re ↔ j ∈ s)) then
           stripPhase (t*δ) ((1 - Complex.I) * withSign (signs i) (u : ℂ)).im else 1) ∧
       (∀ u, H (1,u) = stripUnit i s δ hδ gap (endPoint (fun j => (b j : ℂ)) ht signs u)) := by
  classical
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ (i j : Fin m) (e d : Bool) (v : I × Circle),
      t*δ < |(movingRoot (b i) e (t,v)).im| ∨ (movingRoot (b j) d (t,v)).re ≠ 0 :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun e =>
      eventually_all.mpr fun d => moving_strip_separation _ _ _ e d
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, t^2 * ‖(b i : ℂ)‖ < 1 := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun t : ℝ => t^2 * ‖(b i : ℂ)‖) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hall.and hsmall)
  refine ⟨ε, hε, ?_⟩
  intro t ht hεt i s signs gap
  obtain ⟨sep, small⟩ := hball (show t ∈ Metric.ball 0 ε by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hεt)
  let R (j : Fin m) (v : I × Circle) := movingRoot (b j) (signs j) (t,v)
  have cR (j : Fin m) : Continuous (R j) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hab : (t * v.1.val)^2 * ‖(b j : ℂ)‖ < 1 := by
      apply lt_of_le_of_lt _ (small j)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply pow_le_pow_left₀ (mul_nonneg ht.le v.1.property.1)
      simpa using mul_le_mul_of_nonneg_left v.1.property.2 ht.le
    let scale (w : I × Circle) := (t * w.1.val, w.2)
    have hscale : Continuous scale := by unfold scale; fun_prop
    exact (continuousAt_rotateEnd (b j) (signs j) (p := scale v) hab).comp hscale.continuousAt
  refine ⟨⟨_, continuous_stripValue R cR i s (mul_pos ht hδ) (fun v j => sep i j _ _ v)⟩, ?_, ?_⟩
  · intro u
    simp [R, movingRoot, rotateEnd, matchesStrip]
  · intro u
    rw [stripUnit_apply]
    have he (j : Fin m) : rotatedRoot j (endPoint (fun j => (b j : ℂ)) ht signs u) =
        R j (1,u) / (t : ℂ) := by
      change (1-Complex.I) * (withSign (signs j) _ / (t : ℂ)) = _
      simp [R, movingRoot, rotateEnd, mul_div_assoc]
    have hr (j : Fin m) : 0 < (rotatedRoot j (endPoint (fun j => (b j : ℂ)) ht signs u)).re ↔
        0 < (R j (1,u)).re := by
      rw [he j, Complex.div_ofReal_re]
      exact div_pos_iff_of_pos_right ht
    have hcond : stripSigns i s (endPoint (fun j => (b j : ℂ)) ht signs u) ↔
        matchesStrip s i (fun j => R j (1,u)) :=
      forall_congr' fun j => forall_congr' fun _ => iff_congr (hr j) Iff.rfl
    simp only [ContinuousMap.coe_mk, hcond, he i, Complex.div_ofReal_im, stripPhase_scaled ht hδ]

end NRR.Surface

