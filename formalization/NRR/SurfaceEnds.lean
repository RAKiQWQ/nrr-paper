import NRR.SurfaceSheets
import NRR.LocalModel
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Parametrization at infinity of the simultaneous square roots.
The variable `t` is the inverse square root of the base radius. -/

open Set Topology Filter
noncomputable section

namespace NRR.Surface

/-- The normalized root on the end with the positive choice at infinity. -/
def endRoot (b : ℂ) (p : ℝ × Circle) : ℂ :=
  (p.2 : ℂ) * (1 + (p.1 : ℂ) ^ 2 * b / (p.2 : ℂ) ^ 2) ^ (2⁻¹ : ℂ)

@[simp] theorem endRoot_zero (b : ℂ) (u : Circle) : endRoot b (0, u) = u := by
  simp [endRoot]

theorem endRoot_sq (b : ℂ) (p : ℝ × Circle) :
    endRoot b p ^ 2 = (p.2 : ℂ) ^ 2 + (p.1 : ℂ) ^ 2 * b := by
  rw [endRoot, mul_pow, ← Complex.cpow_mul_nat]
  norm_num
  field_simp

theorem continuousAt_endRoot (b : ℂ) {p : ℝ × Circle} (hp : p.1 ^ 2 * ‖b‖ < 1) :
    ContinuousAt (endRoot b) p := by
  let g (v : ℝ × Circle) := 1 + (v.1 : ℂ) ^ 2 * b / (v.2 : ℂ) ^ 2
  have hc : Continuous g := by
    unfold g
    fun_prop (disch := simp)
  have hs : g p ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_of_norm_lt_one
    simpa [norm_div, norm_mul, norm_pow, Complex.norm_real, sq_abs] using hp
  exact (continuous_subtype_val.comp continuous_snd).continuousAt.mul
    ((continuousAt_cpow_const hs).comp hc.continuousAt)

def withSign (e : Bool) (z : ℂ) : ℂ := if e then -z else z

@[simp] theorem withSign_sq (e : Bool) (z : ℂ) : withSign e z ^ 2 = z ^ 2 := by
  cases e <;> simp [withSign]

theorem continuous_withSign (e : Bool) : Continuous (withSign e) := by
  cases e
  · exact continuous_id
  · exact continuous_neg

/-- All the roots with a fixed argument and radius are obtained by independent
sign choices, including points where one of the roots vanishes. -/
theorem exists_endRoot_signs {m : ℕ} (b : Fin m → ℂ) (z : Fin m → ℂ) {t : ℝ}
    (ht : t ≠ 0) (u : Circle) (h : ∀ i, z i ^ 2 = (u : ℂ)^2 / (t : ℂ)^2 + b i) :
    ∃ σ : Fin m → Bool, ∀ i, withSign (σ i) (endRoot (b i) (t,u)) = (t : ℂ) * z i := by
  have hc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have sq (i : Fin m) : ((t : ℂ) * z i) ^ 2 = endRoot (b i) (t,u) ^ 2 := by
    rw [mul_pow, h i, endRoot_sq]
    dsimp
    field_simp
  have hσ (i : Fin m) : ∃ e : Bool, withSign e (endRoot (b i) (t,u)) = (t : ℂ) * z i := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sq i) with hi | hi
    · exact ⟨false, hi.symm⟩
    · exact ⟨true, hi.symm⟩
  exact Classical.axiomOfChoice hσ

variable {m : ℕ}

/-- The rescaled difference from the common value. It has an actual value at
`t = 0`, with all roots equal to the appropriate sign of `u`. -/
def endResidual (h f : ℂ → ℂ) (b : Fin m → ℂ) (σ : Fin m → Bool) (p : ℝ × Circle) : ℂ :=
  f (-(∑ i, h (withSign (σ i) (endRoot (b i) p)))) - (p.2 : ℂ)^2

theorem continuousAt_endResidual {h f : ℂ → ℂ} (ch : Continuous h) (cf : Continuous f)
    (b : Fin m → ℂ) (σ : Fin m → Bool) {p : ℝ × Circle} (hp : ∀ i, p.1^2 * ‖b i‖ < 1) :
    ContinuousAt (endResidual h f b σ) p := by
  have cs (i : Fin m) : ContinuousAt (fun v => h (withSign (σ i) (endRoot (b i) v))) p :=
    ch.continuousAt.comp ((continuous_withSign _).continuousAt.comp (continuousAt_endRoot _ (hp i)))
  have csum : ContinuousAt (fun v => ∑ i, h (withSign (σ i) (endRoot (b i) v))) p :=
    tendsto_finset_sum _ fun i _ => cs i
  exact (cf.continuousAt.comp csum.neg).sub
    ((continuous_subtype_val.comp continuous_snd).continuousAt.pow 2)

/-- Nonvanishing at infinity persists in a collar of uniform width over
the entire circle and all sign choices. -/
theorem exists_end_collar {h f : ℂ → ℂ} (ch : Continuous h) (cf : Continuous f)
    (b : Fin m → ℂ) (hlim : ∀ (σ : Fin m → Bool) (u : Circle),
      f (-(∑ i, h (withSign (σ i) u))) ≠ (u : ℂ)^2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ σ u, endResidual h f b σ (t,u) ≠ 0 := by
  have per (σ : Fin m → Bool) : ∀ᶠ t : ℝ in 𝓝 0, ∀ u, endResidual h f b σ (t,u) ≠ 0 := by
    let good := {p : ℝ × Circle | endResidual h f b σ p ≠ 0}
    have inside (u : Circle) : (0,u) ∈ interior good :=
      mem_interior_iff_mem_nhds.mpr
        ((continuousAt_endResidual ch cf b σ (p := (0,u)) (fun _ => by norm_num)).eventually_ne
          (by simpa [endResidual] using sub_ne_zero.mpr (hlim σ u)))
    obtain ⟨U, V, ho, _, hU, hV, hs⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) (isCompact_univ (X := Circle))
        (isOpen_interior (s := good)) (fun ⟨t,u⟩ hp => by
          obtain rfl : t = 0 := hp.1
          exact inside u)
    filter_upwards [ho.mem_nhds (hU (mem_singleton _))] with t ht u
    exact interior_subset (hs ⟨ht, hV (mem_univ u)⟩)
  have hall := Filter.eventually_all.mpr per
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨ε, hε, fun t ht => hball (by simpa [Metric.mem_ball, Real.dist_eq] using ht)⟩

/-- The radial coordinate of every nonzero common value and its unit argument
on the squaring cover. -/
theorem exists_end_coordinates {q : ℂ} (hq : q ≠ 0) :
    ∃ (t : ℝ) (u : Circle), 0 < t ∧ (t⁻¹)^2 = ‖q‖ ∧
      (u : ℂ)^2 = (t : ℂ)^2 * q := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq q zero_lt_two
  have hw0 : w ≠ 0 := by intro e; simp [e, hq.symm] at hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let u : Circle := ⟨w / (‖w‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    simp [Complex.norm_real, hn.ne'])⟩
  refine ⟨‖w‖⁻¹, u, inv_pos.mpr hn, ?_, ?_⟩
  · rw [inv_inv, ← hw, norm_pow]
  · change (w / (‖w‖ : ℂ))^2 = _ * q
    rw [← hw, Complex.ofReal_inv, div_eq_mul_inv, mul_pow, mul_comm]

/-- In the homogeneous model the rescaled end residual equals `t²` times
the actual residual on each point of the square-root fiber. -/
theorem endResidual_eq_actual {h f : ℂ → ℂ}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, h ((r : ℂ)*z) = (r : ℂ)*h z)
    (hf : ∀ r : ℝ, 0 < r → ∀ z, f ((r : ℂ)*z) = (r : ℂ)^2*f z)
    (b z : Fin m → ℂ) {q : ℂ} (hz : ∀ i, z i ^ 2 = q + b i)
    {t : ℝ} (ht : 0 < t) (u : Circle) (hu : (u : ℂ)^2 = (t : ℂ)^2 * q) :
    ∃ σ, endResidual h f b σ (t,u) = (t : ℂ)^2 * (f (-(∑ i, h (z i))) - q) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  obtain ⟨σ, hσ⟩ := exists_endRoot_signs b z ht.ne' u (fun i => by
    rw [hu, mul_div_cancel_left₀ q (pow_ne_zero _ htc), hz])
  refine ⟨σ, ?_⟩
  unfold endResidual
  simp only [hσ, hh t ht, ← Finset.mul_sum, ← mul_neg, hf t ht, hu, mul_sub]

theorem nonzero_outside_disk {h f : ℂ → ℂ} (ch : Continuous h) (cf : Continuous f)
    (hh : ∀ r : ℝ, 0 < r → ∀ z, h ((r : ℂ)*z) = (r : ℂ)*h z)
    (hf : ∀ r : ℝ, 0 < r → ∀ z, f ((r : ℂ)*z) = (r : ℂ)^2*f z)
    (b : Fin m → ℂ) (hlim : ∀ (σ : Fin m → Bool) (u : Circle),
      f (-(∑ i, h (withSign (σ i) u))) ≠ (u : ℂ)^2) :
    ∃ T : ℝ, 0 < T ∧ ∀ (q : ℂ), T < ‖q‖ → ∀ z : Fin m → ℂ,
      (∀ i, z i ^ 2 = q + b i) → f (-(∑ i, h (z i))) ≠ q := by
  obtain ⟨ε, hε, avoid⟩ := exists_end_collar ch cf b hlim
  refine ⟨(ε⁻¹)^2, by positivity, ?_⟩
  intro q hq z hz he
  obtain ⟨t, u, ht, htq, hu⟩ := exists_end_coordinates (q := q)
    (norm_pos_iff.mp ((sq_nonneg _).trans_lt hq))
  have small : t < ε := by
    rw [← htq] at hq
    have hi : ε⁻¹ < t⁻¹ := by nlinarith [inv_pos.mpr ht, inv_pos.mpr hε]
    simpa using inv_lt_of_inv_lt₀ hε hi
  obtain ⟨σ, hσ⟩ := endResidual_eq_actual hh hf b z hz ht u hu
  exact avoid t (by simpa [abs_of_pos ht] using small) σ u (by rw [hσ, he, sub_self, mul_zero])

/-- For the square-after-homeomorphism model, avoiding every two-branch
sum guarantees the limit inequality on every end. -/
theorem end_limit_of_avoid [NeZero m] (h : ℂ ≃ₜ ℂ) (hzero : h 0 = 0)
    (avoid : ∀ z ≠ 0, ∀ j ≤ m+1, LocalModel.branchSum h (m+1) j z ≠ 0)
    (σ : Fin m → Bool) (u : Circle) :
    (h.symm (-(∑ i, h (withSign (σ i) u))))^2 ≠ (u : ℂ)^2 := by
  intro he
  let v (i : Fin m) := h (withSign (σ i) u)
  let w : Fin (m+1) → ℂ := Fin.cons (-(∑ i, v i)) v
  have hw : ∑ i, w i = 0 := by simp [w, Fin.sum_univ_succ]
  have hv (i : Fin (m+1)) : (h.symm (w i))^2 = (u : ℂ)^2 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact he
    · simp [w, v]
  have vanish := LocalModel.balanced_square_rigidity h.toEquiv hzero avoid w hw
    (fun i j => (hv i).trans (hv j).symm)
  have hh : h (withSign (σ 0) u) = 0 := vanish (Fin.succ 0)
  have hn := h.injective (hh.trans hzero.symm)
  cases e : σ 0 <;> simp [withSign, e] at hn

variable [NeZero m]

/-- Sign representatives modulo simultaneous reversal of all signs and of
the circle parameter. -/
abbrev EndLabel (m : ℕ) [NeZero m] := {σ : Fin m → Bool // σ 0 = false}

def endBoundary (b : Fin m → ℂ) (t : ℝ) : Set (locus b) :=
  {z | ‖z.val 0 ^ 2 - b 0‖ = (t⁻¹)^2}

def endPoint (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t) (σ : Fin m → Bool)
    (u : Circle) : locus b := by
  let z (i : Fin m) := withSign (σ i) (endRoot (b i) (t,u)) / (t : ℂ)
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have sq (i : Fin m) : z i ^ 2 - b i = (u : ℂ)^2 / (t : ℂ)^2 := by
    dsimp [z]
    rw [div_pow, withSign_sq, endRoot_sq]
    dsimp
    field_simp
    ring
  exact ⟨z, fun i => (sq i).trans (sq 0).symm⟩

theorem endPoint_base (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t) (σ : Fin m → Bool) (u : Circle) :
    (endPoint b ht σ u).val 0 ^ 2 - b 0 = (u : ℂ)^2 / (t : ℂ)^2 := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  change (withSign _ _ / _)^2 - _ = _
  rw [div_pow, withSign_sq, endRoot_sq]
  dsimp
  field_simp
  ring

def endBoundaryPoint (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t)
    (p : EndLabel m × Circle) : endBoundary b t := by
  refine ⟨endPoint b ht p.1.val p.2, ?_⟩
  change ‖_ ^ 2 - b 0‖ = _
  rw [endPoint_base]
  simp [norm_pow, Complex.norm_real, inv_pow]

private def antipode (u : Circle) : Circle := ⟨-(u : ℂ), mem_sphere_zero_iff_norm.mpr (by simp)⟩

private theorem endRoot_antipode (b : ℂ) (t : ℝ) (u : Circle) :
    endRoot b (t, antipode u) = -endRoot b (t,u) := by
  change -(u : ℂ) * (1 + (t : ℂ)^2 * b / (-(u : ℂ))^2) ^ (2⁻¹ : ℂ) = _
  simp [endRoot]

private theorem withSign_complement (e : Bool) (z : ℂ) : withSign (!e) (-z) = withSign e z := by
  cases e <;> simp [withSign]

private theorem endBoundaryPoint_surjective (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    Function.Surjective (endBoundaryPoint b ht) := by
  intro x
  let q := x.val.val 0 ^ 2 - b 0
  have hq : ‖q‖ = (t⁻¹)^2 := x.property
  have hq0 : q ≠ 0 := norm_pos_iff.mp (by rw [hq]; positivity)
  obtain ⟨s, u, hs, hsq, hu⟩ := exists_end_coordinates hq0
  have hst : s = t := by
    have hst' : s⁻¹ = t⁻¹ := by nlinarith [inv_pos.mpr ht, inv_pos.mpr hs]
    simpa using congrArg (fun r : ℝ => r⁻¹) hst'
  subst s
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  obtain ⟨σ, hσ⟩ := exists_endRoot_signs b x.val.val ht.ne' u (fun i => by
    rw [hu, mul_div_cancel_left₀ q (pow_ne_zero _ htc)]
    linear_combination x.val.property i)
  cases he : σ 0 with
  | false =>
    refine ⟨(⟨σ, he⟩, u), Subtype.ext (Subtype.ext (funext fun i => ?_))⟩
    change withSign (σ i) _ / (t : ℂ) = x.val.val i
    rw [hσ, mul_div_cancel_left₀ _ htc]
  | true =>
    let τ := fun i => !(σ i)
    refine ⟨(⟨τ, by simp [τ, he]⟩, antipode u), Subtype.ext (Subtype.ext (funext fun i => ?_))⟩
    change withSign (!(σ i)) (endRoot (b i) (t, antipode u)) / (t : ℂ) = x.val.val i
    rw [endRoot_antipode, withSign_complement, hσ, mul_div_cancel_left₀ _ htc]

private theorem endRoot_ne_zero (b : ℂ) {t : ℝ} (u : Circle) (hs : t^2 * ‖b‖ < 1) :
    endRoot b (t,u) ≠ 0 := by
  intro hz
  have e := endRoot_sq b (t,u)
  rw [hz, zero_pow two_ne_zero] at e
  have en := congrArg norm (eq_neg_of_add_eq_zero_left e.symm)
  simp [norm_pow, Complex.norm_real, sq_abs] at en
  linarith

private theorem endBoundaryPoint_injective (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ i, t^2 * ‖b i‖ < 1) : Function.Injective (endBoundaryPoint b ht) := by
  rintro ⟨σ,u⟩ ⟨τ,v⟩ he
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hb := congrArg (fun x : endBoundary b t => x.val.val 0 ^ 2 - b 0) he
  change (endPoint b ht σ.val u).val 0 ^ 2 - b 0 = (endPoint b ht τ.val v).val 0 ^ 2 - b 0 at hb
  rw [endPoint_base, endPoint_base] at hb
  have hu := sq_eq_sq_iff_eq_or_eq_neg.mp ((div_left_inj' (pow_ne_zero 2 htc)).mp hb)
  have roots (i : Fin m) : withSign (σ.val i) (endRoot (b i) (t,u)) =
      withSign (τ.val i) (endRoot (b i) (t,v)) := by
    apply (div_left_inj' htc).mp
    exact congrArg (fun x : endBoundary b t => x.val.val i) he
  have huv : u = v := by
    rcases hu with h | h
    · exact Circle.ext h
    · have e : u = antipode v := Circle.ext h
      have bad := roots 0
      simp [σ.property, τ.property, withSign, e, endRoot_antipode] at bad
      exact False.elim ((endRoot_ne_zero _ v (hs 0)) (by linear_combination -bad / 2))
  subst v
  refine Prod.ext (Subtype.ext (funext fun i => ?_)) rfl
  have hi := roots i
  cases heσ : σ.val i <;> cases heτ : τ.val i <;> try rfl
  all_goals simp [heσ, heτ, withSign] at hi
  all_goals exact False.elim ((endRoot_ne_zero _ u (hs i)) (by first | linear_combination hi / 2 | linear_combination -hi / 2))

/-- The entire boundary is a disjoint union of circles, counted once by
holding the first sign positive. The base along each circle is `u² / t²`. -/
def endBoundaryHomeomorph (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ i, t^2 * ‖b i‖ < 1) : (EndLabel m × Circle) ≃ₜ endBoundary b t := by
  apply Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (endBoundaryPoint b ht)
    ⟨endBoundaryPoint_injective b ht hs, endBoundaryPoint_surjective b ht⟩)
  change Continuous (endBoundaryPoint b ht)
  apply continuous_prod_of_discrete_left.mpr
  intro σ
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hr : Continuous (fun u : Circle => endRoot (b i) (t,u)) :=
    continuous_iff_continuousAt.mpr fun u =>
      (continuousAt_endRoot (b i) (p := (t,u)) (hs i)).comp
        (continuousAt_const.prodMk continuousAt_id)
  exact ((continuous_withSign (σ.val i)).comp hr).div_const _

theorem isClosed_endBoundary (b : Fin m → ℂ) (t : ℝ) : IsClosed (endBoundary b t) := by
  apply isClosed_eq _ continuous_const
  exact ((((continuous_apply (0 : Fin m)).comp continuous_subtype_val).pow 2).sub continuous_const).norm

/-- For gluing it suffices that the actual boundary circles contain the
topological frontier of the core. -/
theorem frontier_diskCore_subset_endBoundary (b : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    frontier (diskCore b ((t⁻¹)^2)) ⊆ endBoundary (fun i => (b i : ℂ)) t := by
  intro x hx
  have he := (projection b).continuous.frontier_preimage_subset
    (Metric.closedBall (0 : ℂ) ((t⁻¹)^2)) hx
  rw [frontier_closedBall _ (by positivity)] at he
  exact mem_sphere_zero_iff_norm.mp he

open scoped unitInterval

private theorem scaled_residual_on_endPoint {h f : ℂ → ℂ}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, h ((r : ℂ)*z) = (r : ℂ)*h z)
    (hf : ∀ r : ℝ, 0 < r → ∀ z, f ((r : ℂ)*z) = (r : ℂ)^2*f z)
    (b : Fin m → ℂ) {t : ℝ} (ht : 0 < t) (signs : Fin m → Bool) (u : Circle) :
    endResidual h f b signs (t,u) =
      (t : ℂ)^2 * (f (-(∑ i, h ((endPoint b ht signs u).val i))) - (u : ℂ)^2 / (t : ℂ)^2) := by
  have tc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have scales (i : Fin m) : (t : ℂ) * (endPoint b ht signs u).val i =
      withSign (signs i) (endRoot (b i) (t,u)) := by
    change _ * (_ / _) = _
    field_simp
  unfold endResidual
  dsimp
  simp only [← scales, hh t ht, ← Finset.mul_sum, ← mul_neg, hf t ht, mul_sub]
  field_simp

/-- The actual residual on each boundary circle has a nonvanishing
homotopy to the limiting unshifted residual. The interpolation in the
positive scalar removes the normalization at the finite end. -/
theorem exists_residual_end_homotopy {h f : ℂ → ℂ} (ch : Continuous h) (cf : Continuous f)
    (hh : ∀ r : ℝ, 0 < r → ∀ z, h ((r : ℂ)*z) = (r : ℂ)*h z)
    (hf : ∀ r : ℝ, 0 < r → ∀ z, f ((r : ℂ)*z) = (r : ℂ)^2*f z)
    (b : Fin m → ℂ) (hlim : ∀ (signs : Fin m → Bool) (u : Circle),
      f (-(∑ i, h (withSign (signs i) u))) ≠ (u : ℂ)^2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε → ∀ (signs : Fin m → Bool),
      ∃ H : C(I × Circle, ℂ), (∀ p, H p ≠ 0) ∧
        (∀ u, H (0,u) = f (-(∑ i, h (withSign (signs i) u))) - (u : ℂ)^2) ∧
        ∀ u, H (1,u) = f (-(∑ i, h ((endPoint b ht signs u).val i))) -
          ((endPoint b ht signs u).val 0 ^ 2 - b 0) := by
  obtain ⟨η,hη,avoid⟩ := exists_end_collar ch cf b hlim
  have small : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, r^2 * ‖b i‖ < 1 := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun r : ℝ => r^2 * ‖b i‖) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp small
  refine ⟨min η ε, lt_min hη hε, ?_⟩
  intro t ht hsmall signs
  let r (p : I × Circle) := t * p.1.val
  have bounds (p : I × Circle) : 0 ≤ r p ∧ r p ≤ t :=
    ⟨mul_nonneg ht.le p.1.property.1, by simpa [r] using mul_le_mul_of_nonneg_left p.1.property.2 ht.le⟩
  let base (p : I × Circle) := (r p, p.2)
  have cb : Continuous base := by unfold base r; fun_prop
  let w (p : I × Circle) := 1 - p.1.val + p.1.val * t^2
  have hw (p : I × Circle) : 0 < w p := by
    by_cases hz : p.1.val = 0
    · simp [w, hz]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr p.1.property.2)
        (mul_pos (lt_of_le_of_ne p.1.property.1 (Ne.symm hz)) (sq_pos_of_pos ht))
  have hn (p : I × Circle) : (w p : ℂ) ≠ 0 := by exact_mod_cast (hw p).ne'
  have cw : Continuous (fun p => (w p : ℂ)) := by unfold w; fun_prop
  have cG : Continuous (fun p => endResidual h f b signs (base p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hr := hball (show r p ∈ Metric.ball 0 ε by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (bounds p).1]
      exact (bounds p).2.trans_lt (lt_min_iff.mp hsmall).2)
    exact (continuousAt_endResidual ch cf b signs (p := base p) hr).comp cb.continuousAt
  refine ⟨⟨fun p => endResidual h f b signs (base p) / (w p : ℂ), cG.div cw hn⟩, ?_, ?_, ?_⟩
  · intro p
    exact div_ne_zero (avoid _ (by rw [abs_of_nonneg (bounds p).1]
                                   exact (bounds p).2.trans_lt (lt_min_iff.mp hsmall).1) signs p.2) (hn p)
  · intro u
    simp [w, base, r, endResidual]
  · intro u
    have tc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    simp [w, base, r, scaled_residual_on_endPoint hh hf b ht signs u, endPoint_base, tc]

end NRR.Surface

