import NRR.CircleParam
import NRR.AngularProfile
import NRR.AngularApproximation

/-! Finite symmetric winding prescriptions realized by actual odd circle maps. -/

noncomputable section
open Set Topology
open scoped unitInterval

namespace NRR.AngularLoops

open Surface AngularMap

def doubledLoop {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q) {a : region Q}
    (p : Path a (reflect hQ a)) : C(Circle, ℂ) :=
  ⟨fun u => (circleOfPath (doubled hQ p) u).val,
    continuous_subtype_val.comp (circleOfPath (doubled hQ p)).continuous⟩

@[simp] theorem doubledLoop_firstHalf {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q)
    {a : region Q} (p : Path a (reflect hQ a)) (t : I) :
    doubledLoop hQ p (periodPath (firstHalf t)) = (p t).val := by
  change (circleOfPath (doubled hQ p) (periodPath (firstHalf t))).val = _
  rw [circleOfPath_period, doubled_firstHalf]

@[simp] theorem doubledLoop_secondHalf {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q)
    {a : region Q} (p : Path a (reflect hQ a)) (t : I) :
    doubledLoop hQ p (periodPath (secondHalf t)) = -(p t).val := by
  change (circleOfPath (doubled hQ p) (periodPath (secondHalf t))).val = _
  rw [circleOfPath_period, doubled_secondHalf]
  rfl

theorem doubledLoop_odd {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q)
    {a : region Q} (p : Path a (reflect hQ a)) (u : Circle) :
    doubledLoop hQ p (antipode u) = -doubledLoop hQ p u := by
  have half (t : I) : antipode (periodPath (firstHalf t)) = periodPath (secondHalf t) := by
    apply Circle.ext
    exact (periodPath_secondHalf t).symm
  have twice (v : Circle) : antipode (antipode v) = v := by
    apply Circle.ext
    simp [antipode]
  obtain ⟨t, h | h⟩ := exists_half_parameter u
  · rw [h, half, doubledLoop_secondHalf, doubledLoop_firstHalf]
  · rw [h, ← half, twice, doubledLoop_firstHalf, half, doubledLoop_secondHalf, neg_neg]

theorem doubledLoop_avoids {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q)
    {a : region Q} (p : Path a (reflect hQ a)) (q : ℝ) (hq : q ∈ Q) (u : Circle) :
    shifted (doubledLoop hQ p) q u ≠ 0 :=
  sub_ne_zero.mpr ((circleOfPath (doubled hQ p) u).property.2 q hq)

theorem doubledLoop_winding {Q : Finset ℝ} (hQ : ∀ q ∈ Q, -q ∈ Q)
    {a : region Q} (p : Path a (reflect hQ a)) (q : ℝ) (hq : q ∈ Q) :
    complexWinding (shifted (doubledLoop hQ p) q) (doubledLoop_avoids hQ p q hq) =
      increment (probe q hq) (doubled hQ p) := by
  have phase_eq : phaseOf (shifted (doubledLoop hQ p) q) (doubledLoop_avoids hQ p q hq) =
      (probe q hq).comp (circleOfPath (doubled hQ p)) := by
    ext u
    rfl
  rw [complexWinding, phase_eq, winding_circleOfPath]

/-- This constructs the continuous odd curve itself, including all puncture
avoidance and winding witnesses; no curve or radius is assumed as input. -/
theorem exists_symmetric_loop (Q : Finset ℝ) (hQ : ∀ q ∈ Q, -q ∈ Q)
    (w : ℝ → ℤ) (symm : ∀ q ∈ Q, w (-q) = w q)
    (outside : ∀ q ∈ Q, 1 ≤ |q| → w q = 0)
    (k : ℤ) (central : w 0 = 2*k-1) :
    ∃ P : C(Circle, ℂ), (∀ u, P (antipode u) = -P u) ∧
      (∀ u, |(P u).re| < 1) ∧
      ∃ miss : ∀ q ∈ Q, ∀ u, shifted P q u ≠ 0,
        ∀ q (hq : q ∈ Q), complexWinding (shifted P q) (miss q hq) = (w q : ℝ) := by
  obtain ⟨δ, hδ, _, p, hp⟩ := exists_symmetric_half_profile Q hQ w symm outside k central
  refine ⟨doubledLoop hQ p, doubledLoop_odd hQ p, ?_, doubledLoop_avoids hQ p, ?_⟩
  · intro u
    exact (circleOfPath (doubled hQ p) u).property.1
  · intro q hq
    exact (doubledLoop_winding hQ p q hq).trans (hp q hq)

end NRR.AngularLoops
