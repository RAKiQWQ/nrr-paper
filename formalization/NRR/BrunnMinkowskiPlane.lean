import NRR.BrunnMinkowskiBodySlices

/-! The two-dimensional Brunn--Minkowski inequality by normalized cumulative
transport and one-dimensional convex sections. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiPlane

open BrunnMinkowskiSlices BrunnMinkowskiTransport BrunnMinkowskiBodySlices

def normalizedDensity {a b : ℝ} (D : PositiveDensity a b) :
    PositiveDensity a b where
  density x := D.density x / D.mass
  proper := D.proper
  integrable := D.integrable.div_const D.mass
  positive x hx := div_pos (D.positive x hx) D.mass_pos
  continuous := D.continuous.div_const D.mass

@[simp] theorem normalizedDensity_mass {a b : ℝ} (D : PositiveDensity a b) :
    (normalizedDensity D).mass = 1 := by
  change (∫ x in a..b,D.density x / D.mass) = 1
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  exact mul_inv_cancel₀ D.mass_pos.ne'

private theorem normalized_jacobian_gap (a b M N : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hb : 0 < b) :
    ((a+b)/2)*((1+(a/M)/(b/N))/2) -
        ((Real.sqrt M+Real.sqrt N)/2)^2/M*a =
      (Real.sqrt M*b-Real.sqrt N*a)^2/(4*M*b) := by
  field_simp [hM.ne',hN.ne',hb.ne']
  ring_nf
  simp only [Real.sq_sqrt hM.le,Real.sq_sqrt hN.le]
  ring

private theorem normalized_jacobian_lower (a b M N : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hb : 0 < b) :
    ((Real.sqrt M+Real.sqrt N)/2)^2/M*a ≤
      ((a+b)/2)*((1+(a/M)/(b/N))/2) := by
  have nonneg : 0 ≤ (Real.sqrt M*b-Real.sqrt N*a)^2/(4*M*b) := by positivity
  rw [← normalized_jacobian_gap a b M N hM hN hb] at nonneg
  linarith

/-- Unequal masses are handled by a genuinely constructed transport between
the normalized densities. The section lower bound is the one-dimensional
arithmetic mean of interval lengths. -/
theorem sqrt_mass_le_midpoint_integral {a b c d : ℝ}
    (A : PositiveDensity a b) (B : PositiveDensity c d) (g : ℝ → ℝ)
    (lower : ∀ x ∈ Ioo a b,
      (A.density x+B.density (transport (normalizedDensity A) (normalizedDensity B) x))/2 ≤
        g (transportMidpoint (transport (normalizedDensity A) (normalizedDensity B)) x))
    (integrableG : IntegrableOn g
      (transportMidpoint (transport (normalizedDensity A) (normalizedDensity B)) '' Ioo a b)) :
    ((Real.sqrt A.mass+Real.sqrt B.mass)/2)^2 ≤
      ∫ z in transportMidpoint (transport (normalizedDensity A) (normalizedDensity B)) ''
        Ioo a b,g z := by
  let A' := normalizedDensity A
  let B' := normalizedDensity B
  let T := transport A' B'
  have eqmass : A'.mass = B'.mass := by simp only [A',B',normalizedDensity_mass]
  have mono : MonotoneOn T (Ioo a b) :=
    (strictMonoOn_transport A' B' eqmass).monotoneOn
  have derivative (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivWithinAt T ((A.density x/A.mass)/(B.density (T x)/B.mass)) (Ioo a b) x :=
    (hasDerivAt_transport A' B' eqmass x hx).hasDerivWithinAt
  have midpointDerivative (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivWithinAt (transportMidpoint T)
        ((1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2) (Ioo a b) x :=
    ((hasDerivWithinAt_id x (Ioo a b)).add (derivative x hx)).div_const 2
  have midpointMono := monotoneOn_transportMidpoint T mono
  have hint : IntegrableOn
      (fun x => ((1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2) *
        g (transportMidpoint T x)) (Ioo a b) := by
    simpa only [smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurableSet_Ioo midpointDerivative midpointMono g).mp integrableG
  let factor : ℝ := ((Real.sqrt A.mass+Real.sqrt B.mass)/2)^2/A.mass
  have bound (x : ℝ) (hx : x ∈ Ioo a b) :
      factor * A.density x ≤
      ((1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2) *
        g (transportMidpoint T x) := by
    have hxB : T x ∈ Ioo c d := transport_mem A' B' eqmass x hx
    have posB := B.positive _ hxB
    have hcoef : 0 ≤ (1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2 := by
      have posA := A.positive x hx
      have hM := A.mass_pos
      have hN := B.mass_pos
      positivity
    calc
      _ ≤ ((A.density x+B.density (T x))/2) *
          ((1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2) :=
        normalized_jacobian_lower _ _ _ _ A.mass_pos B.mass_pos posB
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_right (lower x hx) hcoef]
  have h := setIntegral_mono_on
    (A.integrableOn_Ioo.const_mul factor) hint measurableSet_Ioo bound
  rw [integral_const_mul,A.integral_Ioo] at h
  have cancel : factor*A.mass = ((Real.sqrt A.mass+Real.sqrt B.mass)/2)^2 := by
    exact div_mul_cancel₀ _ A.mass_pos.ne'
  rw [cancel] at h
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Ioo midpointDerivative midpointMono g]
  exact h

end NRR.BrunnMinkowskiPlane
