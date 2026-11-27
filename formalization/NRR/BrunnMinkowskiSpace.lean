import NRR.BrunnMinkowskiGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Three-dimensional Brunn--Minkowski from actual planar sections and
normalized cumulative transport. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiSpace

open BrunnMinkowskiSlices BrunnMinkowskiTransport BrunnMinkowskiPlane
  BrunnMinkowskiBodySlices ConvexSectionContinuity BrunnMinkowskiGeometry

theorem cube_root (x : ℝ) (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  simpa only [one_div] using Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0)

private theorem homogeneous_jacobian_gap (x y t : ℝ) (hy : y ≠ 0) :
    ((x+y)/2)^2*((1+t^3*x^2/y^2)/2)-x^2*((1+t)/2)^3 =
      (y-t*x)^2*(y^2+2*(1+t)*x*y+t*x^2)/(8*y^2) := by
  field_simp
  ring

private theorem normalized_jacobian_lower (a b M N t : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hM : 0 < M) (hN : 0 < N)
    (ht : 0 ≤ t) (cube : t^3 = N/M) :
    ((1+t)/2)^3*a ≤
      ((Real.sqrt a+Real.sqrt b)/2)^2*((1+(a/M)/(b/N))/2) := by
  have h := homogeneous_jacobian_gap (Real.sqrt a) (Real.sqrt b) t
    (Real.sqrt_pos.mpr hb).ne'
  simp only [Real.sq_sqrt ha,Real.sq_sqrt hb.le] at h
  have ratio : (a/M)/(b/N) = t^3*a/b := by
    rw [cube]
    field_simp
  have positive : 0 ≤ (Real.sqrt b-t*Real.sqrt a)^2*
      (b+2*(1+t)*Real.sqrt a*Real.sqrt b+t*a)/(8*b) := by positivity
  rw [ratio]
  linarith

/-- The full unequal-mass analytic step in dimension three. Its section
inequality is supplied by the genuine planar theorem below. -/
theorem root_mass_le_midpoint_integral {a b c d : ℝ}
    (A : PositiveDensity a b) (B : PositiveDensity c d) (g : ℝ → ℝ)
    (lower : ∀ x ∈ Ioo a b,
      ((Real.sqrt (A.density x)+
        Real.sqrt (B.density (transport (normalizedDensity A) (normalizedDensity B) x)))/2)^2 ≤
        g (transportMidpoint (transport (normalizedDensity A) (normalizedDensity B)) x))
    (integrableG : IntegrableOn g
      (transportMidpoint (transport (normalizedDensity A) (normalizedDensity B)) '' Ioo a b)) :
    ((A.mass^(1/3 : ℝ)+B.mass^(1/3 : ℝ))/2)^3 ≤
      ∫ z in transportMidpoint (transport (normalizedDensity A) (normalizedDensity B)) ''
        Ioo a b,g z := by
  let A' := normalizedDensity A
  let B' := normalizedDensity B
  let T := transport A' B'
  have eqmass : A'.mass = B'.mass := by simp only [A',B',normalizedDensity_mass]
  let t : ℝ := (B.mass/A.mass)^(1/3 : ℝ)
  have hM := A.mass_pos
  have hN := B.mass_pos
  have ht : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have tcube : t^3 = B.mass/A.mass := cube_root _ (by positivity)
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
  have bound (x : ℝ) (hx : x ∈ Ioo a b) :
      ((1+t)/2)^3*A.density x ≤
      ((1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2) *
        g (transportMidpoint T x) := by
    have posA := A.positive x hx
    have hxB := transport_mem A' B' eqmass x hx
    have posB := B.positive _ hxB
    have hcoef : 0 ≤ (1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2 := by positivity
    calc
      _ ≤ ((Real.sqrt (A.density x)+Real.sqrt (B.density (T x)))/2)^2 *
          ((1+(A.density x/A.mass)/(B.density (T x)/B.mass))/2) :=
        normalized_jacobian_lower _ _ _ _ _ posA.le posB hM hN ht tcube
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_right (lower x hx) hcoef]
  have h := setIntegral_mono_on
    (A.integrableOn_Ioo.const_mul (((1+t)/2)^3)) hint measurableSet_Ioo bound
  rw [integral_const_mul,A.integral_Ioo] at h
  have rootRatio : t = B.mass^(1/3 : ℝ)/A.mass^(1/3 : ℝ) :=
    Real.div_rpow hN.le hM.le _
  have rootProduct : A.mass^(1/3 : ℝ)*t = B.mass^(1/3 : ℝ) := by
    rw [rootRatio]
    field_simp
  have cancel : ((1+t)/2)^3*A.mass =
      ((A.mass^(1/3 : ℝ)+B.mass^(1/3 : ℝ))/2)^3 := by
    calc
      _ = ((1+t)/2)^3*(A.mass^(1/3 : ℝ))^3 := by rw [cube_root A.mass hM.le]
      _ = (A.mass^(1/3 : ℝ)*((1+t)/2))^3 := by ring
      _ = _ := by
        congr 1
        linarith [rootProduct]
  rw [cancel] at h
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Ioo midpointDerivative midpointMono g]
  exact h


instance planeHaar : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Genuine two-dimensional sections discharge the lower-dimensional
estimate used in the three-dimensional transport argument. -/
theorem section_midpoint_lower_plane {A B : Set ((ℝ × ℝ) × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty)
    {s t : ℝ} (hs : s ∈ interior (projection A))
    (ht : t ∈ interior (projection B)) :
    ((Real.sqrt (sectionMass A s)+Real.sqrt (sectionMass B t))/2)^2 ≤
      sectionMass (minkowskiMidpoint A B) ((s+t)/2) := by
  have vol := volume_midpoint_plane (compact_fiber compactA s) (convex_fiber convexA s)
    (full_fiber convexA fullA hs) (compact_fiber compactB t) (convex_fiber convexB t)
    (full_fiber convexB fullB ht)
  have mono : volume.real (minkowskiMidpoint (fiber A s) (fiber B t)) ≤
      volume.real (fiber (minkowskiMidpoint A B) ((s+t)/2)) :=
    measureReal_mono (midpoint_fiber_subset (A := A) (B := B) s t)
      (compact_fiber (compact_midpoint compactA compactB) ((s+t)/2)).measure_lt_top.ne
  exact vol.trans mono

/-- The genuine three-dimensional Brunn--Minkowski midpoint inequality
for arbitrary full-dimensional compact convex bodies. -/
theorem volume_midpoint_space {A B : Set ((ℝ × ℝ) × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty) :
    (((volume.real A)^(1/3 : ℝ)+(volume.real B)^(1/3 : ℝ))/2)^3 ≤
      volume.real (minkowskiMidpoint A B) := by
  let DA := sectionDensity A compactA convexA fullA
  let DB := sectionDensity B compactB convexB fullB
  let T := transport (normalizedDensity DA) (normalizedDensity DB)
  have equal : (normalizedDensity DA).mass = (normalizedDensity DB).mass := by simp
  have bound := root_mass_le_midpoint_integral DA DB
    (sectionMass (minkowskiMidpoint A B)) (fun s hs => by
      have ht := transport_mem (normalizedDensity DA) (normalizedDensity DB) equal s hs
      apply section_midpoint_lower_plane compactA convexA fullA compactB convexB fullB
      · change s ∈ interior (projection A)
        rwa [projection_eq_interval compactA convexA fullA,interior_Icc]
      · change T s ∈ interior (projection B)
        rwa [projection_eq_interval compactB convexB fullB,interior_Icc])
    (integrable_sectionMass (compact_midpoint compactA compactB)).integrableOn
  have upper : (∫ z in transportMidpoint T '' Ioo (lower A) (upper A),
      sectionMass (minkowskiMidpoint A B) z) ≤
      volume.real (minkowskiMidpoint A B) := by
    rw [← integral_sectionMass (compact_midpoint compactA compactB)]
    exact setIntegral_le_integral
      (integrable_sectionMass (compact_midpoint compactA compactB))
      (Eventually.of_forall fun _ => measureReal_nonneg)
  simpa only [DA,DB,sectionDensity_mass] using bound.trans upper

/-- Equal positive volumes give the form directly consumed by product
rigidity; this is a consequence of the full unequal-volume inequality. -/
theorem volume_le_midpoint_space {A B : Set ((ℝ × ℝ) × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty) (equal : volume.real A = volume.real B) :
    volume.real A ≤ volume.real (minkowskiMidpoint A B) := by
  have h := volume_midpoint_space compactA convexA fullA compactB convexB fullB
  rw [← equal] at h
  simpa only [add_self_div_two,cube_root _ measureReal_nonneg] using h


end NRR.BrunnMinkowskiSpace
