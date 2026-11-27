import NRR.BrunnMinkowskiSpace
import NRR.CubeSectionSupport

/-! Equality in the genuine three-dimensional slicing argument.
The cumulative transport is constructed from actual section volumes. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiEquality

open BrunnMinkowskiTransport BrunnMinkowskiSlices BrunnMinkowskiBodySlices
  BrunnMinkowskiPlane BrunnMinkowskiGeometry BrunnMinkowskiSpace
  ConvexSectionContinuity

abbrev Active := (ℝ × ℝ) × ℝ

/-- A translation produced by cumulative transport also translates both
endpoints of the open support intervals. -/
theorem endpoints_of_transport_translation {a b c d v : ℝ}
    (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass)
    (shift : ∀ x ∈ Ioo a b, transport A B x = x+v) :
    c = a+v ∧ d = b+v := by
  have himage : Ioo c d = Ioo (a+v) (b+v) := by
    rw [← transport_image A B equal, ← image_add_const_Ioo]
    exact image_congr shift
  constructor
  · have h := congrArg sInf himage
    simpa only [csInf_Ioo B.proper,csInf_Ioo (add_lt_add_right A.proper v)] using h
  · have h := congrArg sSup himage
    simpa only [csSup_Ioo B.proper,csSup_Ioo (add_lt_add_right A.proper v)] using h

/-- Actual equal-volume compact full-dimensional convex bodies attaining
three-dimensional midpoint equality have translated projection intervals
and translated section-volume densities. No equality assumption about the
individual planar sections is imposed. -/
theorem exists_sectionMass_translation_of_volume_midpoint_eq
    {A B : Set Active}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty)
    (equal : volume.real A = volume.real B)
    (equality : volume.real (minkowskiMidpoint A B) = volume.real A) :
    ∃ v : ℝ, lower B = lower A+v ∧ upper B = upper A+v ∧
      ∀ x ∈ Ioo (lower A) (upper A), sectionMass A x = sectionMass B (x+v) := by
  let DA := sectionDensity A compactA convexA fullA
  let DB := sectionDensity B compactB convexB fullB
  let T := transport DA DB
  have massEqual : DA.mass = DB.mass := by
    simpa only [DA,DB,sectionDensity_mass] using equal
  have sectionLower (s : ℝ) (hs : s ∈ Ioo (lower A) (upper A)) :
      ((Real.sqrt (DA.density s)+Real.sqrt (DB.density (T s)))/2)^2 ≤
        sectionMass (minkowskiMidpoint A B) (transportMidpoint T s) := by
    have ht := transport_mem DA DB massEqual s hs
    apply section_midpoint_lower_plane compactA convexA fullA compactB convexB fullB
    · change s ∈ interior (projection A)
      rwa [projection_eq_interval compactA convexA fullA,interior_Icc]
    · change T s ∈ interior (projection B)
      rwa [projection_eq_interval compactB convexB fullB,interior_Icc]
  have integrableG : IntegrableOn (sectionMass (minkowskiMidpoint A B))
      (transportMidpoint T '' Ioo (lower A) (upper A)) :=
    (integrable_sectionMass (compact_midpoint compactA compactB)).integrableOn
  have integralLower := mass_le_midpoint_integral DA DB massEqual
    (sectionMass (minkowskiMidpoint A B)) sectionLower integrableG
  have integralUpper : (∫ z in transportMidpoint T '' Ioo (lower A) (upper A),
      sectionMass (minkowskiMidpoint A B) z) ≤ DA.mass := by
    rw [sectionDensity_mass,← equality,← integral_sectionMass (compact_midpoint compactA compactB)]
    exact setIntegral_le_integral
      (integrable_sectionMass (compact_midpoint compactA compactB))
      (Eventually.of_forall fun _ => measureReal_nonneg)
  obtain ⟨v,hv⟩ := exists_translation_of_midpoint_integral_eq DA DB massEqual
    (sectionMass (minkowskiMidpoint A B)) sectionLower integrableG
    (le_antisymm integralUpper integralLower)
  have endpoints := endpoints_of_transport_translation DA DB massEqual (fun x hx => (hv x hx).1)
  exact ⟨v,endpoints.1,endpoints.2,fun x hx => (hv x hx).2⟩

/-- In the fixed height direction, the equality case translates the entire
projection and transforms the true first moment by mass times that shift. -/
theorem exists_projection_shift_and_moment_of_volume_midpoint_eq
    {A B : Set Active}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty)
    (equal : volume.real A = volume.real B)
    (equality : volume.real (minkowskiMidpoint A B) = volume.real A) :
    ∃ v : ℝ, projection B = (fun t : ℝ => t+v) '' projection A ∧
      (∫ x in B,x.2 ∂volume) = (∫ x in A,x.2 ∂volume)+volume.real A*v := by
  obtain ⟨v,hl,hu,hs⟩ := exists_sectionMass_translation_of_volume_midpoint_eq
    compactA convexA fullA compactB convexB fullB equal equality
  refine ⟨v,?_,?_⟩
  · rw [projection_eq_interval compactA convexA fullA,
      projection_eq_interval compactB convexB fullB,hl,hu,image_add_const_Icc]
  · have shift : ∀ᵐ t ∂volume, sectionMass B (t+v) = sectionMass A t :=
      CubeSectionSupport.ae_density_shift_of_interval_support
        (sectionMass A) (sectionMass B) (lower A) (upper A) v
        (fun t ht => (hs t ht).symm)
        (fun t ht => sectionMass_zero_outside (by
          rwa [projection_eq_interval compactA convexA fullA]))
        (fun t ht => sectionMass_zero_outside (by
          rwa [projection_eq_interval compactB convexB fullB,hl,hu]))
    have integrableMoment : Integrable (fun t => t*sectionMass A t) volume := by
      have hi : IntegrableOn (fun p : Active => p.2) A volume :=
        continuous_snd.continuousOn.integrableOn_compact compactA
      have hp := (hi.integrable_indicator compactA.measurableSet).integral_prod_right
      apply hp.congr
      filter_upwards with t
      have eq : (fun x : ℝ × ℝ => A.indicator (fun p : Active => p.2) (x,t)) =
          (fiber A t).indicator (fun _ => t) := by
        funext x
        by_cases h : (x,t) ∈ A <;> simp [fiber,h]
      rw [eq,integral_indicator (compact_fiber compactA t).measurableSet,setIntegral_const]
      simp only [smul_eq_mul,sectionMass,mul_comm]
    have moments := CubeSectionSupport.first_moment_of_density_shift
      (sectionMass A) (sectionMass B) v (integrable_sectionMass compactA) integrableMoment shift
    rw [integral_sectionMass compactA] at moments
    rw [integral_snd compactA (fun t => t)
      (continuous_snd.continuousOn.integrableOn_compact compactA),
      integral_snd compactB (fun t => t)
      (continuous_snd.continuousOn.integrableOn_compact compactB)]
    simpa only [smul_eq_mul,mul_comm] using moments

end NRR.BrunnMinkowskiEquality
