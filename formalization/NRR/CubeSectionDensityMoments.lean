import NRR.CubeSectionSupport
import NRR.BrunnMinkowskiBodySlices

/-! Fubini connects the actual directional first moment of a body to the
one-dimensional density translation produced by equality in slicing. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.CubeSectionDensityMoments
open ConvexSectionContinuity BrunnMinkowskiBodySlices CubeSectionSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem integrable_sectionMass_smul {C : Set (E × ℝ)} (compact : IsCompact C)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F)
    (hg : IntegrableOn (fun p : E × ℝ => g p.2) C volume) :
    Integrable (fun u => sectionMass C u • g u) volume := by
  have ms := compact.measurableSet
  have h := (hg.integrable_indicator ms).integral_prod_right
  apply h.congr
  filter_upwards with u
  have eq : (fun x : E => C.indicator (fun p => g p.2) (x,u)) =
      (fiber C u).indicator (fun _ => g u) := by
    funext x
    by_cases h : (x,u) ∈ C <;> simp [fiber,h]
  rw [eq,integral_indicator (compact_fiber compact u).measurableSet,setIntegral_const]
  rfl

theorem integrable_sectionMass_moment {C : Set (E × ℝ)} (compact : IsCompact C) :
    Integrable (fun u => u*sectionMass C u) volume := by
  simpa only [smul_eq_mul,mul_comm] using integrable_sectionMass_smul compact id
    (continuous_snd.continuousOn.integrableOn_compact compact)

/-- Translation of the genuine slice density changes the actual body's
directional first moment by its ordinary volume times the same shift. -/
theorem body_moment_of_sectionMass_shift {A B : Set (E × ℝ)}
    (compactA : IsCompact A) (compactB : IsCompact B) (c : ℝ)
    (shift : ∀ᵐ t ∂volume, sectionMass B (t+c) = sectionMass A t) :
    (∫ p in B,p.2 ∂volume) =
      (∫ p in A,p.2 ∂volume) + volume.real A*c := by
  have hA : (∫ p in A,p.2 ∂volume) =
      ∫ t,t*sectionMass A t ∂volume := by
    simpa only [smul_eq_mul,mul_comm] using integral_snd compactA id
      (continuous_snd.continuousOn.integrableOn_compact compactA)
  have hB : (∫ p in B,p.2 ∂volume) =
      ∫ t,t*sectionMass B t ∂volume := by
    simpa only [smul_eq_mul,mul_comm] using integral_snd compactB id
      (continuous_snd.continuousOn.integrableOn_compact compactB)
  rw [hA,hB,first_moment_of_density_shift _ _ c
    (integrable_sectionMass compactA) (integrable_sectionMass_moment compactA) shift,
    integral_sectionMass compactA]
  ring

theorem projection_shift_of_endpoints {A B : Set (E × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A) (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B) (fullB : (interior B).Nonempty)
    (c : ℝ) (lowerEq : lower B = lower A+c) (upperEq : upper B = upper A+c) :
    projection B = (fun t : ℝ => t+c) '' projection A := by
  rw [projection_eq_interval compactA convexA fullA,
    projection_eq_interval compactB convexB fullB,lowerEq,upperEq]
  ext t
  constructor
  · intro ht
    refine ⟨t-c,⟨by linarith [ht.1],by linarith [ht.2]⟩,by ring⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

/-- The interior density equality obtained from cumulative transport suffices
for the true body moment identity; the two endpoint slices may be exceptional. -/
theorem body_moment_of_interior_density_shift {A B : Set (E × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A) (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B) (fullB : (interior B).Nonempty)
    (c : ℝ) (lowerEq : lower B = lower A+c) (upperEq : upper B = upper A+c)
    (inside : ∀ t ∈ Ioo (lower A) (upper A), sectionMass B (t+c) = sectionMass A t) :
    (∫ p in B,p.2 ∂volume) =
      (∫ p in A,p.2 ∂volume) + volume.real A*c := by
  apply body_moment_of_sectionMass_shift compactA compactB c
  apply ae_density_shift_of_interval_support _ _ (lower A) (upper A) c inside
  · intro t ht
    exact sectionMass_zero_outside (by
      rwa [projection_eq_interval compactA convexA fullA])
  · intro t ht
    exact sectionMass_zero_outside (by
      rwa [projection_eq_interval compactB convexB fullB,lowerEq,upperEq])

end NRR.CubeSectionDensityMoments
