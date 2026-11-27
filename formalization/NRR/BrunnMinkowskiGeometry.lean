import NRR.BrunnMinkowskiPlane

/-! The normalized two-dimensional inequality for actual compact convex
bodies. All lower-dimensional section estimates are discharged here. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiGeometry

open ConvexSectionContinuity BrunnMinkowskiBodySlices
  BrunnMinkowskiTransport BrunnMinkowskiSlices BrunnMinkowskiPlane

section Midpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def minkowskiMidpoint (A B : Set E) : Set E :=
  (fun p : E × E => (1/2 : ℝ) • (p.1+p.2)) '' (A ×ˢ B)

theorem compact_midpoint {A B : Set E}
    (compactA : IsCompact A) (compactB : IsCompact B) :
    IsCompact (minkowskiMidpoint A B) :=
  (compactA.prod compactB).image (by fun_prop)

theorem midpoint_fiber_subset {A B : Set (E × ℝ)} (s t : ℝ) :
    minkowskiMidpoint (fiber A s) (fiber B t) ⊆
      fiber (minkowskiMidpoint A B) ((s+t)/2) := by
  rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  refine ⟨((x,s),(y,t)),⟨hx,hy⟩,?_⟩
  apply Prod.ext
  · rfl
  · change (1/2 : ℝ)*(s+t) = (s+t)/2
    ring

theorem midpoint_real_eq (A B : Set ℝ) :
    minkowskiMidpoint A B = BrunnMinkowskiSlices.midpointSet A B := by
  ext z
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    exact ⟨x+y,⟨x,hx,y,hy,rfl⟩,rfl⟩
  · rintro ⟨v,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨(x,y),⟨hx,hy⟩,rfl⟩

end Midpoint

/-- The actual one-dimensional convex fibers supply the section bound,
including all compactness, positivity and set-inclusion hypotheses. -/
theorem section_midpoint_lower_real {A B : Set (ℝ × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty)
    {s t : ℝ} (hs : s ∈ interior (projection A))
    (ht : t ∈ interior (projection B)) :
    (sectionMass A s+sectionMass B t)/2 ≤
      sectionMass (minkowskiMidpoint A B) ((s+t)/2) := by
  have vol := volume_midpoint_real (compact_fiber compactA s) (convex_fiber convexA s)
    ((full_fiber convexA fullA hs).mono interior_subset)
    (compact_fiber compactB t) (convex_fiber convexB t)
    ((full_fiber convexB fullB ht).mono interior_subset)
  have mono : volume.real (minkowskiMidpoint (fiber A s) (fiber B t)) ≤
      volume.real (fiber (minkowskiMidpoint A B) ((s+t)/2)) :=
    measureReal_mono (midpoint_fiber_subset (A := A) (B := B) s t)
      (compact_fiber (compact_midpoint compactA compactB) ((s+t)/2)).measure_lt_top.ne
  rw [midpoint_real_eq] at mono
  exact vol.symm.trans_le mono

/-- The genuine planar Brunn--Minkowski midpoint inequality, for arbitrary
full-dimensional compact convex bodies with no prescribed relation between
their areas. No abstract section inequality remains in the statement. -/
theorem volume_midpoint_plane {A B : Set (ℝ × ℝ)}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty) :
    ((Real.sqrt (volume.real A)+Real.sqrt (volume.real B))/2)^2 ≤
      volume.real (minkowskiMidpoint A B) := by
  let DA := sectionDensity A compactA convexA fullA
  let DB := sectionDensity B compactB convexB fullB
  let T := transport (normalizedDensity DA) (normalizedDensity DB)
  have equal : (normalizedDensity DA).mass = (normalizedDensity DB).mass := by simp
  have bound := sqrt_mass_le_midpoint_integral DA DB
    (sectionMass (minkowskiMidpoint A B)) (fun s hs => by
      have ht := transport_mem (normalizedDensity DA) (normalizedDensity DB) equal s hs
      apply section_midpoint_lower_real compactA convexA fullA compactB convexB fullB
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

end NRR.BrunnMinkowskiGeometry
