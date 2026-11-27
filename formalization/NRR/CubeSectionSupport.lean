import NRR.CubeSectionTranslation
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Recover one actual translation from the projection translations and
first moments in all nonzero linear directions. This avoids a recursive
equality analysis of lower-dimensional Brunn--Minkowski sections. -/

noncomputable section
open Set Topology MeasureTheory

namespace NRR.CubeSectionSupport
open CubeProductMoments CubeSectionTranslation

/-- Nonzero continuous linear images detect containment in closed convex
sets. The zero direction is supplied by nonemptiness. -/
theorem subset_of_nonzero_linear_images {A B : Set Active}
    (closedB : IsClosed B) (convexB : Convex ℝ B) (nonemptyB : B.Nonempty)
    (images : ∀ (L : Active →L[ℝ] ℝ), L ≠ 0 → L '' A ⊆ L '' B) :
    A ⊆ B := by
  intro x hx
  have halfSpaces : x ∈ ⋂ L : Active →L[ℝ] ℝ, {z | ∃ y ∈ B, L z ≤ L y} := by
    apply mem_iInter.mpr
    intro L
    by_cases hL : L = 0
    · obtain ⟨y,hy⟩ := nonemptyB
      exact ⟨y,hy,by simp only [hL,ContinuousLinearMap.zero_apply,le_refl]⟩
    · obtain ⟨y,hy,he⟩ := images L hL (mem_image_of_mem L hx)
      exact ⟨y,hy,he.symm.le⟩
  rwa [iInter_halfSpaces_eq convexB closedB] at halfSpaces

theorem eq_of_nonzero_linear_images {A B : Set Active}
    (closedA : IsClosed A) (closedB : IsClosed B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (nonemptyA : A.Nonempty) (nonemptyB : B.Nonempty)
    (images : ∀ (L : Active →L[ℝ] ℝ), L ≠ 0 → L '' A = L '' B) :
    A = B :=
  Subset.antisymm
    (subset_of_nonzero_linear_images closedB convexB nonemptyB
      (fun L hL => (images L hL).subset))
    (subset_of_nonzero_linear_images closedA convexA nonemptyA
      (fun L hL => (images L hL).symm.subset))

theorem linear_image_translate (L : Active →L[ℝ] ℝ)
    (A : Set Active) (v : Active) :
    L '' translate A v = (fun t : ℝ => t + L v) '' (L '' A) := by
  simp only [translate,image_image,map_add]

/-- The scalar shift in every linear projection is the evaluation of one
vector. Then the original closed convex bodies are translates by that vector. -/
theorem eq_translate_of_linear_images {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (nonemptyA : A.Nonempty) (nonemptyB : B.Nonempty) (v : Active)
    (images : ∀ (L : Active →L[ℝ] ℝ), L ≠ 0 →
      L '' B = (fun t : ℝ => t + L v) '' (L '' A)) :
    B = translate A v := by
  have compactT : IsCompact (translate A v) :=
    compactA.image (continuous_id.add continuous_const)
  have convexT : Convex ℝ (translate A v) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ a b ha hb hab
    refine ⟨a • x+b • y,convexA hx hy ha hb hab,?_⟩
    calc
      (a • x+b • y)+v = (a • x+b • y)+(a+b) • v := by rw [hab,one_smul]
      _ = a • (x+v)+b • (y+v) := by module
  apply eq_of_nonzero_linear_images compactB.isClosed compactT.isClosed
    convexB convexT nonemptyB (nonemptyA.image (fun x => x+v))
  intro L hL
  exact (images L hL).trans (linear_image_translate L A v).symm

/-- The ordinary volume centroid of the actual compact body. -/
def volumeCentroid (A : Set Active) : Active :=
  (volume.real A)⁻¹ • ∫ x in A, x ∂volume

theorem linear_volumeCentroid (A : Set Active) (compactA : IsCompact A)
    (L : Active →L[ℝ] ℝ) :
    L (volumeCentroid A) = (volume.real A)⁻¹ * ∫ x in A, L x ∂volume := by
  have hi : IntegrableOn id A volume :=
    continuous_id.continuousOn.integrableOn_compact compactA
  have comm := L.integral_comp_comm hi
  change (∫ x in A,L x ∂volume) = L (∫ x in A,x ∂volume) at comm
  rw [volumeCentroid,map_smul,← comm]
  rfl

/-- In the equality case of slicing, the one-dimensional translation shifts
are fixed by the actual first moments. Therefore all directional translates
come from the same centroid difference, and the bodies themselves translate. -/
theorem eq_translate_of_projection_shifts_and_moments {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (positiveA : 0 < volume.real A) (equal : volume.real A = volume.real B)
    (shifts : ∀ (L : Active →L[ℝ] ℝ), L ≠ 0 → ∃ c : ℝ,
      L '' B = (fun t : ℝ => t+c) '' (L '' A) ∧
        (∫ x in B,L x ∂volume) =
          (∫ x in A,L x ∂volume) + volume.real A*c) :
    B = translate A (volumeCentroid B-volumeCentroid A) := by
  have nonemptyA : A.Nonempty := by
    by_contra h
    have he : A = ∅ := not_nonempty_iff_eq_empty.mp h
    simpa only [he,measureReal_empty,lt_self_iff_false] using positiveA
  have nonemptyB : B.Nonempty := by
    by_contra h
    have he : B = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [he,measureReal_empty] at equal
    exact positiveA.ne' equal
  apply eq_translate_of_linear_images compactA compactB convexA convexB nonemptyA nonemptyB
  intro L hL
  obtain ⟨c,himage,hmoment⟩ := shifts L hL
  have hc : L (volumeCentroid B-volumeCentroid A) = c := by
    rw [map_sub,linear_volumeCentroid B compactB,linear_volumeCentroid A compactA,
      ← equal,hmoment]
    field_simp [positiveA.ne']
    ring
  simpa only [hc] using himage


/-- A translation identity of slice densities on their open projection
intervals extends almost everywhere to the entire line. Endpoint densities
are allowed to be discontinuous and need not match. -/
theorem ae_density_shift_of_interval_support
    (f g : ℝ → ℝ) (a b c : ℝ)
    (inside : ∀ t ∈ Ioo a b, g (t+c) = f t)
    (outsideF : ∀ t ∉ Icc a b, f t = 0)
    (outsideG : ∀ t ∉ Icc (a+c) (b+c), g t = 0) :
    ∀ᵐ t ∂volume, g (t+c) = f t := by
  filter_upwards [(countable_singleton a).ae_notMem (volume : Measure ℝ),
    (countable_singleton b).ae_notMem (volume : Measure ℝ)] with t ha hb
  have hta : t ≠ a := by simpa only [mem_singleton_iff] using ha
  have htb : t ≠ b := by simpa only [mem_singleton_iff] using hb
  by_cases ht : t ∈ Icc a b
  · exact inside t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
  · have hg : t+c ∉ Icc (a+c) (b+c) := by
      intro h
      exact ht ⟨by linarith [h.1],by linarith [h.2]⟩
    rw [outsideF t ht,outsideG (t+c) hg]

/-- Actual first moments of translated slice densities transform by the
ordinary mass times the same scalar shift. -/
theorem first_moment_of_density_shift (f g : ℝ → ℝ) (c : ℝ)
    (integrableF : Integrable f volume)
    (integrableMoment : Integrable (fun t => t*f t) volume)
    (shift : ∀ᵐ t ∂volume, g (t+c) = f t) :
    (∫ t,t*g t ∂volume) =
      (∫ t,t*f t ∂volume) + c*(∫ t,f t ∂volume) := by
  calc
    _ = ∫ t,(t+c)*g (t+c) ∂volume :=
      (integral_add_right_eq_self (fun t : ℝ => t*g t) c).symm
    _ = ∫ t,(t+c)*f t ∂volume := by
      apply integral_congr_ae
      filter_upwards [shift] with t ht
      rw [ht]
    _ = (∫ t,t*f t ∂volume) + c*(∫ t,f t ∂volume) := by
      simp_rw [add_mul]
      rw [integral_add integrableMoment (integrableF.const_mul c),integral_const_mul]

end NRR.CubeSectionSupport
