import NRR.BrunnMinkowskiEquality
import NRR.BrunnMinkowskiCoordinates

/-! The actual three-dimensional Brunn--Minkowski equality theorem.
All directional scalar shifts are forced to be one centroid difference. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiRigidity

open BrunnMinkowskiBodySlices BrunnMinkowskiGeometry BrunnMinkowskiSpace
  BrunnMinkowskiWeighted BrunnMinkowskiEquality BrunnMinkowskiCoordinates
  CubeSectionSupport CubeSectionTranslation

abbrev Active := (ℝ × ℝ) × ℝ

/-- Midpoint equality yields translated projections and the matching true
first-moment shift in every nonzero linear direction. -/
theorem directional_shift_of_volume_midpoint_eq
    {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (positiveA : 0 < volume.real A) (equal : volume.real A = volume.real B)
    (equality : volume.real (minkowskiMidpoint A B) = volume.real A)
    (L : Active →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ c : ℝ, L '' B = (fun t : ℝ => t+c) '' (L '' A) ∧
      (∫ x in B,L x ∂volume) = (∫ x in A,L x ∂volume)+volume.real A*c := by
  obtain ⟨e,he⟩ := exists_equiv_snd L hL
  have cA := compactA.image e.continuous
  have cB := compactB.image e.continuous
  have vA : Convex ℝ (e '' A) := convexA.linear_image e.toLinearMap
  have vB : Convex ℝ (e '' B) := convexB.linear_image e.toLinearMap
  have fA := full_of_volume_pos vA (positive_volume_image e positiveA)
  have fB := full_of_volume_pos vB (positive_volume_image e (equal ▸ positiveA))
  obtain ⟨c,hp,hm⟩ := exists_projection_shift_and_moment_of_volume_midpoint_eq
    cA vA fA cB vB fB (equal_volume_image e equal) (midpoint_volume_eq_image e equality)
  refine ⟨c,?_,?_⟩
  · simpa only [projection,image_image,he] using hp
  · rw [moment_image,moment_image,volume_image] at hm
    simp_rw [he] at hm
    have factorNonzero : (haarFactor e : ℝ) ≠ 0 :=
      ne_of_gt (show (0 : ℝ) < (haarFactor e : ℝ) from haarFactor_pos e)
    apply mul_left_cancel₀ factorNonzero
    calc
      _ = (haarFactor e : ℝ)*(∫ x in A,L x ∂volume)+
          ((haarFactor e : ℝ)*volume.real A)*c := hm
      _ = _ := by ring

/-- Genuine equal-volume compact convex bodies attaining the
three-dimensional midpoint bound are translates. The translation is their
actual volume-centroid difference; no geometric equality premise remains. -/
theorem eq_translate_of_volume_midpoint_eq
    {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (positiveA : 0 < volume.real A) (equal : volume.real A = volume.real B)
    (equality : volume.real (minkowskiMidpoint A B) = volume.real A) :
    B = translate A (volumeCentroid B-volumeCentroid A) := by
  apply eq_translate_of_projection_shifts_and_moments compactA compactB
    convexA convexB positiveA equal
  exact directional_shift_of_volume_midpoint_eq compactA compactB convexA convexB
    positiveA equal equality

/-- Existential form of the actual three-dimensional equality theorem. -/
theorem exists_translation_of_volume_midpoint_eq
    {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (positiveA : 0 < volume.real A) (equal : volume.real A = volume.real B)
    (equality : volume.real (minkowskiMidpoint A B) = volume.real A) :
    ∃ w : Active, B = translate A w :=
  ⟨_,eq_translate_of_volume_midpoint_eq compactA compactB convexA convexB
    positiveA equal equality⟩

/-- Both ordinary Brunn--Minkowski inputs needed for actual partition
rigidity, now established from the bodies themselves. -/
theorem midpoint_rigidity
    (A B : Set Active)
    (compactA : IsCompact A) (compactB : IsCompact B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (positiveA : 0 < volume.real A) (equal : volume.real A = volume.real B) :
    volume.real A ≤ volume.real (minkowskiMidpoint A B) ∧
      (volume.real (minkowskiMidpoint A B) = volume.real A →
        ∃ w : Active, B = translate A w) := by
  exact ⟨volume_le_midpoint_space compactA convexA (full_of_volume_pos convexA positiveA)
    compactB convexB (full_of_volume_pos convexB (equal ▸ positiveA)) equal,
    exists_translation_of_volume_midpoint_eq compactA compactB convexA convexB positiveA equal⟩

end NRR.BrunnMinkowskiRigidity