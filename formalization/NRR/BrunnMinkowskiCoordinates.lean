import NRR.BrunnMinkowskiWeighted
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Coordinate changes adapted to an arbitrary nonzero linear functional.
The same positive Haar factor transforms volume and all first moments. -/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal

namespace NRR.BrunnMinkowskiCoordinates

open BrunnMinkowskiWeighted BrunnMinkowskiGeometry

abbrev Active := (ℝ × ℝ) × ℝ

private def swapFirstLast : Active ≃ₗ[ℝ] Active where
  toFun x := ((x.2,x.1.2),x.1.1)
  invFun x := ((x.2,x.1.2),x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def swapSecondLast : Active ≃ₗ[ℝ] Active where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem exists_equiv_snd_of_last (L : Active →L[ℝ] ℝ)
    (hL : L ((0,0),1) ≠ 0) :
    ∃ e : Active ≃L[ℝ] Active, ∀ x, (e x).2 = L x := by
  let f : Active →ₗ[ℝ] Active := (LinearMap.fst ℝ (ℝ × ℝ) ℝ).prod L.toLinearMap
  have inj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x h
    have hfst : x.1 = 0 := congrArg Prod.fst h
    have hsnd : L x = 0 := congrArg Prod.snd h
    have heq : x = x.2 • ((0,0),1) := by
      apply Prod.ext
      · change x.1 = x.2 • (0 : ℝ × ℝ)
        simpa only [smul_zero] using hfst
      · simp
    have hz : x.2 = 0 := by
      rw [heq,map_smul,smul_eq_mul] at hsnd
      exact (mul_eq_zero.mp hsnd).resolve_right hL
    exact Prod.ext hfst hz
  refine ⟨(LinearEquiv.ofInjectiveEndo f inj).toContinuousLinearEquiv,?_⟩
  intro x
  rfl

/-- Any nonzero continuous linear functional is the height coordinate of
an actual continuous linear automorphism of three-dimensional space. -/
theorem exists_equiv_snd (L : Active →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ e : Active ≃L[ℝ] Active, ∀ x, (e x).2 = L x := by
  by_cases hz : L ((0,0),1) ≠ 0
  · exact exists_equiv_snd_of_last L hz
  by_cases hx : L ((1,0),0) ≠ 0
  · let s := swapFirstLast.toContinuousLinearEquiv
    obtain ⟨e,he⟩ := exists_equiv_snd_of_last (L.comp s.toContinuousLinearMap) hx
    refine ⟨s.trans e,fun x => ?_⟩
    exact he (s x)
  by_cases hy : L ((0,1),0) ≠ 0
  · let s := swapSecondLast.toContinuousLinearEquiv
    obtain ⟨e,he⟩ := exists_equiv_snd_of_last (L.comp s.toContinuousLinearMap) hy
    refine ⟨s.trans e,fun x => ?_⟩
    exact he (s x)
  exfalso
  apply hL
  apply ContinuousLinearMap.ext
  intro x
  change L x = 0
  have decomp : x = x.1.1 • (((1,0),0) : Active) +
      x.1.2 • (((0,1),0) : Active) + x.2 • (((0,0),1) : Active) := by
    ext <;> simp
  rw [decomp,map_add,map_add,map_smul,map_smul,map_smul]
  simp only [not_not] at hz hx hy
  simp only [hx,hy,hz,smul_zero,add_zero]

/-- The common positive factor for change of variables by `e`. -/
def haarFactor (e : Active ≃L[ℝ] Active) : ℝ≥0 :=
  Measure.addHaarScalarFactor ((volume : Measure Active).map e.symm) volume

theorem haarFactor_pos (e : Active ≃L[ℝ] Active) : 0 < haarFactor e :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem map_symm_volume (e : Active ≃L[ℝ] Active) :
    (volume : Measure Active).map e.symm = haarFactor e • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

/-- All set integrals transform by the same positive factor. No regularity
assumptions on the set or integrand are needed for this identity. -/
theorem integral_image (e : Active ≃L[ℝ] Active) (A : Set Active) (g : Active → ℝ) :
    (∫ y in e '' A, g y ∂volume) =
      (haarFactor e : ℝ) * ∫ x in A, g (e x) ∂volume := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Active))
    e.symm.toHomeomorph.toMeasurableEquiv (fun x => g (e x)) A
  change (∫ y in A, g (e y) ∂Measure.map e.symm volume) =
    ∫ x in e.symm ⁻¹' A,g (e (e.symm x)) ∂volume at h
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [map_symm_volume,Measure.restrict_smul,integral_smul_nnreal_measure] at h
  have hp : e.symm ⁻¹' A = e '' A := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y,hy,e.apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
  simpa only [hp,smul_eq_mul] using h.symm

theorem volume_image (e : Active ≃L[ℝ] Active) (A : Set Active) :
    volume.real (e '' A) = (haarFactor e : ℝ)*volume.real A := by
  simpa only [setIntegral_one_eq_measureReal] using integral_image e A (fun _ => 1)

theorem moment_image (e : Active ≃L[ℝ] Active) (A : Set Active) :
    (∫ y in e '' A, y.2 ∂volume) =
      (haarFactor e : ℝ) * ∫ x in A, (e x).2 ∂volume :=
  integral_image e A Prod.snd

theorem image_midpoint (e : Active ≃L[ℝ] Active) (A B : Set Active) :
    e '' minkowskiMidpoint A B = minkowskiMidpoint (e '' A) (e '' B) := by
  ext z
  constructor
  · rintro ⟨_,⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩,rfl⟩
    exact ⟨(e x,e y),⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,by simp⟩
  · rintro ⟨⟨_,_⟩,⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,rfl⟩
    exact ⟨_,⟨(x,y),⟨hx,hy⟩,rfl⟩,by simp⟩

theorem equal_volume_image (e : Active ≃L[ℝ] Active) {A B : Set Active}
    (h : volume.real A = volume.real B) :
    volume.real (e '' A) = volume.real (e '' B) := by
  rw [volume_image,volume_image,h]

theorem positive_volume_image (e : Active ≃L[ℝ] Active) {A : Set Active}
    (h : 0 < volume.real A) : 0 < volume.real (e '' A) := by
  rw [volume_image]
  exact mul_pos (haarFactor_pos e) h

theorem midpoint_volume_eq_image (e : Active ≃L[ℝ] Active) {A B : Set Active}
    (h : volume.real (minkowskiMidpoint A B) = volume.real A) :
    volume.real (minkowskiMidpoint (e '' A) (e '' B)) = volume.real (e '' A) := by
  rw [← image_midpoint,volume_image,volume_image,h]

end NRR.BrunnMinkowskiCoordinates
