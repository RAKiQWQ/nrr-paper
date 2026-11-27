import NRR.Geometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Coordinate transport from the two-dimensional Euclidean space and its
product with height to explicit horizontal and vertical coordinates. -/

noncomputable section

open MeasureTheory Set

namespace NRR.CubePlaneCoordinates

/-- The two Euclidean coordinates, in their natural order. -/
def e : NRR.Space 2 ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem e_apply (u : NRR.Space 2) : e u = (u 0, u 1) := by
  simp [e, PiLp.continuousLinearEquiv]

/-- Horizontal coordinates together with the height coordinate. -/
def E : (NRR.Space 2 × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  e.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem E_apply (u : NRR.Space 2) (z : ℝ) :
    E (u, z) = ((u 0, u 1), z) := by
  simp [E]

def coordinateSquare : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

def coordinateCube : Set ((ℝ × ℝ) × ℝ) :=
  {p | p.1 ∈ coordinateSquare ∧ p.2 ∈ Icc (-1 : ℝ) 1}

def square : Set (NRR.Space 2) := e ⁻¹' coordinateSquare

def cube : Set (NRR.Space 2 × ℝ) := E ⁻¹' coordinateCube

@[simp] theorem mem_square (u : NRR.Space 2) :
    u ∈ square ↔ u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-1 : ℝ) 1 := by
  simp [square, coordinateSquare, e_apply]
  tauto

@[simp] theorem mem_cube (p : NRR.Space 2 × ℝ) :
    p ∈ cube ↔ p.1 0 ∈ Icc (-1 : ℝ) 1 ∧ p.1 1 ∈ Icc (-1 : ℝ) 1 ∧
      p.2 ∈ Icc (-1 : ℝ) 1 := by
  rcases p with ⟨u,z⟩
  simp [cube, coordinateCube, coordinateSquare, E_apply]
  tauto

@[simp] theorem image_square : e '' square = coordinateSquare := by
  ext p
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hp
    exact ⟨e.symm p, hp, e.apply_symm_apply p⟩

@[simp] theorem image_cube : E '' cube = coordinateCube := by
  ext p
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hp
    exact ⟨E.symm p, hp, E.apply_symm_apply p⟩

/-- The two-dimensional coordinate change preserves the actual volume measures. -/
theorem measurePreserving_e : MeasurePreserving e (volume : Measure (NRR.Space 2)) volume := by
  simpa [e, PiLp.continuousLinearEquiv] using
    (volume_preserving_finTwoArrow ℝ).comp
      (PiLp.volume_preserving_ofLp (ι := Fin 2))

/-- The full horizontal-height coordinate change preserves actual volume. -/
theorem measurePreserving_E :
    MeasurePreserving E (volume : Measure (NRR.Space 2 × ℝ)) volume := by
  rw [Measure.volume_eq_prod (NRR.Space 2) ℝ,
    Measure.volume_eq_prod (ℝ × ℝ) ℝ]
  simpa [E] using
    (measurePreserving_e.prod (MeasurePreserving.id (volume : Measure ℝ)))

/-- Change variables on any set under the volume-preserving cube coordinate
equivalence. This applies, in particular, to continuous densities and
measurable sets. -/
theorem setIntegral_image_E (B : Set (NRR.Space 2 × ℝ))
    (f : ((ℝ × ℝ) × ℝ) → ℝ) :
    ∫ y in E '' B, f y = ∫ x in B, f (E x) := by
  exact measurePreserving_E.setIntegral_image_emb E.toHomeomorph.measurableEmbedding f B


/-- The two coefficients of a linear height functional in horizontal
coordinates. -/
def planeSlope (P : NRR.Space 2 →L[ℝ] ℝ) : ℝ × ℝ :=
  (P (EuclideanSpace.single 0 1), P (EuclideanSpace.single 1 1))

/-- In coordinate variables, a linear height functional is its affine plane
with these two slopes. -/
theorem height_eq_planeSlope (P : NRR.Space 2 →L[ℝ] ℝ) (x : ℝ × ℝ) :
    P (e.symm x) = (planeSlope P).1 * x.1 + (planeSlope P).2 * x.2 := by
  have hcoord : e.symm x = x.1 • EuclideanSpace.single 0 1 +
      x.2 • EuclideanSpace.single 1 1 := by
    apply e.injective
    simp [e_apply, EuclideanSpace.single_apply]
  rw [hcoord, map_add, map_smul, map_smul]
  simp only [planeSlope, smul_eq_mul]
  ring

/-- Each coordinate slope is bounded in absolute value by the operator norm. -/
theorem abs_planeSlope_fst_le (P : NRR.Space 2 →L[ℝ] ℝ) :
    |(planeSlope P).1| ≤ ‖P‖ := by
  simpa [planeSlope, EuclideanSpace.norm_single] using
    (P.le_opNorm (EuclideanSpace.single 0 (1 : ℝ)))

theorem abs_planeSlope_snd_le (P : NRR.Space 2 →L[ℝ] ℝ) :
    |(planeSlope P).2| ≤ ‖P‖ := by
  simpa [planeSlope, EuclideanSpace.norm_single] using
    (P.le_opNorm (EuclideanSpace.single 1 (1 : ℝ)))
end NRR.CubePlaneCoordinates