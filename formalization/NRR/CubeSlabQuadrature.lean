import NRR.CubeFourMomentReadout
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Exact iterated quadrature for the four moments of a two-plane cube slab. -/

noncomputable section

open MeasureTheory

namespace NRR.CubeFourMomentReadout

/-- Height of an affine interface above the horizontal square. -/
def slabHeight (m t : ℝ) (p : Plane) (x y : ℝ) : ℝ :=
  t + 3 * m * (p.1 * x + p.2 * y)

/-- The oriented threefold integral between the two affine interfaces. -/
def slabIntegral (m top : ℝ) (lo hi : Plane) (g : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
    ∫ z in (slabHeight m (top - m) lo x y)..(slabHeight m top hi x y), g x y z

private theorem integral_cubic (a b c d : ℝ) :
    (∫ x in (-1 : ℝ)..1, a + b * x + c * x ^ 2 + d * x ^ 3) =
      2 * a + (2 / 3 : ℝ) * c := by
  have linear : (∫ x in (-1 : ℝ)..1, b * x) = 0 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
     intervalIntegral.integral_const, integral_pow, smul_eq_mul, linear]
  norm_num
  ring

private theorem integral_eq_cubic (f : ℝ → ℝ) (a b c d : ℝ)
    (h : ∀ x, f x = a + b * x + c * x ^ 2 + d * x ^ 3) :
    (∫ x in (-1 : ℝ)..1, f x) = 2 * a + (2 / 3 : ℝ) * c := by
  simp_rw [h]
  exact integral_cubic a b c d

private theorem square_height_x (m t : ℝ) (p : Plane) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      x * slabHeight m t p x y) = 4 * m * p.1 := by
  have inner (x : ℝ) :
      (∫ y in (-1 : ℝ)..1, x * slabHeight m t p x y) =
        2 * t * x + 6 * m * p.1 * x ^ 2 := by
    convert integral_eq_cubic (fun y => x * slabHeight m t p x y)
      (x * t + 3 * m * p.1 * x ^ 2)
      (3 * m * p.2 * x) 0 0 (fun y => by dsimp [slabHeight]; ring) using 1
    ring
  simp_rw [inner]
  convert integral_eq_cubic (fun x => 2 * t * x + 6 * m * p.1 * x ^ 2)
    0 (2 * t) (6 * m * p.1) 0 (fun x => by ring)
    using 1
  ring

private theorem square_height_y (m t : ℝ) (p : Plane) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      y * slabHeight m t p x y) = 4 * m * p.2 := by
  have inner (x : ℝ) :
      (∫ y in (-1 : ℝ)..1, y * slabHeight m t p x y) = 2 * m * p.2 := by
    convert integral_eq_cubic (fun y => y * slabHeight m t p x y)
      0 (t + 3 * m * p.1 * x) (3 * m * p.2) 0
      (fun y => by dsimp [slabHeight]; ring) using 1
    ring
  simp_rw [inner]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem square_height_sq_one_add_x (m t : ℝ) (p : Plane) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      (1 + x) * (slabHeight m t p x y ^ 2 / 2)) =
      2 * t ^ 2 + 6 * m ^ 2 * (p.1 ^ 2 + p.2 ^ 2) + 4 * m * t * p.1 := by
  have inner (x : ℝ) :
      (∫ y in (-1 : ℝ)..1, (1 + x) * (slabHeight m t p x y ^ 2 / 2)) =
        (1 + x) * ((t + 3 * m * p.1 * x) ^ 2 + 3 * m ^ 2 * p.2 ^ 2) := by
    convert integral_eq_cubic (fun y => (1 + x) * (slabHeight m t p x y ^ 2 / 2))
      ((1 + x) * (t + 3 * m * p.1 * x) ^ 2 / 2)
      ((1 + x) * (t + 3 * m * p.1 * x) * (3 * m * p.2))
      ((1 + x) * (3 * m * p.2) ^ 2 / 2) 0
      (fun y => by dsimp [slabHeight]; ring) using 1
    ring
  simp_rw [inner]
  convert integral_eq_cubic
    (fun x => (1 + x) * ((t + 3 * m * p.1 * x) ^ 2 + 3 * m ^ 2 * p.2 ^ 2))
    (t ^ 2 + 3 * m ^ 2 * p.2 ^ 2)
    (t ^ 2 + 3 * m ^ 2 * p.2 ^ 2 + 6 * t * m * p.1)
    (9 * m ^ 2 * p.1 ^ 2 + 6 * t * m * p.1) (9 * m ^ 2 * p.1 ^ 2)
    (fun x => by ring) using 1
  ring

private theorem square_height_sq_y (m t : ℝ) (p : Plane) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      y * (slabHeight m t p x y ^ 2 / 2)) = 4 * m * t * p.2 := by
  have inner (x : ℝ) :
      (∫ y in (-1 : ℝ)..1, y * (slabHeight m t p x y ^ 2 / 2)) =
        2 * m * p.2 * (t + 3 * m * p.1 * x) := by
    convert integral_eq_cubic (fun y => y * (slabHeight m t p x y ^ 2 / 2))
      0 ((t + 3 * m * p.1 * x) ^ 2 / 2)
      ((t + 3 * m * p.1 * x) * (3 * m * p.2)) ((3 * m * p.2) ^ 2 / 2)
      (fun y => by dsimp [slabHeight]; ring) using 1
    ring
  simp_rw [inner]
  convert integral_eq_cubic (fun x => 2 * m * p.2 * (t + 3 * m * p.1 * x))
    (2 * m * p.2 * t) (6 * m ^ 2 * p.1 * p.2) 0 0
    (fun x => by ring) using 1
  ring

private theorem square_integral_sub (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, f x y - g x y) =
      (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, f x y) -
      (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, g x y) := by
  have hfx (x : ℝ) : Continuous (f x) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hgx (x : ℝ) : Continuous (g x) :=
    hg.comp (continuous_const.prodMk continuous_id)
  simp_rw [intervalIntegral.integral_sub ((hfx _).intervalIntegrable _ _)
    ((hgx _).intervalIntegrable _ _)]
  exact intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf (-1) 1
      ).intervalIntegrable _ _)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg (-1) 1
      ).intervalIntegrable _ _)

/-- Exact unnormalized horizontal first moment in the first coordinate. -/
theorem slabIntegral_x (m top : ℝ) (lo hi : Plane) :
    slabIntegral m top lo hi (fun x _ _ => x) =
      4 * m * (cubeFourMoments m top lo hi).1.1 := by
  unfold slabIntegral
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have split (x y : ℝ) :
      (slabHeight m top hi x y - slabHeight m (top - m) lo x y) * x =
        x * slabHeight m top hi x y - x * slabHeight m (top - m) lo x y := by ring
  simp_rw [split]
  rw [square_integral_sub _ _
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)]
  rw [square_height_x, square_height_x]
  dsimp [cubeFourMoments]
  ring

/-- Exact unnormalized horizontal first moment in the second coordinate. -/
theorem slabIntegral_y (m top : ℝ) (lo hi : Plane) :
    slabIntegral m top lo hi (fun _ y _ => y) =
      4 * m * (cubeFourMoments m top lo hi).1.2 := by
  unfold slabIntegral
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have split (x y : ℝ) :
      (slabHeight m top hi x y - slabHeight m (top - m) lo x y) * y =
        y * slabHeight m top hi x y - y * slabHeight m (top - m) lo x y := by ring
  simp_rw [split]
  rw [square_integral_sub _ _
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)]
  rw [square_height_y, square_height_y]
  dsimp [cubeFourMoments]
  ring

/-- Exact unnormalized moment of `(1 + x) * z`. -/
theorem slabIntegral_one_add_x_mul_z (m top : ℝ) (lo hi : Plane) :
    slabIntegral m top lo hi (fun x _ z => (1 + x) * z) =
      4 * m * (cubeFourMoments m top lo hi).2.1 := by
  unfold slabIntegral
  have inner (x y : ℝ) :
      (∫ z in (slabHeight m (top - m) lo x y)..(slabHeight m top hi x y),
        (1 + x) * z) =
      (1 + x) * ((slabHeight m top hi x y ^ 2 -
        slabHeight m (top - m) lo x y ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
  simp_rw [inner]
  have split (x y : ℝ) :
      (1 + x) * ((slabHeight m top hi x y ^ 2 -
        slabHeight m (top - m) lo x y ^ 2) / 2) =
      (1 + x) * (slabHeight m top hi x y ^ 2 / 2) -
        (1 + x) * (slabHeight m (top - m) lo x y ^ 2 / 2) := by ring
  simp_rw [split]
  rw [square_integral_sub _ _
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)]
  rw [square_height_sq_one_add_x, square_height_sq_one_add_x]
  dsimp [cubeFourMoments]
  ring

/-- Exact unnormalized moment of `y * z`. -/
theorem slabIntegral_y_mul_z (m top : ℝ) (lo hi : Plane) :
    slabIntegral m top lo hi (fun _ y z => y * z) =
      4 * m * (cubeFourMoments m top lo hi).2.2 := by
  unfold slabIntegral
  have inner (x y : ℝ) :
      (∫ z in (slabHeight m (top - m) lo x y)..(slabHeight m top hi x y), y * z) =
      y * ((slabHeight m top hi x y ^ 2 -
        slabHeight m (top - m) lo x y ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
  simp_rw [inner]
  have split (x y : ℝ) :
      y * ((slabHeight m top hi x y ^ 2 -
        slabHeight m (top - m) lo x y ^ 2) / 2) =
      y * (slabHeight m top hi x y ^ 2 / 2) -
        y * (slabHeight m (top - m) lo x y ^ 2 / 2) := by ring
  simp_rw [split]
  rw [square_integral_sub _ _
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)
    (by dsimp [Function.uncurry, slabHeight]; fun_prop)]
  rw [square_height_sq_y, square_height_sq_y]
  dsimp [cubeFourMoments]
  ring

/-- The actual iterated slab integrals recover all four modeled moments after
normalization by the cube layer volume `4 * m`. -/
theorem slabIntegral_fourMoments (m top : ℝ) (lo hi : Plane) (hm : 0 < m) :
    (((1 / (4 * m)) * slabIntegral m top lo hi (fun x _ _ => x),
      (1 / (4 * m)) * slabIntegral m top lo hi (fun _ y _ => y)),
     ((1 / (4 * m)) * slabIntegral m top lo hi (fun x _ z => (1 + x) * z),
      (1 / (4 * m)) * slabIntegral m top lo hi (fun _ y z => y * z))) =
      cubeFourMoments m top lo hi := by
  rw [slabIntegral_x, slabIntegral_y, slabIntegral_one_add_x_mul_z, slabIntegral_y_mul_z]
  have hnorm (a : ℝ) : (1 / (4 * m)) * (4 * m * a) = a := by
    field_simp [hm.ne']
  simp only [hnorm]

end NRR.CubeFourMomentReadout
