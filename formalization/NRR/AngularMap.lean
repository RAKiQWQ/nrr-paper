import NRR.LocalModel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-! Homogeneous angular maps with exactly linear antipodal difference. -/

noncomputable section
open Set
open scoped NNReal

namespace NRR.AngularMap

def direction (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_direction_le (z : ℂ) : ‖direction z‖ ≤ 1 := by
  by_cases h : z = 0
  · simp [h, direction]
  · simp [direction, norm_ne_zero_iff.mpr h]

theorem radius_mul_direction (z : ℂ) : (‖z‖ : ℂ) * direction z = z := by
  by_cases h : z = 0
  · simp [h, direction]
  · have h' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    unfold direction
    field_simp

theorem direction_pos_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    direction (r * z) = direction z := by
  simp only [direction, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.ofReal_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0)

@[simp] theorem direction_neg (z : ℂ) : direction (-z) = -direction z := by simp [direction, neg_div]

/-- Multiplication by the radius compensates for the singularity of angular
normalization at zero. This estimate also holds when one argument is zero. -/
theorem weighted_direction_dist (x y : ℂ) :
    ‖x‖ * ‖direction x - direction y‖ ≤ 2 * ‖x - y‖ := by
  have he : (‖x‖ : ℂ) * (direction x - direction y) =
      (x-y) + ((‖y‖ : ℂ) - ‖x‖) * direction y := by
    rw [mul_sub, sub_mul, radius_mul_direction, radius_mul_direction]
    ring
  calc
    _ = ‖(‖x‖ : ℂ) * (direction x - direction y)‖ := by simp
    _ ≤ ‖x-y‖ + ‖((‖y‖ : ℂ) - ‖x‖) * direction y‖ := he ▸ norm_add_le .. 
    _ ≤ ‖x-y‖ + |‖y‖ - ‖x‖| := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) (norm_direction_le _)) _
    _ ≤ _ := by linarith [abs_norm_sub_norm_le y x, norm_sub_rev y x]

def radial (a : ℂ → ℝ) (z : ℂ) : ℂ := (a (direction z) : ℂ) * z

private theorem radial_bound {a : ℂ → ℝ} {A L : ℝ} (hL : 0 ≤ L)
    (ha : ∀ u, ‖u‖ ≤ 1 → |a u| ≤ A)
    (hlip : ∀ u, ‖u‖ ≤ 1 → ∀ v, ‖v‖ ≤ 1 → |a u - a v| ≤ L * ‖u-v‖)
    (x y : ℂ) : ‖radial a x - radial a y‖ ≤ (A + 2*L) * ‖x-y‖ := by
  let u := direction x
  let v := direction y
  have hu := norm_direction_le x
  have hv := norm_direction_le y
  have he : radial a x - radial a y = (a v : ℂ)*(x-y) + ((a u : ℂ)-a v)*x := by
    unfold radial
    dsimp [u,v]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ A * ‖x-y‖ + (L * ‖u-v‖) * ‖x‖ := by
      gcongr
      · exact ha v hv
      · exact hlip u hu v hv
    _ = A * ‖x-y‖ + L * (‖x‖ * ‖u-v‖) := by ring
    _ ≤ A * ‖x-y‖ + L * (2 * ‖x-y‖) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left (weighted_direction_dist x y) hL) _
    _ = _ := by ring

private theorem continuous_radial {a : ℂ → ℝ} {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (ha : ∀ u, ‖u‖ ≤ 1 → |a u| ≤ A)
    (hlip : ∀ u, ‖u‖ ≤ 1 → ∀ v, ‖v‖ ≤ 1 → |a u - a v| ≤ L * ‖u-v‖) :
    Continuous (radial a) :=
  (show LipschitzWith ⟨A+2*L, by positivity⟩ (radial a) from
    lipschitzWith_iff_norm_sub_le.mpr (radial_bound hL ha hlip)).continuous

/-- Positive bounded radial rescaling has an explicit reciprocal, even at the origin. -/
private def radialHomeomorph (a : ℂ → ℝ)
    (hpos : ∀ u, ‖u‖ ≤ 1 → 0 < a u) (hc : Continuous (radial a))
    (hci : Continuous (radial fun u => (a u)⁻¹)) : ℂ ≃ₜ ℂ where
  toFun := radial a
  invFun := radial fun u => (a u)⁻¹
  left_inv z := by
    have h := hpos _ (norm_direction_le z)
    simp [radial, direction_pos_mul _ h, h.ne']
  right_inv z := by
    have h := hpos _ (norm_direction_le z)
    simp only [radial, direction_pos_mul _ (inv_pos.mpr h)]
    simp [h.ne']
  continuous_toFun := hc
  continuous_invFun := hci

/-- A global Lipschitz perturbation of the identity of constant at most 1/2. -/
private def smallHomeomorph (f : ℂ → ℂ)
    (hf : ∀ x y, ‖f x - f y‖ ≤ (1/2 : ℝ)*‖x-y‖) : ℂ ≃ₜ ℂ := by
  let idL := ContinuousLinearEquiv.refl ℝ ℂ
  let c : ℝ≥0 := 1/2
  have ha : ApproximatesLinearOn (fun z => z + f z) idL.toContinuousLinearMap univ c := by
    intro x _ y _
    change ‖x + f x - (y + f y) - (x-y)‖ ≤ (c : ℝ) * ‖x-y‖
    rw [show x + f x - (y + f y) - (x-y) = f x - f y by ring]
    exact hf x y
  exact ha.toHomeomorph _ (f' := idL) (Or.inr (by
    change (1/2 : ℝ≥0) < ‖ContinuousLinearMap.id ℝ ℂ‖₊⁻¹
    rw [ContinuousLinearMap.nnnorm_id]
    norm_num))

/-- Uniform inverse estimate for the positive real part of the angular factor. -/
private theorem reciprocal_bound {a : ℂ → ℝ} {c L : ℝ} (hc : 0 < c)
    (hlower : ∀ u, ‖u‖ ≤ 1 → c ≤ a u)
    (hlip : ∀ u, ‖u‖ ≤ 1 → ∀ v, ‖v‖ ≤ 1 → |a u-a v| ≤ L*‖u-v‖)
    {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |(a u)⁻¹ - (a v)⁻¹| ≤ (L / c^2) * ‖u-v‖ := by
  have hp := hc.trans_le (hlower u hu)
  have hq := hc.trans_le (hlower v hv)
  have H : (a u)⁻¹ - (a v)⁻¹ = (a v - a u)/(a u * a v) := by field_simp
  rw [H, abs_div, abs_of_pos (mul_pos hp hq), abs_sub_comm]
  calc
    _ ≤ (L * ‖u-v‖)/(c*c) :=
      div_le_div₀ ((abs_nonneg _).trans (hlip u hu v hv)) (hlip u hu v hv) (mul_pos hc hc)
        (mul_le_mul (hlower u hu) (hlower v hv) hc.le hp.le)
    _ = _ := by ring

/-- Throughout the straight angular isotopy, a single choice of the imaginary
scale gives genuine plane homeomorphisms. The functions are sampled only at
normalized directions and zero. -/
theorem exists_isotopy (s v : ℂ → ℝ) {c A V L K : ℝ}
    (hc : 0 < c) (hcone : c ≤ 1) (hA : 1 ≤ A) (hV : 0 ≤ V) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hlo : ∀ u, ‖u‖ ≤ 1 → c ≤ 1 + s u) (hhi : ∀ u, ‖u‖ ≤ 1 → 1 + s u ≤ A)
    (hv : ∀ u, ‖u‖ ≤ 1 → |v u| ≤ V)
    (hsL : ∀ u, ‖u‖ ≤ 1 → ∀ w, ‖w‖ ≤ 1 → |s u - s w| ≤ L*‖u-w‖)
    (hvL : ∀ u, ‖u‖ ≤ 1 → ∀ w, ‖w‖ ≤ 1 → |v u - v w| ≤ K*‖u-w‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ h : ℂ ≃ₜ ℂ, ∀ z,
      h z = z + (t : ℂ) * ((s (direction z) : ℂ) +
        Complex.I * ε * (v (direction z) : ℂ)) * z := by
  let B := c⁻¹ + 2*(L/c^2)
  let M := V + 2*K
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let ε := 1 / (2*(1+M*B))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε * (M*B) ≤ 1/2 := by
    dsimp [ε]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  refine ⟨ε, hε, ?_⟩
  intro t ht
  let a := fun z => 1 + t * s z
  have hlo' (u : ℂ) (hu : ‖u‖ ≤ 1) : c ≤ a u := by
    dsimp [a]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hlo u hu)) ht.1,
      mul_nonneg (sub_nonneg.mpr hcone) (sub_nonneg.mpr ht.2)]
  have hp (u : ℂ) (hu : ‖u‖ ≤ 1) : 0 < a u := hc.trans_le (hlo' u hu)
  have hi' (u : ℂ) (hu : ‖u‖ ≤ 1) : |a u| ≤ A := by
    rw [abs_of_pos (hp u hu)]
    dsimp [a]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hhi u hu)) ht.1,
      mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr ht.2)]
  have hlip (u : ℂ) (hu : ‖u‖ ≤ 1) (w : ℂ) (hw : ‖w‖ ≤ 1) :
      |a u - a w| ≤ L*‖u-w‖ := by
    rw [show a u - a w = t * (s u-s w) by dsimp [a]; ring, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans (hsL u hu w hw)
  have hr (u : ℂ) (hu : ‖u‖ ≤ 1) : |(a u)⁻¹| ≤ c⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (hp u hu))]
    exact inv_anti₀ hc (hlo' u hu)
  have hrl := fun u (hu : ‖u‖ ≤ 1) w (hw : ‖w‖ ≤ 1) => reciprocal_bound hc hlo' hlip hu hw
  have hL' : 0 ≤ L/c^2 := by positivity
  let r := radialHomeomorph a hp (continuous_radial (by linarith) hL hi' hlip)
    (continuous_radial (inv_nonneg.mpr hc.le) hL' hr hrl)
  have hri (x y : ℂ) : ‖r.symm x - r.symm y‖ ≤ B*‖x-y‖ := radial_bound hL' hr hrl x y
  let f := fun x : ℂ => ((t:ℂ) * Complex.I * ε) * radial v (r.symm x)
  have hf (x y : ℂ) : ‖f x - f y‖ ≤ (1/2 : ℝ) * ‖x-y‖ := by
    dsimp only [f]
    rw [← mul_sub, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ht.1, abs_of_pos hε]
    calc
      _ ≤ (t*ε) * (M * ‖r.symm x - r.symm y‖) :=
        mul_le_mul_of_nonneg_left (radial_bound hK hv hvL _ _) (mul_nonneg ht.1 hε.le)
      _ ≤ ε * (M * (B * ‖x-y‖)) :=
        mul_le_mul (mul_le_of_le_one_left hε.le ht.2)
          (mul_le_mul_of_nonneg_left (hri x y) hM) (by positivity) hε.le
      _ = ε * (M*B) * ‖x-y‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  refine ⟨r.trans (smallHomeomorph f hf), fun z => ?_⟩
  change r z + ((t:ℂ)*Complex.I*ε) * radial v (r.symm (r z)) = _
  rw [r.symm_apply_apply]
  change radial a z + _ = _
  unfold radial
  simp only [a, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  ring

theorem antipodal_difference (s v : ℂ → ℝ) (hs : ∀ z, s (-z) = -s z)
    (hv : ∀ z, v (-z) = -v z) (ε : ℝ) (h : ℂ → ℂ)
    (hh : ∀ z, h z = z + ((s (direction z) : ℂ) + Complex.I * ε * (v (direction z) : ℂ)) * z) :
    ∀ z, h z - h (-z) = 2*z := by
  intro z
  rw [hh, hh]
  simp only [direction_neg, hs, hv, Complex.ofReal_neg]
  ring

/-- The same deformation is jointly continuous in time and the plane point.
This gives homotopies of differences of distinct points for degree calculations. -/
theorem continuous_isotopy (s v : ℂ → ℝ) {A V L K : ℝ}
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hs : ∀ u, ‖u‖ ≤ 1 → |s u| ≤ A) (hv : ∀ u, ‖u‖ ≤ 1 → |v u| ≤ V)
    (hsL : ∀ u, ‖u‖ ≤ 1 → ∀ w, ‖w‖ ≤ 1 → |s u - s w| ≤ L*‖u-w‖)
    (hvL : ∀ u, ‖u‖ ≤ 1 → ∀ w, ‖w‖ ≤ 1 → |v u - v w| ≤ K*‖u-w‖) (ε : ℝ) :
    Continuous (fun p : ℝ × ℂ => p.2 + (p.1 : ℂ) * ((s (direction p.2) : ℂ) +
      Complex.I * ε * (v (direction p.2) : ℂ)) * p.2) := by
  have Cs := (continuous_radial hA hL hs hsL).comp (continuous_snd (X := ℝ))
  have Cv := (continuous_radial hV hK hv hvL).comp (continuous_snd (X := ℝ))
  have C := continuous_snd.add ((Complex.continuous_ofReal.comp continuous_fst).mul
    (Cs.add (continuous_const.mul Cv : Continuous (fun p : ℝ × ℂ =>
      (Complex.I * ε) * radial v p.2))))
  convert C using 1
  ext p
  change _ = _ + _ * (radial s _ + _ * radial v _)
  unfold radial
  simp only [Function.comp_apply]
  ring

theorem branchSum_eq (s v : ℂ → ℝ) (hs : ∀ z, s (-z) = -s z) (hv : ∀ z, v (-z) = -v z)
    (ε : ℝ) (h : ℂ → ℂ)
    (hh : ∀ z, h z = z + ((s (direction z) : ℂ) + Complex.I * ε * (v (direction z) : ℂ)) * z)
    {n j : ℕ} (hj : j ≤ n) (z : ℂ) :
    LocalModel.branchSum h n j z = z * (((2*(j:ℝ)-n+n*s (direction z) : ℝ) : ℂ) +
      Complex.I * ((n:ℂ)*ε*v (direction z))) := by
  unfold LocalModel.branchSum
  rw [hh, hh, Nat.cast_sub hj]
  push_cast
  simp only [direction_neg, hs, hv, Complex.ofReal_neg]
  ring

/-- Missing the punctures gives avoidance of every branch sum on the whole
plane, including the two single-sign cases. -/
theorem avoids_branchSums (s v : ℂ → ℝ) (hs : ∀ z, s (-z) = -s z) (hv : ∀ z, v (-z) = -v z)
    {ε : ℝ} (hε : 0 < ε) (h : ℂ → ℂ)
    (hh : ∀ z, h z = z + ((s (direction z) : ℂ) + Complex.I * ε * (v (direction z) : ℂ)) * z)
    {n : ℕ} (hn : 0 < n) (miss : ∀ u : ℂ, ‖u‖ = 1 → ∀ j ≤ n, v u = 0 →
      2*(j:ℝ)-n+n*s u ≠ 0) :
    ∀ z ≠ 0, ∀ j ≤ n, LocalModel.branchSum h n j z ≠ 0 := by
  intro z hz j hj
  rw [branchSum_eq s v hs hv ε h hh hj]
  apply mul_ne_zero hz
  intro he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  rw [show (n:ℂ)*(ε:ℂ)*(v (direction z):ℂ) = ((n*ε*v (direction z):ℝ):ℂ) by push_cast; rfl] at hi hr
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
    zero_mul, one_mul, sub_zero, add_zero, zero_add] at hi hr
  have hne : (n:ℝ)*ε ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') hε.ne'
  exact miss (direction z) (by simp [direction, norm_ne_zero_iff.mpr hz]) j hj
    ((mul_eq_zero.mp hi).resolve_left hne) hr

theorem homogeneous (s v : ℂ → ℝ) (ε : ℝ) (h : ℂ → ℂ)
    (hh : ∀ z, h z = z + ((s (direction z) : ℂ) + Complex.I * ε * (v (direction z) : ℂ)) * z)
    {r : ℝ} (hr : 0 < r) (z : ℂ) : h (r*z) = (r:ℂ)*h z := by
  rw [hh, hh, direction_pos_mul r hr]
  ring

end NRR.AngularMap
