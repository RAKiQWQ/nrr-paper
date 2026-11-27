import NRR.AngularApproximation

open Set
open scoped unitInterval
noncomputable section

namespace NRR.AngularMap

open Surface

def center (n j : ℕ) : ℝ := 1 - 2*(j:ℝ)/n

private def unitLoop : C(Circle, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

private theorem unit_winding : complexWinding unitLoop (fun u => u.coe_ne_zero) = 1 := by
  let l : C(I, ℝ) := ⟨fun t => 2*Real.pi*t.val, by fun_prop⟩
  have h (t : I) : Circle.exp (l t) = (phaseOf unitLoop (fun u => u.coe_ne_zero)).comp periodPath t := by
    apply Circle.ext
    change (periodPath t : ℂ) = (periodPath t : ℂ) / (‖(periodPath t:ℂ)‖ : ℂ)
    simp
  rw [complexWinding, winding, phaseChange_eq _ l h]
  simp [l, Real.pi_ne_zero]

/-- Positive rescaling of the two Cartesian coordinates preserves winding
about the origin. The original modulus may vary along the loop. -/
private theorem rescale_winding (g : C(Circle, ℂ)) (gn : ∀ u, g u ≠ 0) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∃ (k : C(Circle, ℂ)) (kn : ∀ u, k u ≠ 0),
      (∀ u, k u = (a:ℂ)*(g u).re + Complex.I*b*(g u).im) ∧
      complexWinding k kn = complexWinding g gn := by
  let A (c : ℝ) (t : I) := 1-t.val+t.val*c
  have pos {c : ℝ} (hc : 0 < c) (t : I) : 0 < A c t := by
    by_cases ht : t.val = 0
    · simp [A, ht]
    · have := mul_pos (lt_of_le_of_ne t.2.1 (Ne.symm ht)) hc
      dsimp [A]
      linarith [t.2.2]
  let H : C(I × Circle, ℂ) := ⟨fun p => (A a p.1:ℂ)*(g p.2).re +
    Complex.I*(A b p.1:ℂ)*(g p.2).im, by dsimp [A]; fun_prop⟩
  have hH (p : I × Circle) : H p ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp [H, Complex.mul_re, Complex.mul_im, (pos ha p.1).ne', (pos hb p.1).ne'] at hr hi
    exact gn p.2 (Complex.ext hr hi)
  let k : C(Circle,ℂ) := ⟨fun u => H (1,u), by fun_prop⟩
  refine ⟨k, fun u => hH (1,u), fun u => by simp [k,H,A], ?_⟩
  apply (complexWinding_homotopy g k gn _ H hH ?_ (fun _ => rfl)).symm
  intro u
  simp [H,A, mul_comm Complex.I, Complex.re_add_im]

theorem realize_coordinates (p : Coordinates) {n : ℕ} (hn : 0 < n)
    (miss : ∀ j ≤ n, ∀ u, shifted p.loop (center n j) u ≠ 0) :
    ∃ (h : ℂ ≃ₜ ℂ) (avoid : ∀ z ≠ 0, ∀ j ≤ n, LocalModel.branchSum h n j z ≠ 0),
      h 0 = 0 ∧ (∀ z, h z - h (-z) = 2*z) ∧
      (∀ r : ℝ, 0 < r → ∀ z, h ((r:ℂ)*z) = (r:ℂ)*h z) ∧
      (∀ t : I, Function.Injective (fun z => straightAction h (t,z))) ∧
      ∀ j (hj : j ≤ n), complexWinding (branchLoop h n j) (fun u => avoid u u.coe_ne_zero j hj) =
        1 + complexWinding (shifted p.loop (center n j)) (miss j hj) := by
  have hwidth := (abs_nonneg _).trans (p.hs 0)
  have hbound := (abs_nonneg _).trans (p.hv 0)
  obtain ⟨ε, hε, family⟩ := exists_isotopy p.s p.v (sub_pos.mpr p.width_lt)
    (by linarith : 1-p.width ≤ 1) (by linarith : 1 ≤ 1+p.width)
    hbound p.L.2 p.K.2
    (fun u _ => by linarith [(abs_le.mp (p.hs u)).1])
    (fun u _ => by linarith [(abs_le.mp (p.hs u)).2]) (fun u _ => p.hv u)
    (fun u _ v _ => p.s_lip.dist_le_mul u v)
    (fun u _ v _ => p.v_lip.dist_le_mul u v)
  obtain ⟨h, h₁⟩ := family 1 ⟨zero_le_one, le_rfl⟩
  simp only [Complex.ofReal_one, one_mul] at h₁
  have hnr : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have alg (j : ℕ) : (n:ℝ) * center n j = n-2*j := by unfold center; field_simp
  have avoid := avoids_branchSums p.s p.v p.s_odd p.v_odd hε h h₁ hn (by
    intro u hu j hj hv he
    let w : Circle := ⟨u, mem_sphere_zero_iff_norm.mpr hu⟩
    apply miss j hj w
    change (p.s u:ℂ) + Complex.I * (p.v u:ℂ) - center n j = 0
    have hs : p.s u = center n j := by
      apply mul_left_cancel₀ hnr
      linarith only [he, alg j]
    simp [hs, hv])
  refine ⟨h, avoid, by simp [h₁], antipodal_difference _ _ p.s_odd p.v_odd _ _ h₁,
    fun _ hr z => homogeneous _ _ _ _ h₁ hr z,
    straightAction_injective_of_angular_family h _ h₁ (fun t ht => ?_), ?_⟩
  · obtain ⟨k,hk⟩ := family t ht
    exact ⟨k, fun z => by rw [hk]; ring⟩
  · intro j hj
    let g := shifted p.loop (center n j)
    obtain ⟨k, kn, hk, hw⟩ := rescale_winding g (miss j hj) (Nat.cast_pos.mpr hn) (mul_pos (Nat.cast_pos.mpr hn) hε)
    have he : branchLoop h n j = unitLoop * k := by
      ext u
      change LocalModel.branchSum h n j u = (u:ℂ) * k u
      rw [branchSum_eq p.s p.v p.s_odd p.v_odd ε h h₁ hj, hk]
      have hu : direction (u:ℂ) = u := by simp [direction]
      rw [hu]
      congr 1
      have hre : (g u).re = p.s u - center n j := by simp [g, shifted, Coordinates.loop, Complex.mul_re]
      have him : (g u).im = p.v u := by simp [g, shifted, Coordinates.loop, Complex.mul_im]
      rw [hre, him]
      push_cast
      have e : (n:ℂ) * (center n j:ℂ) = n-2*j := by exact_mod_cast alg j
      linear_combination e
    rw [show complexWinding (branchLoop h n j) _ = complexWinding (unitLoop*k)
        (fun u => mul_ne_zero u.coe_ne_zero (kn u)) by congr 1]
    rw [complexWinding_mul unitLoop k (fun u => u.coe_ne_zero) kn, unit_winding, hw]

end NRR.AngularMap
