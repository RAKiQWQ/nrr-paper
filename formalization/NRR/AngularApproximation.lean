import NRR.AngularMap
import NRR.SurfaceResidualWinding

open Set
open scoped NNReal
open scoped unitInterval
noncomputable section

namespace NRR.AngularMap

def antipode (u : Circle) : Circle := ⟨-(u:ℂ), mem_sphere_zero_iff_norm.mpr (by simp)⟩

/-- A bounded odd continuous coordinate on the circle can be replaced, with
arbitrarily small uniform error, by a globally Lipschitz odd coordinate on the
plane with the same bound. -/
theorem approximate_odd_coordinate (f : C(Circle, ℝ)) (hodd : ∀ u, f (antipode u) = -f u)
    {A : ℝ} (hb : ∀ u, |f u| ≤ A) {η : ℝ} (hη : 0 < η) :
    ∃ (F : ℂ → ℝ) (L : ℝ≥0), LipschitzWith L F ∧ (∀ z, F (-z) = -F z) ∧
      (∀ z, |F z| ≤ A) ∧ ∀ u : Circle, |F u - f u| ≤ η := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hb 1)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) η hη
  let K : ℝ≥0 := ⟨2*A/δ, by positivity⟩
  let F₀ (z : ℂ) := ⨅ u : Circle, f u + (K : ℝ)*dist z (u:ℂ)
  have bounded (z : ℂ) : BddBelow (Set.range fun u : Circle => f u + (K : ℝ)*dist z (u:ℂ)) := by
    refine ⟨-A, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact ((abs_le.mp (hb u)).1).trans (le_add_of_nonneg_right (by positivity))
  have lip : LipschitzWith K F₀ := LipschitzWith.of_le_add_mul K fun x y => by
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun u => ?_
    rw [sub_le_iff_le_add]
    calc
      _ ≤ f u + K * dist x (u:ℂ) := ciInf_le (bounded x) u
      _ ≤ f u + K * dist y (u:ℂ) + K * dist x y := by
        rw [add_assoc, ← mul_add, add_comm (dist y (u:ℂ))]
        exact add_le_add_left (mul_le_mul_of_nonneg_left (dist_triangle ..) K.2) _
  have err (u : Circle) : f u - η ≤ F₀ u ∧ F₀ u ≤ f u := by
    refine ⟨le_ciInf (fun w => ?_), by simpa using (ciInf_le (bounded u) u)⟩
    by_cases h : dist u w < δ
    · have close := hd h
      rw [Real.dist_eq] at close
      exact (by linarith [(abs_lt.mp close).2] : f u - η ≤ f w).trans
        (le_add_of_nonneg_right (by positivity))
    · have hle : δ ≤ dist (u:ℂ) (w:ℂ) := le_of_not_gt h
      have hscale : 2*A ≤ (K:ℝ)*dist (u:ℂ) (w:ℂ) := calc
        2*A = (K:ℝ)*δ := by dsimp [K]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hle K.2
      linarith [(abs_le.mp (hb u)).2, (abs_le.mp (hb w)).1]
  let G (z : ℂ) := max (-A) (min A (F₀ z))
  have clip : LipschitzWith 1 (fun y : ℝ => max (-A) (min A y)) :=
    (LipschitzWith.id.const_min A).const_max (-A)
  have hG : LipschitzWith K G := by simpa [G, Function.comp_def] using clip.comp lip
  have hbG (z : ℂ) : -A ≤ G z ∧ G z ≤ A :=
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have heG (u : Circle) : f u - η ≤ G u ∧ G u ≤ f u := by
    obtain ⟨lo,hi⟩ := err u
    have h := abs_le.mp (hb u)
    exact ⟨(le_min (by linarith) lo).trans (le_max_right _ _), max_le h.1 ((min_le_right _ _).trans hi)⟩
  let F (z : ℂ) := (G z - G (-z))/2
  refine ⟨F, K, LipschitzWith.of_dist_le_mul (fun x y => ?_), ?_, ?_, ?_⟩
  · have hxy := hG.dist_le_mul x y
    have hneg := hG.dist_le_mul (-x) (-y)
    rw [Real.dist_eq] at hxy hneg
    rw [dist_neg_neg] at hneg
    rw [Real.dist_eq, abs_le]
    dsimp only [F]
    obtain ⟨_,_⟩ := abs_le.mp hxy
    obtain ⟨_,_⟩ := abs_le.mp hneg
    constructor <;> linarith
  · intro z
    simp only [F, neg_neg]
    ring
  · intro z
    exact abs_le.mpr ⟨by dsimp [F]; linarith [(hbG z).1, (hbG (-z)).2],
      by dsimp [F]; linarith [(hbG z).2, (hbG (-z)).1]⟩
  · intro u
    have h := heG (antipode u)
    rw [hodd] at h
    change -f u - η ≤ G (-(u:ℂ)) ∧ G (-(u:ℂ)) ≤ -f u at h
    rw [abs_le]
    dsimp only [F]
    constructor <;> linarith [(heG u).1, (heG u).2]

/-- The Lipschitz data used to draw the same angular curve with bounded
coordinates throughout the unit disk. -/
structure Coordinates where
  s : ℂ → ℝ
  v : ℂ → ℝ
  width : ℝ
  width_lt : width < 1
  hs : ∀ z, |s z| ≤ width
  bound : ℝ
  hv : ∀ z, |v z| ≤ bound
  L : ℝ≥0
  K : ℝ≥0
  s_lip : LipschitzWith L s
  v_lip : LipschitzWith K v
  s_odd : ∀ z, s (-z) = -s z
  v_odd : ∀ z, v (-z) = -v z

def Coordinates.loop (a : Coordinates) : C(Circle, ℂ) :=
  ⟨fun u => (a.s u : ℂ) + Complex.I*(a.v u : ℂ),
    (Complex.continuous_ofReal.comp (a.s_lip.continuous.comp continuous_subtype_val)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (a.v_lip.continuous.comp continuous_subtype_val)))⟩

def shifted (P : C(Circle, ℂ)) (c : ℝ) : C(Circle, ℂ) := P - ContinuousMap.const _ (c:ℂ)

/-- Approximation preserves the winding about each of an arbitrary finite
set of punctures, including the central puncture. -/
theorem approximate_loop {ι : Type} [Finite ι] (P : C(Circle, ℂ))
    (odd : ∀ u, P (antipode u) = -P u) (strip : ∀ u, |(P u).re| < 1)
    (c : ι → ℝ) (miss : ∀ i u, shifted P (c i) u ≠ 0) :
    ∃ a : Coordinates, ∃ avoid : ∀ i u, shifted a.loop (c i) u ≠ 0,
      ∀ i, Surface.complexWinding (shifted a.loop (c i)) (avoid i) =
        Surface.complexWinding (shifted P (c i)) (miss i) := by
  classical
  letI := Fintype.ofFinite ι
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  let size (p : ι × Circle) := ‖P p.2 - (c p.1 : ℂ)‖
  have cs : Continuous size :=
    ((P.continuous.comp continuous_snd).sub
      (Complex.continuous_ofReal.comp (continuous_of_discreteTopology.comp continuous_fst))).norm
  obtain ⟨e, he, lower⟩ := isCompact_univ.exists_forall_le' cs.continuousOn
    (fun p _ => norm_pos_iff.mpr (miss p.1 p.2))
  let fr : C(Circle,ℝ) := ⟨fun u => (P u).re, Complex.continuous_re.comp P.continuous⟩
  let fi : C(Circle,ℝ) := ⟨fun u => (P u).im, Complex.continuous_im.comp P.continuous⟩
  obtain ⟨u, _, hu⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty fr.continuous.abs.continuousOn
  obtain ⟨v, _, hv⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty fi.continuous.abs.continuousOn
  have η : 0 < e/4 := by positivity
  obtain ⟨s, L, sl, so, sb, se⟩ := approximate_odd_coordinate fr
    (fun w => congrArg Complex.re (odd w)) (fun w => hu (mem_univ w)) η
  obtain ⟨b, K, bl, bo, bb, be⟩ := approximate_odd_coordinate fi
    (fun w => congrArg Complex.im (odd w)) (fun w => hv (mem_univ w)) η
  let a : Coordinates := ⟨s, b, |fr u|, strip u, sb, |fi v|, bb, L, K, sl, bl, so, bo⟩
  have err (w : Circle) : ‖a.loop w - P w‖ ≤ e/2 := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |((s w : ℂ) + Complex.I * (b w : ℂ) - P w).re| +
      |((s w : ℂ) + Complex.I * (b w : ℂ) - P w).im| ≤ _
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero, zero_add]
    linarith only [show |s w - (P w).re| ≤ e/4 from se w, show |b w - (P w).im| ≤ e/4 from be w]
  let H (i : ι) : C(I × Circle, ℂ) :=
    ⟨fun p => (P p.2 - (c i:ℂ)) + (p.1.val:ℂ)*(a.loop p.2 - P p.2),
      by fun_prop⟩
  have hH (i : ι) (p : I × Circle) : H i p ≠ 0 := by
    intro hz
    have heq : P p.2 - (c i:ℂ) = -((p.1.val:ℂ)*(a.loop p.2 - P p.2)) :=
      eq_neg_of_add_eq_zero_left hz
    have hlow : e ≤ ‖P p.2 - (c i:ℂ)‖ := lower (i,p.2) trivial
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.1.2.1] at hlow
    linarith [mul_le_of_le_one_left (norm_nonneg (a.loop p.2 - P p.2)) p.1.2.2, err p.2]
  have h0 (i : ι) (w : Circle) : H i (0,w) = shifted P (c i) w := by simp [H,shifted]
  have h1 (i : ι) (w : Circle) : H i (1,w) = shifted a.loop (c i) w := by simp [H,shifted]
  let hn := fun i w => h1 i w ▸ hH i (1,w)
  exact ⟨a, hn, fun i => (Surface.complexWinding_homotopy _ _ (miss i) (hn i)
    (H i) (hH i) (h0 i) (h1 i)).symm⟩

end NRR.AngularMap
