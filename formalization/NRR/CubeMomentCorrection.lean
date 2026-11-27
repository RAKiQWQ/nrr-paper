import NRR.CubeFourMomentReadout
import NRR.PlanarScaling
import NRR.GlobalAssembly

/-! The bounded, continuous four-moment correction for the uniform three-dimensional cube.
The input is exactly `(W,V) : (ℝ × ℝ) × (ℝ × ℝ)`. No integration or
geometric identification of these inputs is assumed here. -/

noncomputable section
open scoped BigOperators

namespace NRR.CubeMomentCorrection

open CubeFourMomentReadout LocalModel RootSums

abbrev Input := Plane × Plane

/-- Identify the two active real coordinates with the complex plane. -/
def toComplex (p : Plane) : ℂ := ⟨p.1, p.2⟩

@[simp] theorem toComplex_add (p q : Plane) :
    toComplex (p + q) = toComplex p + toComplex q := rfl

@[simp] theorem toComplex_sub (p q : Plane) :
    toComplex (p - q) = toComplex p - toComplex q := rfl

theorem continuous_toComplex : Continuous toComplex := by
  have hc : Continuous (fun p : Plane => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  convert hc using 1
  funext p
  apply Complex.ext <;> simp [toComplex]

/-- The first pair of the four-moment input is the horizontal moment. -/
def horizontal : C(Input, ℂ) :=
  ⟨fun x => toComplex x.1, continuous_toComplex.comp continuous_fst⟩

/-- On the special (second) layer this reads `(p₁,-p₂)`. The positive
max denominator in `lowerReadout` makes this continuous on *all* inputs. -/
def interfaceReading (thickness top : ℝ) (hm : 0 < thickness) :
    C(Input, ℂ × ℂ) :=
  ⟨fun x => (toComplex (lowerReadout thickness top x),
      -toComplex (lowerReadout thickness top x + x.1)), by
    have hc := continuous_toComplex.comp (continuous_lowerReadout thickness top hm)
    exact hc.prodMk ((continuous_toComplex.comp
      ((continuous_lowerReadout thickness top hm).add continuous_fst)).neg)⟩

theorem interfaceReading_model (thickness top : ℝ) (hm : 0 < thickness)
    (lower upper : Plane) (hslope : upper.1 - lower.1 > -(1 / 6 : ℝ)) :
    interfaceReading thickness top hm (cubeFourMoments thickness top lower upper) =
      (toComplex lower, -toComplex upper) := by
  change (toComplex (lowerReadout thickness top _), -toComplex
    (lowerReadout thickness top _ + _)) = _
  rw [upperReadout_model thickness top lower upper hm hslope,
    lowerReadout_model thickness top lower upper hm hslope]

/-- `none` labels the special second layer; `some i` labels an ordinary
layer with planar shift `i`. The centers are the original horizontal centers. -/
def window {m : ℕ} (thickness : ℝ) (center : Option (Fin m) → ℝ)
    (i : Option (Fin m)) (x : Input) : ℝ :=
  layerWindow thickness (center i) x.2.1

theorem window_nonneg {m : ℕ} (thickness : ℝ)
    (center : Option (Fin m) → ℝ) (i) (x : Input) :
    0 ≤ window thickness center i x := by
  exact le_max_left _ _

theorem window_le_one {m : ℕ} (thickness : ℝ)
    (center : Option (Fin m) → ℝ) (i) (x : Input) :
    window thickness center i x ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

/-- The explicit correction on the complete four-moment input space.
Ordinary windows multiply constants, exactly as in the original prescription. -/
def correction {m : ℕ} (thickness top : ℝ) (hm : 0 < thickness)
    (center : Option (Fin m) → ℝ) (σ : ℝ) (D : C(ℂ × ℂ, ℂ)) : C(Input, ℂ) :=
  ⟨fun x => (∑ i : Fin m, (window thickness center (some i) x : ℂ) *
      (-((σ : ℂ)^2 * shift i))) +
    (window thickness center none x : ℂ) *
      scaledCorrection σ D (interfaceReading thickness top hm x), by
    apply Continuous.add
    · apply continuous_finset_sum
      intro i _
      exact (Complex.continuous_ofReal.comp ((layerWindow thickness (center (some i))).continuous.comp
        (continuous_fst.comp continuous_snd))).mul continuous_const
    · exact (Complex.continuous_ofReal.comp ((layerWindow thickness (center none)).continuous.comp
        (continuous_fst.comp continuous_snd))).mul
        ((scaledCorrection σ D).continuous.comp (interfaceReading thickness top hm).continuous)⟩

theorem correction_bound {m : ℕ} (thickness top : ℝ) (hm : 0 < thickness)
    (center : Option (Fin m) → ℝ) (σ : ℝ) (D : C(ℂ × ℂ, ℂ))
    {M : ℝ} (hD : ∀ y, ‖D y‖ ≤ M) (x : Input) :
    ‖correction thickness top hm center σ D x‖ ≤
      σ^2 * GlobalAssembly.TwoInterfaceChart.bound (m := m) M := by
  have hw (i : Option (Fin m)) : ‖(window thickness center i x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (window_nonneg thickness center i x)] using
      window_le_one thickness center i x
  have ordinary (i : Fin m) :
      ‖(window thickness center (some i) x : ℂ) * (-((σ : ℂ)^2 * shift i))‖ ≤
        σ^2 * ‖shift i‖ := by
    calc
      _ ≤ ‖-((σ : ℂ)^2 * shift i)‖ := by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hw (some i))
      _ = _ := by simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
  have special : ‖(window thickness center none x : ℂ) *
      scaledCorrection σ D (interfaceReading thickness top hm x)‖ ≤ σ^2 * M := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw none)).trans
      (scaledCorrection_bound σ D hD _)
  simp only [correction, ContinuousMap.coe_mk]
  calc
    _ ≤ (∑ i : Fin m, ‖(window thickness center (some i) x : ℂ) *
          (-((σ : ℂ)^2 * shift i))‖) +
        ‖(window thickness center none x : ℂ) *
          scaledCorrection σ D (interfaceReading thickness top hm x)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ (∑ i : Fin m, σ^2 * ‖shift i‖) + σ^2 * M :=
      add_le_add (Finset.sum_le_sum fun i _ => ordinary i) special
    _ = _ := by rw [← Finset.mul_sum]; unfold GlobalAssembly.TwoInterfaceChart.bound; ring

/-- Singleton window values give exactly the appropriate layer prescription. -/
theorem correction_on_layer {m : ℕ} (thickness top : ℝ) (hm : 0 < thickness)
    (center : Option (Fin m) → ℝ) (σ : ℝ) (D : C(ℂ × ℂ, ℂ))
    (j : Option (Fin m)) (x : Input)
    (hw : ∀ i, window thickness center i x = if i = j then 1 else 0) :
    correction thickness top hm center σ D x =
      match j with
      | none => scaledCorrection σ D (interfaceReading thickness top hm x)
      | some i => -((σ : ℂ)^2 * shift i) := by
  classical
  cases j <;> simp [correction, hw, apply_ite]

/-- The existing cutoff lemmas supply the singleton condition directly from
the prescribed `m/8` and `m/4` neighborhoods in moment space. -/
theorem windows_on_layer {m : ℕ} (thickness : ℝ) (hm : 0 < thickness)
    (center : Option (Fin m) → ℝ) (j : Option (Fin m)) (x : Input)
    (hnear : |x.2.1 - center j| ≤ thickness / 8)
    (hfar : ∀ i, i ≠ j → thickness / 4 ≤ |x.2.1 - center i|) :
    ∀ i, window thickness center i x = if i = j then 1 else 0 := by
  intro i
  split_ifs with hij
  · subst i; exact layerWindow_eq_one thickness (center j) _ hm hnear
  · exact layerWindow_eq_zero thickness (center i) _ hm (hfar i hij)

/-- Exact special-layer value, including the two signs in the planar input. -/
theorem correction_special_model {m : ℕ} (thickness top : ℝ) (hm : 0 < thickness)
    (center : Option (Fin m) → ℝ) (σ : ℝ) (D : C(ℂ × ℂ, ℂ))
    (lower upper : Plane) (hslope : upper.1 - lower.1 > -(1 / 6 : ℝ))
    (hw : ∀ i, window thickness center i (cubeFourMoments thickness top lower upper) =
      if i = none then 1 else 0) :
    correction thickness top hm center σ D (cubeFourMoments thickness top lower upper) =
      scaledCorrection σ D (toComplex lower, -toComplex upper) := by
  rw [correction_on_layer thickness top hm center σ D none _ hw,
    interfaceReading_model thickness top hm lower upper hslope]

/-- Once the ordered layers give singleton windows and the distinguished
reading, the explicit four-moment correction satisfies the existing scaled
planar exclusion. This is a consequence of `scaled_planar_avoid`, not an
extra exclusion hypothesis on the new correction. -/
theorem rejects_ordered {m : ℕ} [NeZero m]
    (thickness top : ℝ) (hm : 0 < thickness) (center : Option (Fin m) → ℝ)
    (h : ℂ ≃ₜ ℂ)
    (hh : ∀ t : ℝ, 0 < t → ∀ z, h ((t : ℂ) * z) = (t : ℂ) * h z)
    (D : C(ℂ × ℂ, ℂ))
    (avoid : ∀ (w : Fin m → ℂ) (w₂ q : ℂ), (∑ i, w i) + w₂ = 0 →
      (∀ i, squareTest h (w i) - shift i = q) →
      squareTest h w₂ + D (w 0, (∑ i, w i) - w 0) ≠ q)
    {σ : ℝ} (hσ : 0 < σ) (b : Option (Fin m) → Input)
    (hw : ∀ j i, window thickness center i (b j) = if i = j then 1 else 0)
    (balanced : (∑ i : Fin m, horizontal (b (some i))) + horizontal (b none) = 0)
    (read : interfaceReading thickness top hm (b none) =
      (horizontal (b (some 0)),
        (∑ i : Fin m, horizontal (b (some i))) - horizontal (b (some 0)))) :
    ∃ i j, squareTest h (horizontal (b i)) + correction thickness top hm center σ D (b i) ≠
      squareTest h (horizontal (b j)) + correction thickness top hm center σ D (b j) := by
  classical
  have ordinary (i : Fin m) :=
    correction_on_layer thickness top hm center σ D (some i) (b (some i)) (hw (some i))
  have special := correction_on_layer thickness top hm center σ D none (b none) (hw none)
  rw [read] at special
  by_contra! fair
  let q := squareTest h (horizontal (b none)) + correction thickness top hm center σ D (b none)
  have hf (i : Fin m) : squareTest h (horizontal (b (some i))) -
      (σ : ℂ)^2 * shift i = q := by
    have hi := fair (some i) none
    rw [ordinary i] at hi
    exact hi
  have hn := scaled_planar_avoid h hh D avoid hσ
    (fun i => horizontal (b (some i))) (horizontal (b none)) q balanced hf
  exact hn (by dsimp [q]; rw [special])

/-- Formula (5) provides the special reading needed in `rejects_ordered`.
The first ordered layer has horizontal moment `lower = p₁`; balancing then
identifies `-upper` with the sum of the other ordinary moments. -/
theorem ordered_model_reading {m : ℕ} [NeZero m]
    (thickness top : ℝ) (hm : 0 < thickness) (b : Option (Fin m) → Input)
    (lower upper : Plane) (hslope : upper.1 - lower.1 > -(1 / 6 : ℝ))
    (special : b none = cubeFourMoments thickness top lower upper)
    (first : horizontal (b (some 0)) = toComplex lower)
    (balanced : (∑ i : Fin m, horizontal (b (some i))) + horizontal (b none) = 0) :
    interfaceReading thickness top hm (b none) =
      (horizontal (b (some 0)),
        (∑ i : Fin m, horizontal (b (some i))) - horizontal (b (some 0))) := by
  rw [special, interfaceReading_model thickness top hm lower upper hslope, first]
  refine Prod.ext rfl ?_
  have hb : (∑ i : Fin m, horizontal (b (some i))) +
      (toComplex upper - toComplex lower) = 0 := by
    simpa only [special, horizontal, ContinuousMap.coe_mk, cubeFourMoments,
      toComplex_sub] using balanced
  change -toComplex upper = (∑ i : Fin m, horizontal (b (some i))) - toComplex lower
  linear_combination -hb

/-- The actual horizontal index, starting at zero, for the second-layer
exception convention. In particular `some 0` is the first layer. -/
def layerNumber {m : ℕ} : Option (Fin m) → ℕ
  | none => 1
  | some i => if i.val = 0 then 0 else i.val + 1

/-- Original centers `c_i = -1 + i m - m/2`, with one-based `i`. -/
def cubeCenter {m : ℕ} (thickness : ℝ) (i : Option (Fin m)) : ℝ :=
  -1 + ((layerNumber i + 1 : ℕ) : ℝ) * thickness - thickness / 2

theorem layerNumber_injective {m : ℕ} : Function.Injective (@layerNumber m) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => simp only [layerNumber] at hij; (split_ifs at hij; omega)
  | some i =>
    cases j with
    | none => simp only [layerNumber] at hij; (split_ifs at hij; omega)
    | some j =>
      simp only [layerNumber] at hij
      have hv : i.val = j.val := by split_ifs at hij <;> omega
      exact congrArg some (Fin.ext hv)

theorem cubeCenter_separated {m : ℕ} (thickness : ℝ) (hm : 0 < thickness)
    {i j : Option (Fin m)} (hij : i ≠ j) :
    thickness ≤ |cubeCenter thickness i - cubeCenter thickness j| := by
  have hn : layerNumber i ≠ layerNumber j := fun he => hij (layerNumber_injective he)
  rcases lt_or_gt_of_ne hn with hn | hn
  · have hn' : (layerNumber i : ℝ) + 1 ≤ (layerNumber j : ℝ) := by exact_mod_cast hn
    have hp := mul_le_mul_of_nonneg_right hn' hm.le
    have ha := neg_le_abs (cubeCenter thickness i - cubeCenter thickness j)
    simp only [cubeCenter, Nat.cast_add, Nat.cast_one] at ha ⊢
    nlinarith
  · have hn' : (layerNumber j : ℝ) + 1 ≤ (layerNumber i : ℝ) := by exact_mod_cast hn
    have hp := mul_le_mul_of_nonneg_right hn' hm.le
    have ha := le_abs_self (cubeCenter thickness i - cubeCenter thickness j)
    simp only [cubeCenter, Nat.cast_add, Nat.cast_one] at ha ⊢
    nlinarith

/-- For the original centers, being in the `m/8` core already forces every
other window to vanish; no separate window-vanishing assumption is needed. -/
theorem cube_windows_on_layer {m : ℕ} (thickness : ℝ) (hm : 0 < thickness)
    (j : Option (Fin m)) (x : Input)
    (hnear : |x.2.1 - cubeCenter thickness j| ≤ thickness / 8) :
    ∀ i, window thickness (cubeCenter thickness) i x = if i = j then 1 else 0 := by
  intro i
  split_ifs with hij
  · subst i; exact layerWindow_eq_one thickness _ _ hm hnear
  · exact layerWindows_disjoint thickness hm
      (cubeCenter_separated thickness hm (Ne.symm hij))
      (by rw [layerWindow_eq_one thickness _ _ hm hnear]; norm_num)

/-- The §4 correction, with the special top fixed at `t₂ = -1 + 2m`. -/
def cubeCorrection {m : ℕ} (thickness : ℝ) (hm : 0 < thickness)
    (σ : ℝ) (D : C(ℂ × ℂ, ℂ)) : C(Input, ℂ) :=
  correction thickness (-1 + 2 * thickness) hm (cubeCenter (m := m) thickness) σ D

theorem cubeCorrection_bound {m : ℕ} (thickness : ℝ) (hm : 0 < thickness)
    (σ : ℝ) (D : C(ℂ × ℂ, ℂ)) {M : ℝ} (hD : ∀ y, ‖D y‖ ≤ M) (x : Input) :
    ‖cubeCorrection (m := m) thickness hm σ D x‖ ≤
      σ^2 * GlobalAssembly.TwoInterfaceChart.bound (m := m) M :=
  correction_bound thickness _ hm _ σ D hD x

theorem cubeCorrection_on_layer {m : ℕ} (thickness : ℝ) (hm : 0 < thickness)
    (σ : ℝ) (D : C(ℂ × ℂ, ℂ)) (j : Option (Fin m)) (x : Input)
    (hnear : |x.2.1 - cubeCenter thickness j| ≤ thickness / 8) :
    cubeCorrection (m := m) thickness hm σ D x =
      match j with
      | none => scaledCorrection σ D (interfaceReading thickness (-1 + 2 * thickness) hm x)
      | some i => -((σ : ℂ)^2 * shift i) := by
  cases j with
  | none =>
    exact correction_on_layer thickness (-1 + 2 * thickness) hm (cubeCenter thickness) σ D none x
      (cube_windows_on_layer thickness hm none x hnear)
  | some i =>
    exact correction_on_layer thickness (-1 + 2 * thickness) hm (cubeCenter thickness) σ D (some i) x
      (cube_windows_on_layer thickness hm (some i) x hnear)

/-- Complete ordered-layer application using the original cube centers and
formula (5). All new correction values and interface readings are proved
from moments; the only avoidance premise is the pre-existing planar lemma. -/
theorem cube_rejects_ordered_model {m : ℕ} [NeZero m]
    (thickness : ℝ) (hm : 0 < thickness)
    (h : ℂ ≃ₜ ℂ)
    (hh : ∀ t : ℝ, 0 < t → ∀ z, h ((t : ℂ) * z) = (t : ℂ) * h z)
    (D : C(ℂ × ℂ, ℂ))
    (avoid : ∀ (w : Fin m → ℂ) (w₂ q : ℂ), (∑ i, w i) + w₂ = 0 →
      (∀ i, squareTest h (w i) - shift i = q) →
      squareTest h w₂ + D (w 0, (∑ i, w i) - w 0) ≠ q)
    {σ : ℝ} (hσ : 0 < σ) (b : Option (Fin m) → Input)
    (hnear : ∀ j, |(b j).2.1 - cubeCenter thickness j| ≤ thickness / 8)
    (lower upper : Plane) (hslope : upper.1 - lower.1 > -(1 / 6 : ℝ))
    (special : b none = cubeFourMoments thickness (-1 + 2 * thickness) lower upper)
    (first : horizontal (b (some 0)) = toComplex lower)
    (balanced : (∑ i : Fin m, horizontal (b (some i))) + horizontal (b none) = 0) :
    ∃ i j, squareTest h (horizontal (b i)) + cubeCorrection (m := m) thickness hm σ D (b i) ≠
      squareTest h (horizontal (b j)) + cubeCorrection (m := m) thickness hm σ D (b j) := by
  exact rejects_ordered thickness _ hm (cubeCenter thickness) h hh D avoid hσ b
    (fun j => cube_windows_on_layer thickness hm j (b j) (hnear j)) balanced
    (ordered_model_reading thickness _ hm b lower upper hslope special first balanced)

end NRR.CubeMomentCorrection
