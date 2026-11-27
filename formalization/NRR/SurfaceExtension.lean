import NRR.Surface
import NRR.SurfaceExtensionWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Set Topology Filter
open scoped Classical unitInterval
noncomputable section

namespace NRR.Surface

variable {m : ℕ} [NeZero m] {b : Fin m → ℝ}

/-- Rotate the roots so that a horizontal line through a branch point
projects to a vertical ray in the base, avoiding all other branch points. -/
def rotatedRoot (i : Fin m) : C(locus (fun j => (b j : ℂ)), ℂ) :=
  ⟨fun z => (1 - Complex.I) * z.val i,
    continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)⟩

theorem rotatedRoot_sq_sub (z : locus (fun j => (b j : ℂ))) (i j : Fin m) :
    rotatedRoot j z ^ 2 - rotatedRoot i z ^ 2 = -2 * Complex.I * ((b j : ℂ) - b i) := by
  have h : z.val j ^ 2 - z.val i ^ 2 = (b j : ℂ) - b i := by
    linear_combination z.property j - z.property i
  change ((1 - Complex.I) * z.val j) ^ 2 - ((1 - Complex.I) * z.val i) ^ 2 = _
  rw [mul_pow, mul_pow, ← mul_sub, h]
  congr 1
  linear_combination Complex.I_sq

/-- Within a narrow strip in the i-th root plane all other horizontal
coordinates have a definite, nonzero sign. This holds along the whole strip,
including its two unbounded arms. -/
theorem rotatedRoot_re_ne_zero (z : locus (fun j => (b j : ℂ))) (i j : Fin m) {δ : ℝ}
    (hgap : δ ^ 2 < |b j - b i|) (hstrip : |(rotatedRoot i z).im| ≤ δ) :
    (rotatedRoot j z).re ≠ 0 := by
  intro hz
  have h := rotatedRoot_sq_sub z i j
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hz] at hr hi
  norm_num at hr hi
  let x := (rotatedRoot i z).re
  let y := (rotatedRoot i z).im
  have hxy : x ^ 2 ≤ y ^ 2 := by dsimp [x,y]; nlinarith [sq_nonneg (rotatedRoot j z).im]
  have hprod : x * y = b j - b i := by dsimp [x,y]; nlinarith
  have hax : |x| ≤ |y| := by
    nlinarith [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  have hab : |b j - b i| ≤ δ ^ 2 := calc
    |b j - b i| = |x| * |y| := by rw [← hprod, abs_mul]
    _ ≤ δ * δ := mul_le_mul (hax.trans hstrip) hstrip (abs_nonneg _) ((abs_nonneg _).trans hstrip)
    _ = _ := (sq δ).symm
  exact hgap.not_ge hab

/-- A complete positive turn across the strip, measured in turns. -/
def stripHeight (δ y : ℝ) : ℝ := min 1 (max 0 ((y + δ) / (2 * δ)))

theorem stripHeight_lo {δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ -δ) : stripHeight δ y = 0 := by
  have h : (y + δ) / (2 * δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [stripHeight, max_eq_left h]

theorem stripHeight_hi {δ y : ℝ} (hδ : 0 < δ) (hy : δ ≤ y) : stripHeight δ y = 1 := by
  have h : 1 ≤ (y + δ) / (2 * δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  exact min_eq_left (h.trans (le_max_right _ _))

def stripPhase (δ y : ℝ) : Circle := Circle.exp (2 * Real.pi * stripHeight δ y)

theorem stripPhase_eq_one {δ y : ℝ} (hδ : 0 < δ) (hy : δ ≤ |y|) :
    stripPhase δ y = 1 := by
  rcases le_abs.mp hy with hp | hn
  · simp [stripPhase, stripHeight_hi hδ hp]
  · simp [stripPhase, stripHeight_lo hδ (by linarith)]

/-- The sign pattern naming one lift of the ray. The i-th root is free. -/
def stripSigns (i : Fin m) (s : Finset (Fin m)) (z : locus (fun j => (b j : ℂ))) : Prop :=
  ∀ j, j ≠ i → (0 < (rotatedRoot j z).re ↔ j ∈ s)

private theorem eventually_stripSigns (i : Fin m) (s : Finset (Fin m))
    (z : locus (fun j => (b j : ℂ)))
    (hn : ∀ j, j ≠ i → (rotatedRoot j z).re ≠ 0) :
    ∀ᶠ w in 𝓝 z, stripSigns i s w ↔ stripSigns i s z := by
  have each (j : Fin m) : ∀ᶠ w in 𝓝 z,
      j ≠ i → (0 < (rotatedRoot j w).re ↔ 0 < (rotatedRoot j z).re) := by
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ h => (h hji).elim
    have hc := (Complex.continuous_re.comp (rotatedRoot (b := b) j).continuous).continuousAt (x := z)
    rcases lt_or_gt_of_ne (hn j hji) with h | h
    · filter_upwards [hc.eventually_lt continuousAt_const h] with w hw
      change ((rotatedRoot j) w).re < 0 at hw
      simp [not_lt.mpr hw.le, not_lt.mpr h.le]
    · filter_upwards [continuousAt_const.eventually_lt hc h] with w hw
      change 0 < ((rotatedRoot j) w).re at hw
      simp [hw, h]
  filter_upwards [eventually_all.mpr each] with w hw
  exact forall_congr' fun j => forall_congr' fun hji => iff_congr (hw j hji) Iff.rfl

/-- A global circle-valued map supported on a single lifted strip. It makes
one positive turn when the selected strip is crossed from bottom to top. -/
def stripUnit (i : Fin m) (s : Finset (Fin m)) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ j, j ≠ i → δ ^ 2 < |b j - b i|) :
    C(locus (fun j => (b j : ℂ)), Circle) := by
  classical
  let y (z : locus (fun j => (b j : ℂ))) := (rotatedRoot i z).im
  have cy : Continuous y := Complex.continuous_im.comp (rotatedRoot i).continuous
  refine ⟨fun z => if stripSigns i s z then stripPhase δ (y z) else 1, ?_⟩
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hy : |y z| ≤ δ
  · have signs := eventually_stripSigns i s z (fun j hj => rotatedRoot_re_ne_zero z i j (hgap j hj) hy)
    by_cases hs : stripSigns i s z
    · have cphase : Continuous fun w => stripPhase δ (y w) := by
        unfold stripPhase stripHeight
        exact Circle.exp.continuous.comp (by fun_prop)
      apply cphase.continuousAt.congr_of_eventuallyEq
      filter_upwards [signs] with w hw
      simp [hw.mpr hs]
    · apply continuousAt_const (y := (1 : Circle)) |>.congr_of_eventuallyEq
      filter_upwards [signs] with w hw
      simp [show ¬ stripSigns i s w from fun hh => hs (hw.mp hh)]
  · have ht : δ < |y z| := lt_of_not_ge hy
    apply continuousAt_const (y := (1 : Circle)) |>.congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt cy.abs.continuousAt ht] with w hw
    simp [stripPhase_eq_one hδ hw.le]

theorem stripUnit_apply (i : Fin m) (s : Finset (Fin m)) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ j, j ≠ i → δ ^ 2 < |b j - b i|) (z : locus (fun j => (b j : ℂ))) :
    stripUnit i s δ hδ hgap z =
      if stripSigns i s z then stripPhase δ (rotatedRoot i z).im else 1 := by
  classical
  rfl

/-- On a positively oriented boundary split just below and above the strip,
the two arcs contribute respectively +1 and −1 if they traverse this chosen
sheet. The sign predicates are only needed inside the strip. -/
theorem phaseChange_stripUnit (i : Fin m) (s : Finset (Fin m)) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ j, j ≠ i → δ ^ 2 < |b j - b i|)
    (γ : C(I, locus (fun j => (b j : ℂ)))) (c : I) (pos neg : Bool)
    (hlo : (rotatedRoot i (γ 0)).im ≤ -δ) (hhi : δ ≤ (rotatedRoot i (γ c)).im)
    (hend : (rotatedRoot i (γ 1)).im ≤ -δ)
    (hpos : ∀ t ≤ c, |(rotatedRoot i (γ t)).im| ≤ δ → (stripSigns i s (γ t) ↔ pos = true))
    (hneg : ∀ t ≥ c, |(rotatedRoot i (γ t)).im| ≤ δ → (stripSigns i s (γ t) ↔ neg = true)) :
    phaseChange ((stripUnit i s δ hδ hgap).comp γ) =
      (if pos then 1 else 0) - (if neg then 1 else 0) := by
  let y (t : I) := (rotatedRoot i (γ t)).im
  have cy : Continuous y := Complex.continuous_im.comp ((rotatedRoot i).continuous.comp γ.continuous)
  let arg (v : Bool) : C(I, ℝ) :=
    ⟨fun t => if v then 2 * Real.pi * stripHeight δ (y t) else 0, by
      cases v
      · exact continuous_const
      · change Continuous fun t => 2 * Real.pi * min 1 (max 0 ((y t + δ) / (2 * δ)))
        fun_prop⟩
  let U := stripUnit i s δ hδ hgap
  have hl (v : Bool) (t : I) (h : |y t| ≤ δ → (stripSigns i s (γ t) ↔ v = true)) :
      Circle.exp (arg v t) = (U.comp γ) t := by
    change Circle.exp (if v then 2 * Real.pi * stripHeight δ (y t) else 0) = U (γ t)
    rw [show U (γ t) = _ from stripUnit_apply i s hδ hgap (γ t)]
    by_cases ht : |y t| ≤ δ
    · rw [h ht]
      cases v <;> simp [stripPhase, y]
    · have hone := stripPhase_eq_one hδ ((lt_of_not_ge ht).le)
      change stripPhase δ (rotatedRoot i (γ t)).im = 1 at hone
      cases v
      · simp [hone]
      · simp only [ite_true, hone, ite_self]
        exact hone
  rw [phaseChange_split _ c (arg pos) (arg neg) (fun t ht => hl _ _ (hpos t ht))
    (fun t ht => hl _ _ (hneg t ht))]
  cases pos <;> cases neg <;>
    simp [arg, y, stripHeight_lo hδ hlo, stripHeight_hi hδ hhi, stripHeight_lo hδ hend,
      Real.pi_ne_zero]

/-- Once a global unit realizes the boundary winding class, a continuous
logarithm of the boundary quotient supplies the exact prescribed values. -/
theorem extendWithUnit {X : Type} [TopologicalSpace X] [NormalSpace X]
    {B : Set X} (hB : IsClosed B) (u : C(X, Circle)) (g : C(B, ℂ))
    (l : C(B, ℂ)) (hl : ∀ x : B, (u x.val : ℂ) * Complex.exp (l x) = g x) :
    ∃ G : C(X, ℂ), (∀ x, G x ≠ 0) ∧ ∀ x : B, G x.val = g x := by
  obtain ⟨L, hL⟩ := l.exists_restrict_eq hB
  refine ⟨⟨fun x => (u x : ℂ) * Complex.exp (L x), by fun_prop⟩, ?_, ?_⟩
  · intro x
    exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)
  · intro x
    have he := DFunLike.congr_fun hL x
    change L x.val = l x at he
    simpa [he] using hl x

/-- The phase of a continuous nonvanishing complex function. -/
def phaseOf {B : Type} [TopologicalSpace B] (g : C(B, ℂ)) (hg : ∀ x, g x ≠ 0) :
    C(B, Circle) :=
  ⟨fun x => ⟨g x / (‖g x‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
      simp [Complex.norm_real, norm_ne_zero_iff.mpr (hg x)])⟩,
    (g.continuous.div
      (Complex.continuous_ofReal.comp g.continuous.norm) (fun x => by simp [hg x])).subtype_mk _⟩

def boundaryCircle {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A × Circle ≃ₜ B) (a : A) : C(Circle, B) :=
  ⟨fun u => e (a,u), e.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Match both the phase and the magnitude on all boundary circles.
Components may carry any individual degrees realized by the global unit. -/
theorem extendOfBoundaryWindings {X A : Type} [TopologicalSpace X] [NormalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] {B : Set X} (hB : IsClosed B)
    (e : A × Circle ≃ₜ B) (u : C(X, Circle)) (g : C(B, ℂ)) (hg : ∀ x, g x ≠ 0)
    (hw : ∀ a, winding ((phaseOf g hg).comp (boundaryCircle e a)) =
      winding ((u.restrict B).comp (boundaryCircle e a))) :
    ∃ G : C(X, ℂ), (∀ x, G x ≠ 0) ∧ ∀ x : B, G x.val = g x := by
  let f := phaseOf g hg
  let v := u.restrict B
  have ex (a : A) : ∃ l : C(Circle, ℝ), ∀ t, Circle.exp (l t) =
      (f.comp (boundaryCircle e a) * (v.comp (boundaryCircle e a))⁻¹) t := by
    apply (exists_argument_iff_winding_zero _).mpr
    rw [winding_mul, winding_inv]
    rw [← sub_eq_add_neg]
    exact sub_eq_zero.mpr (hw a)
  choose l hl using ex
  have ca : Continuous (fun p : A × Circle => l p.1 p.2) :=
    continuous_prod_of_discrete_left.mpr (fun a => (l a).continuous)
  let ang : C(B, ℝ) := ⟨fun x => l (e.symm x).1 (e.symm x).2, ca.comp e.symm.continuous⟩
  have hphase (x : B) : Circle.exp (ang x) = f x * (v x)⁻¹ := by
    have h := hl (e.symm x).1 (e.symm x).2
    simpa [ang, boundaryCircle] using h
  let logAbs : C(B, ℝ) := ⟨fun x => Real.log ‖g x‖,
    g.continuous.norm.log fun x => norm_ne_zero_iff.mpr (hg x)⟩
  let L : C(B, ℂ) := ⟨fun x => (logAbs x : ℂ) + (ang x : ℂ) * Complex.I, by fun_prop⟩
  apply extendWithUnit hB u g L
  intro x
  have hp := congrArg (fun w : Circle => (w : ℂ)) (hphase x)
  change Complex.exp ((ang x : ℂ) * Complex.I) =
    (g x / (‖g x‖ : ℂ)) * (u x.val : ℂ)⁻¹ at hp
  change (u x.val : ℂ) * Complex.exp ((Real.log ‖g x‖ : ℝ) + (ang x : ℂ) * Complex.I) = g x
  rw [Complex.exp_add, hp, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hg x))]
  field_simp [Circle.coe_ne_zero, hg x]

/-- Fill the actual interior while retaining the given exterior residual,
including its values on the common boundary. -/
theorem replaceInsideCore {X A : Type} [TopologicalSpace X] [NormalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] (core B : Set X)
    (hB : IsClosed B) (hFr : frontier core ⊆ B)
    (e : A × Circle ≃ₜ B) (u : C(X, Circle)) (old : C(X, ℂ))
    (hn : ∀ x ∉ interior core, old x ≠ 0)
    (hnB : ∀ x : B, old x ≠ 0)
    (hw : ∀ a, winding ((phaseOf (old.restrict B) hnB).comp (boundaryCircle e a)) =
      winding ((u.restrict B).comp (boundaryCircle e a))) :
    ∃ G : C(X, ℂ), (∀ x, G x ≠ 0) ∧ ∀ x ∉ interior core, G x = old x := by
  obtain ⟨F, hF, hEq⟩ := extendOfBoundaryWindings hB e u (old.restrict B) hnB hw
  let G : C(X, ℂ) := ⟨fun x => if x ∈ interior core then F x else old x,
    Continuous.if (fun x hx => hEq ⟨x, hFr (frontier_interior_subset hx)⟩) F.continuous old.continuous⟩
  refine ⟨G, fun x => ?_, fun x hx => if_neg hx⟩
  change (if x ∈ interior core then F x else old x) ≠ 0
  split_ifs with hx
  · exact hF x
  · exact hn x hx

/-- Winding profiles of globally defined units, read on an indexed family
of oriented circles. -/
def windingProfiles {A X : Type} [TopologicalSpace X] (loops : A → C(Circle, X)) :
    AddSubgroup (A → ℝ) where
  carrier q := ∃ u : C(X, Circle), ∀ a, winding (u.comp (loops a)) = q a
  zero_mem' := by
    refine ⟨1, fun a => ?_⟩
    apply (exists_argument_iff_winding_zero _).mp
    exact ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u * v, fun a => ?_⟩
    exact (winding_mul (u.comp (loops a)) (v.comp (loops a))).trans (congrArg₂ (· + ·) (hu a) (hv a))
  neg_mem' := by
    rintro x ⟨u, hu⟩
    exact ⟨u⁻¹, fun a => (winding_inv (u.comp (loops a))).trans (congrArg Neg.neg (hu a))⟩

/-- On a finite connected graph of ends, edge units with winding +1 at
their target and −1 at their source realize every integral profile of sum
zero. The returned element is a global continuous map. -/
theorem realizeBalancedProfile {A X : Type} [Fintype A] [DecidableEq A] [TopologicalSpace X]
    (loops : A → C(Circle, X)) (root : A) (edges : A → A → Prop)
    (reach : ∀ a, Relation.ReflTransGen edges root a)
    (units : ∀ a b, edges a b →
      Pi.single b (1 : ℝ) - Pi.single a 1 ∈ windingProfiles loops)
    (q : A → ℤ) (hzero : ∑ a, q a = 0) :
    ∃ u : C(X, Circle), ∀ a, winding (u.comp (loops a)) = (q a : ℝ) := by
  let P := windingProfiles loops
  have hr (a : A) : Pi.single a (1 : ℝ) - Pi.single root 1 ∈ P := by
    induction reach a with
    | refl => simp
    | @tail v w _ edge ih =>
      have hh := P.add_mem (units v w edge) ih
      simpa only [sub_add_sub_cancel] using hh
  have hs := P.sum_mem (t := Finset.univ) (fun a _ => P.zsmul_mem (hr a) (q a))
  have he : (∑ a, q a • (Pi.single a (1 : ℝ) - Pi.single root 1)) = fun a => (q a : ℝ) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hzero, zero_smul, sub_zero]
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  change (fun a => (q a : ℝ)) ∈ P
  rw [← he]
  exact hs

end NRR.Surface
