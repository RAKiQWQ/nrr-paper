import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.Order.Field.Pointwise
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! Elementary starting points for a slicing proof of Brunn--Minkowski.
The one-dimensional statements concern actual compact convex sets.
The strict Jacobian inequalities are the algebraic step in dimensions
two and three; they are not yet the full geometric inequalities. -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace NRR.BrunnMinkowskiSlices

/-- The actual Minkowski midpoint set. -/
def midpointSet (A B : Set ℝ) : Set ℝ := (1 / 2 : ℝ) • (A + B)

private theorem compact_convex_interval {A : Set ℝ}
    (hA : IsCompact A) (cA : Convex ℝ A) (nA : A.Nonempty) :
    ∃ a b : ℝ, a ≤ b ∧ A = Icc a b :=
  ⟨sInf A, sSup A, csInf_le_csSup hA.bddBelow hA.bddAbove nA,
    eq_Icc_of_connected_compact (cA.isConnected nA) hA⟩

/-- The one-dimensional Brunn--Minkowski formula is exact for all nonempty
compact convex sets, including degenerate intervals. -/
theorem volume_midpoint_real {A B : Set ℝ}
    (hA : IsCompact A) (cA : Convex ℝ A) (nA : A.Nonempty)
    (hB : IsCompact B) (cB : Convex ℝ B) (nB : B.Nonempty) :
    volume.real (midpointSet A B) = (volume.real A + volume.real B) / 2 := by
  obtain ⟨a,b,hab,rfl⟩ := compact_convex_interval hA cA nA
  obtain ⟨c,d,hcd,rfl⟩ := compact_convex_interval hB cB nB
  rw [midpointSet, Set.Icc_add_Icc hab hcd,
    LinearOrderedField.smul_Icc (by norm_num : (0 : ℝ) < 1/2),
    Real.volume_real_Icc_of_le (by linarith : (1/2 : ℝ)*(a+c) ≤ (1/2)*(b+d)),
    Real.volume_real_Icc_of_le hab, Real.volume_real_Icc_of_le hcd]
  ring

/-- Equal-volume one-dimensional compact convex sets differ by translation. -/
theorem exists_translation_real {A B : Set ℝ}
    (hA : IsCompact A) (cA : Convex ℝ A) (nA : A.Nonempty)
    (hB : IsCompact B) (cB : Convex ℝ B) (nB : B.Nonempty)
    (equal : volume.real A = volume.real B) :
    ∃ v : ℝ, B = (fun x => x + v) '' A := by
  obtain ⟨a,b,hab,rfl⟩ := compact_convex_interval hA cA nA
  obtain ⟨c,d,hcd,rfl⟩ := compact_convex_interval hB cB nB
  rw [Real.volume_real_Icc_of_le hab, Real.volume_real_Icc_of_le hcd] at equal
  refine ⟨c-a, ?_⟩
  ext z
  constructor
  · rintro ⟨hzl,hzu⟩
    exact ⟨z-(c-a), ⟨by linarith, by linarith⟩, by ring⟩
  · rintro ⟨x,⟨hxl,hxu⟩,rfl⟩
    constructor <;> linarith

/-- The section lower bound times the midpoint-transport Jacobian in
dimension two. -/
def jacobian2 (a b : ℝ) : ℝ := ((a+b)/2) * ((1+a/b)/2)

theorem jacobian2_gap (a b : ℝ) (hb : b ≠ 0) :
    jacobian2 a b - a = (a-b)^2 / (4*b) := by
  unfold jacobian2
  field_simp
  ring

theorem le_jacobian2 (a b : ℝ) (hb : 0 < b) : a ≤ jacobian2 a b := by
  have h := div_nonneg (sq_nonneg (a-b)) (show 0 ≤ 4*b by positivity)
  rw [← jacobian2_gap a b hb.ne'] at h
  linarith

theorem jacobian2_eq_iff (a b : ℝ) (hb : 0 < b) :
    jacobian2 a b = a ↔ a = b := by
  constructor
  · intro h
    have hz : (a-b)^2/(4*b) = 0 := by rw [← jacobian2_gap a b hb.ne',h,sub_self]
    have hs : (a-b)^2 = 0 := (div_eq_zero_iff).mp hz |>.resolve_right (by positivity)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    subst a
    have gap := jacobian2_gap b b hb.ne'
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] at gap
    linarith

/-- The two-dimensional section Brunn--Minkowski bound, multiplied by the
one-dimensional midpoint-transport Jacobian for a three-dimensional body. -/
def jacobian3 (a b : ℝ) : ℝ :=
  ((Real.sqrt a + Real.sqrt b)/2)^2 * ((1+a/b)/2)

private theorem square_jacobian_gap (x y : ℝ) (hy : y ≠ 0) :
    ((x+y)/2)^2 * ((1+x^2/y^2)/2) - x^2 =
      (x-y)^2 * (x^2+4*x*y+y^2) / (8*y^2) := by
  field_simp
  ring

theorem jacobian3_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    jacobian3 a b - a =
      (Real.sqrt a-Real.sqrt b)^2 *
        (a+4*Real.sqrt a*Real.sqrt b+b) / (8*b) := by
  simpa only [Real.sq_sqrt ha, Real.sq_sqrt hb.le, jacobian3] using
    square_jacobian_gap (Real.sqrt a) (Real.sqrt b) (Real.sqrt_pos.mpr hb).ne'

theorem le_jacobian3 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a ≤ jacobian3 a b := by
  have hn : 0 ≤ (Real.sqrt a-Real.sqrt b)^2 *
      (a+4*Real.sqrt a*Real.sqrt b+b) / (8*b) := by positivity
  rw [← jacobian3_gap a b ha hb] at hn
  linarith

/-- Equality in the Jacobian step forces equal section masses. This is the
strictness needed to make the monotone section transport a translation. -/
theorem jacobian3_eq_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    jacobian3 a b = a ↔ a = b := by
  constructor
  · intro h
    have hz : (Real.sqrt a-Real.sqrt b)^2 *
        (a+4*Real.sqrt a*Real.sqrt b+b) / (8*b) = 0 := by
      rw [← jacobian3_gap a b ha hb,h,sub_self]
    have hp : 0 < a+4*Real.sqrt a*Real.sqrt b+b := by positivity
    have hn : (Real.sqrt a-Real.sqrt b)^2 *
        (a+4*Real.sqrt a*Real.sqrt b+b) = 0 :=
      (div_eq_zero_iff).mp hz |>.resolve_right (by positivity)
    have hs := (mul_eq_zero.mp hn).resolve_right hp.ne'
    have he := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le]
  · intro h
    subst a
    have gap := jacobian3_gap b b hb.le hb
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div] at gap
    linarith


/-- Midpoint of a point and its one-dimensional monotone mass transport. -/
def transportMidpoint (T : ℝ → ℝ) (x : ℝ) : ℝ := (x + T x) / 2

def transportJacobian (a b T : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + a x / b (T x)) / 2

private theorem le_transport_density3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (lower : ((Real.sqrt a + Real.sqrt b)/2)^2 ≤ c) :
    a ≤ ((1+a/b)/2) * c := by
  calc
    a ≤ jacobian3 a b := le_jacobian3 a b ha hb
    _ ≤ _ := by
      unfold jacobian3
      nlinarith [mul_le_mul_of_nonneg_right lower
        (show 0 ≤ (1+a/b)/2 by positivity)]

private theorem transport_density3_eq (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (lower : ((Real.sqrt a + Real.sqrt b)/2)^2 ≤ c)
    (equal : ((1+a/b)/2)*c = a) : a = b := by
  apply (jacobian3_eq_iff a b ha hb).mp
  apply le_antisymm _ (le_jacobian3 a b ha hb)
  calc
    _ ≤ ((1+a/b)/2)*c := by
      unfold jacobian3
      nlinarith [mul_le_mul_of_nonneg_right lower
        (show 0 ≤ (1+a/b)/2 by positivity)]
    _ = a := equal

theorem hasDerivWithinAt_transportMidpoint {S : Set ℝ} (a b T : ℝ → ℝ)
    {x : ℝ} (derivative : HasDerivWithinAt T (a x / b (T x)) S x) :
    HasDerivWithinAt (transportMidpoint T) (transportJacobian a b T x) S x := by
  simpa only [transportMidpoint,transportJacobian] using
    ((hasDerivWithinAt_id x S).add derivative).div_const 2

theorem monotoneOn_transportMidpoint {S : Set ℝ} (T : ℝ → ℝ)
    (mono : MonotoneOn T S) : MonotoneOn (transportMidpoint T) S := by
  intro x hx y hy hxy
  dsimp [transportMidpoint]
  linarith [mono hx hy hxy]

/-- The genuine one-dimensional change-of-variables step in a
three-dimensional slicing proof. The lower bound is the lower-dimensional
section inequality, and the prescribed derivative is the normalized
cumulative-mass transport identity. No full-body Brunn--Minkowski statement
is assumed here. -/
theorem mass_le_integral_midpoint_transport {S : Set ℝ} (measurable : MeasurableSet S)
    (a b c T : ℝ → ℝ) (mono : MonotoneOn T S)
    (derivative : ∀ x ∈ S, HasDerivWithinAt T (a x / b (T x)) S x)
    (nonneg : ∀ x ∈ S, 0 ≤ a x) (positive : ∀ x ∈ S, 0 < b (T x))
    (lower : ∀ x ∈ S, ((Real.sqrt (a x) + Real.sqrt (b (T x)))/2)^2 ≤
      c (transportMidpoint T x))
    (integrableA : IntegrableOn a S)
    (integrableC : IntegrableOn c (transportMidpoint T '' S)) :
    (∫ x in S, a x) ≤ ∫ z in transportMidpoint T '' S, c z := by
  have hz := fun x hx => hasDerivWithinAt_transportMidpoint a b T (derivative x hx)
  have hm := monotoneOn_transportMidpoint T mono
  have hint : IntegrableOn
      (fun x => transportJacobian a b T x * c (transportMidpoint T x)) S := by
    simpa only [smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurable hz hm c).mp integrableC
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn measurable hz hm c]
  apply setIntegral_mono_on integrableA (by simpa only [smul_eq_mul] using hint) measurable
  intro x hx
  exact le_transport_density3 _ _ _ (nonneg x hx) (positive x hx) (lower x hx)

/-- Equality of the whole one-dimensional integrals forces equal transported
section masses almost everywhere, using the strict Jacobian inequality. -/
theorem ae_section_masses_eq_of_midpoint_integral_eq {S : Set ℝ}
    (measurable : MeasurableSet S) (a b c T : ℝ → ℝ) (mono : MonotoneOn T S)
    (derivative : ∀ x ∈ S, HasDerivWithinAt T (a x / b (T x)) S x)
    (nonneg : ∀ x ∈ S, 0 ≤ a x) (positive : ∀ x ∈ S, 0 < b (T x))
    (lower : ∀ x ∈ S, ((Real.sqrt (a x) + Real.sqrt (b (T x)))/2)^2 ≤
      c (transportMidpoint T x))
    (integrableA : IntegrableOn a S)
    (integrableC : IntegrableOn c (transportMidpoint T '' S))
    (equal : (∫ z in transportMidpoint T '' S, c z) = ∫ x in S, a x) :
    ∀ᵐ x ∂volume.restrict S, a x = b (T x) := by
  let w (x : ℝ) := transportJacobian a b T x * c (transportMidpoint T x)
  have hz := fun x hx => hasDerivWithinAt_transportMidpoint a b T (derivative x hx)
  have hm := monotoneOn_transportMidpoint T mono
  have hint : IntegrableOn w S := by
    simpa only [w,smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurable hz hm c).mp integrableC
  have integralW : (∫ x in S, w x) = ∫ x in S, a x := by
    rw [← equal, integral_image_eq_integral_deriv_smul_of_monotoneOn measurable hz hm c]
    rfl
  have diffInt : IntegrableOn (fun x => w x-a x) S := hint.sub integrableA
  have diffNonneg : ∀ᵐ x ∂volume.restrict S, 0 ≤ w x-a x := by
    filter_upwards [ae_restrict_mem measurable] with x hx
    exact sub_nonneg.mpr
      (le_transport_density3 _ _ _ (nonneg x hx) (positive x hx) (lower x hx))
  have diffZero : (∫ x in S, w x-a x) = 0 := by
    rw [integral_sub hint integrableA, integralW, sub_self]
  have vanishes := (integral_eq_zero_iff_of_nonneg_ae diffNonneg diffInt).mp diffZero
  filter_upwards [ae_restrict_mem measurable,vanishes] with x hx he
  exact transport_density3_eq _ _ _ (nonneg x hx) (positive x hx)
    (lower x hx) (sub_eq_zero.mp he)

end NRR.BrunnMinkowskiSlices
