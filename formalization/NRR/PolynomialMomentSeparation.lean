import NRR.RationalMomentApproximation
import NRR.ConvexLimits
import NRR.CubeVolumeMoments
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Ordinary polynomial volume moments separate full-dimensional compact
convex sets. The proof first identifies their actual restricted Borel
measures, using rational Stone--Weierstrass on the union of their supports. -/

noncomputable section
open Set Topology Metric MeasureTheory TopologicalSpace

namespace NRR.PolynomialMomentSeparation

/-- A rational polynomial in the ordinary Euclidean coordinates. -/
def polynomialEvaluation {d : ℕ} (p : MvPolynomial (Fin d) ℚ) : C(Space d, ℝ) :=
  ⟨fun x => RationalMomentApproximation.eval p (fun i => x i),
    (RationalMomentApproximation.continuous_eval p).comp
      (continuous_pi fun i => (EuclideanSpace.proj i).continuous)⟩

/-- The ordinary, unnormalized polynomial volume moment. -/
def polynomialMoment {d : ℕ} (p : MvPolynomial (Fin d) ℚ) (A : Set (Space d)) : ℝ :=
  ∫ x in A, polynomialEvaluation p x ∂volume

/-- Equality of all rational polynomial moments identifies the actual
restricted volume measures of any two compact sets. Convexity and
full-dimensionality are needed only for recovering the sets themselves. -/
theorem restrict_volume_eq_of_polynomialMoments {d : ℕ} {A B : Set (Space d)}
    (hA : IsCompact A) (hB : IsCompact B)
    (moments : ∀ p : MvPolynomial (Fin d) ℚ,
      polynomialMoment p A = polynomialMoment p B) :
    volume.restrict A = volume.restrict B := by
  letI : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hA.measure_lt_top.ne
  letI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  apply eq_of_forall_dist_le
  intro ε hε
  let K := A ∪ B
  have hK : IsCompact K := hA.union hB
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let coordinates : Fin d → C(K, ℝ) := fun i =>
    ⟨fun x => x.val i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩
  have separate : ∀ x y : K, x ≠ y → ∃ i, coordinates i x ≠ coordinates i y := by
    intro x y hxy
    by_contra! he
    exact hxy (Subtype.ext (PiLp.ext he))
  let δ : ℝ := ε / (volume.real A + volume.real B + 1)
  have hden : 0 < volume.real A + volume.real B + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let fK : C(K, ℝ) := ⟨fun x => f x.val, f.continuous.comp continuous_subtype_val⟩
  obtain ⟨p, hp⟩ := RationalMomentApproximation.exists_rational_polynomial_near_coordinates
    coordinates separate fK hδ
  have error (x : Space d) (hx : x ∈ K) :
      |f x - polynomialEvaluation p x| ≤ δ := by
    simpa only [polynomialEvaluation, ContinuousMap.coe_mk, coordinates, fK,
      abs_sub_comm] using (hp ⟨x, hx⟩).le
  have intA : IntegrableOn (fun x => f x) A volume :=
    f.continuous.continuousOn.integrableOn_compact hA
  have intB : IntegrableOn (fun x => f x) B volume :=
    f.continuous.continuousOn.integrableOn_compact hB
  have polyA : IntegrableOn (polynomialEvaluation p) A volume :=
    (polynomialEvaluation p).continuous.continuousOn.integrableOn_compact hA
  have polyB : IntegrableOn (polynomialEvaluation p) B volume :=
    (polynomialEvaluation p).continuous.continuousOn.integrableOn_compact hB
  have eA : dist (∫ x in A, f x ∂volume) (polynomialMoment p A) ≤ δ * volume.real A := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
      (f := fun x : Space d => f x - polynomialEvaluation p x) hA.measure_lt_top
      (fun x hx => show ‖f x - polynomialEvaluation p x‖ ≤ δ from
        by simpa only [Real.norm_eq_abs] using error x (Or.inl hx))
    rw [integral_sub intA polyA] at hb
    exact hb
  have eB : dist (polynomialMoment p B) (∫ x in B, f x ∂volume) ≤ δ * volume.real B := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := B)
      (f := fun x : Space d => f x - polynomialEvaluation p x) hB.measure_lt_top
      (fun x hx => show ‖f x - polynomialEvaluation p x‖ ≤ δ from
        by simpa only [Real.norm_eq_abs] using error x (Or.inr hx))
    rw [integral_sub intB polyB] at hb
    rw [Real.dist_eq, polynomialMoment]
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hb
  have he : δ * (volume.real A + volume.real B + 1) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ hden.ne'
  change dist (∫ x in A, f x ∂volume) (∫ x in B, f x ∂volume) ≤ ε
  calc
    _ ≤ dist (∫ x in A, f x ∂volume) (polynomialMoment p A) +
        dist (polynomialMoment p A) (∫ x in B, f x ∂volume) := dist_triangle _ _ _
    _ = dist (∫ x in A, f x ∂volume) (polynomialMoment p A) +
        dist (polynomialMoment p B) (∫ x in B, f x ∂volume) := by rw [moments p]
    _ ≤ δ * volume.real A + δ * volume.real B := add_le_add eA eB
    _ ≤ ε := by nlinarith

/-- A closed convex set with nonempty interior is determined by the
restriction of ordinary volume to it. -/
theorem convex_eq_of_restrict_volume_eq {d : ℕ} {A B : Set (Space d)}
    (closedA : IsClosed A) (closedB : IsClosed B)
    (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (interiorA : (interior A).Nonempty) (interiorB : (interior B).Nonempty)
    (equal : volume.restrict A = volume.restrict B) : A = B := by
  have subset_of_equal {C D : Set (Space d)} (closedC : IsClosed C) (closedD : IsClosed D)
      (convexC : Convex ℝ C) (interiorC : (interior C).Nonempty)
      (he : volume.restrict C = volume.restrict D) : C ⊆ D := by
    have hz : volume (C \ D) = 0 := by
      have h := congrArg (fun μ : Measure (Space d) => μ (C \ D)) he
      dsimp only at h
      rw [Measure.restrict_apply (closedC.measurableSet.diff closedD.measurableSet),
        Measure.restrict_apply (closedC.measurableSet.diff closedD.measurableSet),
        inter_eq_self_of_subset_left diff_subset, diff_inter_self, measure_empty] at h
      exact h
    have emptyDiff : interior C \ D = ∅ :=
      (isOpen_interior.sdiff closedD).eq_empty_of_measure_zero
        (measure_mono_null (diff_subset_diff_left interior_subset) hz)
    have inside : interior C ⊆ D := diff_eq_empty.mp emptyDiff
    rw [← closedC.closure_eq,
      ← convexC.closure_interior_eq_closure_of_nonempty_interior interiorC]
    exact closure_minimal inside closedD
  exact (subset_of_equal closedA closedB convexA interiorA equal).antisymm
    (subset_of_equal closedB closedA convexB interiorB equal.symm)

/-- Rational ordinary polynomial moments separate every pair of actual
full-dimensional compact convex sets, without prescribing their volume. -/
theorem convex_eq_of_polynomialMoments {d : ℕ} {A B : Set (Space d)}
    (hA : IsCompact A) (hB : IsCompact B) (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (interiorA : (interior A).Nonempty) (interiorB : (interior B).Nonempty)
    (moments : ∀ p : MvPolynomial (Fin d) ℚ,
      polynomialMoment p A = polynomialMoment p B) : A = B :=
  convex_eq_of_restrict_volume_eq hA.isClosed hB.isClosed convexA convexB interiorA interiorB
    (restrict_volume_eq_of_polynomialMoments hA hB moments)

theorem exists_polynomialMoment_ne {d : ℕ} (A B : Body d) (hne : A ≠ B) :
    ∃ p : MvPolynomial (Fin d) ℚ, polynomialMoment p A.points ≠ polynomialMoment p B.points := by
  by_contra! he
  apply hne
  apply Subtype.ext
  apply NonemptyCompacts.ext
  exact convex_eq_of_polynomialMoments A.val.isCompact B.val.isCompact A.property.1 B.property.1
    A.property.2 B.property.2 he

/-- Ordinary multi-indices, with only finitely many nonzero exponents. -/
abbrev MultiIndex (d : ℕ) := Fin d →₀ ℕ

def monomialEvaluation {d : ℕ} (α : MultiIndex d) : C(Space d, ℝ) :=
  ⟨fun x => ∏ i : Fin d, x i ^ α i, by fun_prop⟩

/-- A single ordinary volume moment, in the customary unnormalized units. -/
def ordinaryMoment {d : ℕ} (α : MultiIndex d) (A : Set (Space d)) : ℝ :=
  ∫ x in A, monomialEvaluation α x ∂volume

/-- Every polynomial moment is the explicit finite rational linear
combination of the corresponding ordinary monomial moments. -/
theorem polynomialMoment_eq_sum {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    {A : Set (Space d)} (hA : IsCompact A) :
    polynomialMoment p A =
      ∑ α ∈ p.support, (algebraMap ℚ ℝ) (MvPolynomial.coeff α p) * ordinaryMoment α A := by
  unfold polynomialMoment polynomialEvaluation RationalMomentApproximation.eval
  simp only [ContinuousMap.coe_mk, MvPolynomial.eval₂_eq']
  rw [integral_finset_sum]
  · simp only [ordinaryMoment, monomialEvaluation, ContinuousMap.coe_mk, integral_const_mul]
  · intro α _
    exact (continuous_const.mul (monomialEvaluation α).continuous).continuousOn.integrableOn_compact hA

/-- The ordinary monomial moments themselves already separate actual
full-dimensional compact convex blocks. -/
theorem convex_eq_of_ordinaryMoments {d : ℕ} {A B : Set (Space d)}
    (hA : IsCompact A) (hB : IsCompact B) (convexA : Convex ℝ A) (convexB : Convex ℝ B)
    (interiorA : (interior A).Nonempty) (interiorB : (interior B).Nonempty)
    (moments : ∀ α : MultiIndex d, ordinaryMoment α A = ordinaryMoment α B) : A = B := by
  apply convex_eq_of_polynomialMoments hA hB convexA convexB interiorA interiorB
  intro p
  rw [polynomialMoment_eq_sum p hA, polynomialMoment_eq_sum p hB]
  simp only [moments]

theorem exists_ordinaryMoment_ne {d : ℕ} (A B : Body d) (hne : A ≠ B) :
    ∃ α : MultiIndex d, ordinaryMoment α A.points ≠ ordinaryMoment α B.points := by
  by_contra! he
  apply hne
  apply Subtype.ext
  apply NonemptyCompacts.ext
  exact convex_eq_of_ordinaryMoments A.val.isCompact B.val.isCompact A.property.1 B.property.1
    A.property.2 B.property.2 he

/-- Every ordinary moment is continuous on the entire Hausdorff space of
nonempty compact convex sets, including sets with empty ambient interior. -/
def ordinaryMomentCharacteristic {d : ℕ} (α : MultiIndex d) : C(CompactConvex d, ℝ) :=
  ⟨fun C => ordinaryMoment α (C.val : Set (Space d)),
    ConvexLimits.continuous_integral_of_locallyIntegrable volume volume
      Measure.AbsolutelyContinuous.rfl (monomialEvaluation α).continuous.locallyIntegrable⟩

end NRR.PolynomialMomentSeparation
