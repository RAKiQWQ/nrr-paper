import NRR.Stability
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Rational approximation of moment characteristics

Rational multivariate polynomials approximate continuous real functions on a compact
moment input set. A compact family already excluded by continuous characteristics
can therefore be excluded by rational polynomials, with a strictly positive uniform
gap. The geometric existence of the continuous excluding characteristics is an
explicit hypothesis; this file does not construct a four-moment counterexample.
-/

open Set

noncomputable section

namespace NRR.RationalMomentApproximation

/-- Evaluation of a rational polynomial at real moment coordinates. -/
def eval {ι : Type*} (p : MvPolynomial ι ℚ) (x : ι → ℝ) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p

theorem continuous_eval {ι : Type*} (p : MvPolynomial ι ℚ) :
    Continuous (eval p) := by
  simpa only [eval, MvPolynomial.eval_map] using
    (p.map (algebraMap ℚ ℝ)).continuous_eval

/-- The closure of a rational subalgebra of real continuous functions is also a
real subalgebra: rational constant functions approximate all real constants. -/
private def realClosure {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℚ C(X, ℝ)) : Subalgebra ℝ C(X, ℝ) where
  toSubsemiring := A.topologicalClosure.toSubsemiring
  algebraMap_mem' r := by
    refine Rat.denseRange_cast.induction_on
      (p := fun t : ℝ => algebraMap ℝ C(X, ℝ) t ∈ A.topologicalClosure) r
      (A.isClosed_topologicalClosure.preimage (continuous_algebraMap ℝ C(X, ℝ))) ?_
    intro q
    convert A.topologicalClosure.algebraMap_mem q using 1

/-- Stone-Weierstrass with genuinely rational coefficients. The coordinate
family need only separate points; finiteness of its index type is unnecessary. -/
theorem exists_rational_polynomial_near_coordinates
    {ι X : Type*} [TopologicalSpace X] [CompactSpace X]
    (coordinate : ι → C(X, ℝ))
    (separate : ∀ x y : X, x ≠ y → ∃ i, coordinate i x ≠ coordinate i y)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial ι ℚ, ∀ x, |eval p (fun i => coordinate i x) - f x| < ε := by
  let φ : MvPolynomial ι ℚ →ₐ[ℚ] C(X, ℝ) := MvPolynomial.aeval coordinate
  let A := φ.range
  let B := realClosure A
  have hsep : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := separate x y hxy
    refine ⟨coordinate i, ⟨coordinate i, ?_, rfl⟩, hi⟩
    exact A.le_topologicalClosure ⟨MvPolynomial.X i, MvPolynomial.aeval_X coordinate i⟩
  have hd : closure (A : Set C(X, ℝ)) = Set.univ := by
    have hB := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints B hsep
    have hc : IsClosed (B : Set C(X, ℝ)) := A.isClosed_topologicalClosure
    have he : (B.topologicalClosure : Set C(X, ℝ)) = B := hc.closure_eq
    rw [hB] at he
    exact he.symm
  have hf : f ∈ closure (A : Set C(X, ℝ)) := by rw [hd]; trivial
  obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have he : (φ p) x = eval p (fun i => coordinate i x) :=
    MvPolynomial.comp_aeval_apply coordinate (ContinuousMap.evalAlgHom ℚ ℝ x) p
  rw [← he, ← Real.dist_eq]
  exact (ContinuousMap.dist_apply_le_dist x).trans_lt (by simpa [dist_comm] using hgf)

/-- Uniform rational polynomial approximation on any compact set of moment
inputs, including a compact subset of four-dimensional moment space. -/
theorem exists_rational_polynomial_uniform
    {ι : Type*} (K : Set (ι → ℝ)) (hK : IsCompact K)
    (f : C(K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial ι ℚ, ∀ x : K, |eval p x.val - f x| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let coordinate : ι → C(K, ℝ) := fun i =>
    ⟨fun x => x.val i, (continuous_apply i).comp continuous_subtype_val⟩
  apply exists_rational_polynomial_near_coordinates coordinate ?_ f hε
  intro x y hxy
  by_contra! he
  exact hxy (Subtype.ext (funext he))

/-- An unbundled version, requiring continuity only on the compact input set. -/
theorem exists_rational_polynomial_uniform_on
    {ι : Type*} (K : Set (ι → ℝ)) (hK : IsCompact K)
    (f : (ι → ℝ) → ℝ) (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial ι ℚ, ∀ x ∈ K, |eval p x - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_rational_polynomial_uniform K hK ⟨_, hf.restrict⟩ hε
  exact ⟨p, fun x hx => hp ⟨x, hx⟩⟩

/-- A continuous finite characteristic family which excludes every member of a
compact family has a uniform, strictly positive componentwise exclusion gap. -/
theorem continuous_uniform_gap
    {n k : ℕ} {X : Type*} [TopologicalSpace X]
    (v : Fin n → Fin k → C(X, ℝ)) (s : Set X) (hs : IsCompact s)
    (exclude : ∀ x ∈ s, ∃ i j a, v i a x ≠ v j a x) :
    ∃ δ > (0 : ℝ), ∀ x ∈ s, ∃ i j a, δ < |v i a x - v j a x| := by
  let spread : X → ℝ := fun x =>
    ∑ a, Stability.variation (fun i => v i a x)
  have hc : Continuous spread := by
    dsimp [spread, Stability.variation]
    fun_prop
  have hp : ∀ x ∈ s, 0 < spread x := by
    intro x hx
    obtain ⟨i, j, a, hij⟩ := exclude x hx
    apply (Stability.variation_pos (v := fun i => v i a x) ⟨i, j, hij⟩).trans_le
    apply Finset.single_le_sum (f := fun b => Stability.variation (fun i => v i b x))
    · intro b _
      unfold Stability.variation
      positivity
    · exact Finset.mem_univ a
  obtain ⟨m, hm, hmin⟩ := hs.exists_forall_le' hc.continuousOn hp
  let N : ℝ := (k : ℝ) * (n : ℝ) ^ 2
  let δ := m / (N + 1)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_contra! h
  have upper : spread x ≤ ∑ _a : Fin k, ∑ _i : Fin n, ∑ _j : Fin n, δ := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_le_sum (fun j _ => by simpa [Real.dist_eq] using h i j a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at upper
  have hden : δ * (N + 1) = m := by
    dsimp [δ]
    field_simp
  have hu : spread x ≤ N * δ := by dsimp [N]; nlinarith [upper]
  nlinarith [hmin x hx]

/-- Simultaneous rational approximation preserves exclusion of an entire compact
family. Both the approximation accuracy and a strict uniform exclusion gap are
provided. The compact moment set is independent of the partition parameter space. -/
theorem exists_rational_polynomials_excluding
    {ι X : Type*} {n k : ℕ} [TopologicalSpace X]
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (cell : Fin n → C(X, K)) (f : Fin k → C(K, ℝ))
    (s : Set X) (hs : IsCompact s)
    (exclude : ∀ x ∈ s, ∃ i j a, f a (cell i x) ≠ f a (cell j x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : Fin k → MvPolynomial ι ℚ) (δ : ℝ), 0 < δ ∧
      (∀ a (z : K), |eval (p a) z.val - f a z| < ε) ∧
      (∀ x ∈ s, ∃ i j a,
        δ < |eval (p a) (cell i x).val - eval (p a) (cell j x).val|) := by
  obtain ⟨η, hη, hgap⟩ := continuous_uniform_gap
    (fun i a => (f a).comp (cell i)) s hs exclude
  have ht : 0 < min ε (η / 4) := lt_min hε (by positivity)
  have ha (a : Fin k) := exists_rational_polynomial_uniform K hK (f a) ht
  choose p hp using ha
  refine ⟨p, η / 2, by positivity, ?_, ?_⟩
  · intro a z
    exact (hp a z).trans_le (min_le_left _ _)
  · intro x hx
    obtain ⟨i, j, a, hij⟩ := hgap x hx
    have hi : dist (f a (cell i x)) (eval (p a) (cell i x).val) < η / 4 := by
      rw [dist_comm, Real.dist_eq]
      exact (hp a (cell i x)).trans_le (min_le_right _ _)
    have hj : dist (eval (p a) (cell j x).val) (f a (cell j x)) < η / 4 := by
      rw [Real.dist_eq]
      exact (hp a (cell j x)).trans_le (min_le_right _ _)
    have hd := dist_triangle (f a (cell i x))
      (eval (p a) (cell i x).val) (f a (cell j x))
    have he := dist_triangle (eval (p a) (cell i x).val)
      (eval (p a) (cell j x).val) (f a (cell j x))
    refine ⟨i, j, a, ?_⟩
    simp only [ContinuousMap.comp_apply] at hij
    rw [← Real.dist_eq] at hij ⊢
    linarith

/-- Section 4's rationalization step for four moments and two characteristics.
The existence and exclusion properties of the continuous four-moment
characteristics remain explicit hypotheses. -/
theorem exists_two_rational_four_moment_polynomials
    {X : Type*} {n : ℕ} [TopologicalSpace X]
    (K : Set (Fin 4 → ℝ)) (hK : IsCompact K)
    (cell : Fin n → C(X, K)) (f : Fin 2 → C(K, ℝ))
    (s : Set X) (hs : IsCompact s)
    (exclude : ∀ x ∈ s, ∃ i j a, f a (cell i x) ≠ f a (cell j x)) :
    ∃ (p : Fin 2 → MvPolynomial (Fin 4) ℚ) (δ : ℝ), 0 < δ ∧
      ∀ x ∈ s, ∃ i j a,
        δ < |eval (p a) (cell i x).val - eval (p a) (cell j x).val| := by
  obtain ⟨p, δ, hδ, _, hgap⟩ := exists_rational_polynomials_excluding
    K hK cell f s hs exclude (ε := 1) zero_lt_one
  exact ⟨p, δ, hδ, hgap⟩

end NRR.RationalMomentApproximation
