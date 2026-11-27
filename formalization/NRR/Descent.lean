import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

open Set Topology Function

namespace NRR.Descent

/-- Move a bounded, fiber-compatible continuous correction from the parameter
surface onto the actual space of single-block readings, with the same bound. -/
theorem extendCorrection {S X : Type*} [TopologicalSpace S] [TopologicalSpace X] [NormalSpace X]
    (e : C(S, X)) (he : IsClosedMap e) (δ : C(S, ℂ))
    (consistent : Function.FactorsThrough δ e) {R : ℝ} (hR : 0 < R)
    (bounded : ∀ x, ‖δ x‖ ≤ R) :
    ∃ D : C(X, ℂ), (∀ x, ‖D x‖ ≤ R) ∧ ∀ x, D (e x) = δ x := by
  let Y := Set.range e
  let r : C(S, Y) := ⟨Set.rangeFactorization e, e.continuous.subtype_mk _⟩
  have hsur : Surjective r := by rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩
  have hcl : IsClosedMap r := by
    intro T hT
    have himage : r '' T = Subtype.val ⁻¹' (e '' T) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, Subtype.ext heq⟩
    rw [himage]
    exact (he T hT).preimage continuous_subtype_val
  have hq := hcl.isQuotientMap r.continuous hsur
  have hfac : Function.FactorsThrough δ r := fun _ _ h => consistent (congrArg Subtype.val h)
  let f := hq.lift δ hfac
  have hf (x : S) : f (r x) = δ x := DFunLike.congr_fun (hq.lift_comp δ hfac) x
  letI := Metric.instTietzeExtensionClosedBall ℝ (0 : ℂ) (by simpa using hR : 0 < R)
  obtain ⟨D, hD, hres⟩ := f.exists_forall_mem_restrict_eq he.isClosed_range
    (t := Metric.closedBall (0 : ℂ) R) (by
      intro y
      obtain ⟨x, rfl⟩ := hsur y
      rw [Metric.mem_closedBall, dist_zero_right, hf]
      exact bounded x)
  refine ⟨D, fun x => by simpa using hD x, fun x => ?_⟩
  exact (DFunLike.congr_fun hres (r x)).trans (hf x)

/-- A nonzero residual on the fair surface remains nonzero after descent.
The common value is read from the block, so coincident readings agree. -/
theorem avoidCommonValue {S X : Type} [TopologicalSpace S] [TopologicalSpace X] [NormalSpace X]
    (e : C(S, X)) (he : IsClosedMap e) (old common : C(X, ℂ))
    (g : C(S, ℂ)) (hg : ∀ x, g x ≠ 0) (compatible : Function.FactorsThrough g e)
    {R : ℝ} (hR : 0 < R) (hb : ∀ x, ‖g x - (old (e x) - common (e x))‖ ≤ R) :
    ∃ D : C(X, ℂ), (∀ x, ‖D x‖ ≤ R) ∧ ∀ x, old (e x) + D (e x) ≠ common (e x) := by
  let δ : C(S, ℂ) := g - (old - common).comp e
  have hc : Function.FactorsThrough δ e := by
    intro x y h
    change g x - (old (e x) - common (e x)) = g y - (old (e y) - common (e y))
    rw [compatible h, h]
  obtain ⟨D, hD, heq⟩ := extendCorrection e he δ hc hR hb
  refine ⟨D, hD, fun x h => hg x ?_⟩
  rw [heq] at h
  change old (e x) + (g x - (old (e x) - common (e x))) = common (e x) at h
  linear_combination h

/-- Prescribe a common nonzero value on all the finitely many exceptional
preimages, keeping the residual fixed on the exterior of the compact core. -/
theorem retuneFinite {S : Type} [TopologicalSpace S] [T1Space S] [NormalSpace S]
    (g : C(S, ℂ)) (hg : ∀ x, g x ≠ 0) (B : Set S) (hB : IsClosed B)
    (a : Finset S) (hdis : ∀ x ∈ a, x ∉ B) :
    ∃ G : C(S, ℂ), (∀ x, G x ≠ 0) ∧ Set.EqOn G g B ∧ ∀ x ∈ a, G x = 1 := by
  classical
  induction a using Finset.induction_on with
  | empty => exact ⟨g, hg, fun _ _ => rfl, by simp⟩
  | @insert x a hx ih =>
    obtain ⟨G, hn, hGB, hGa⟩ := ih (fun y hy => hdis y (Finset.mem_insert_of_mem hy))
    have hd : Disjoint (B ∪ (a : Set S)) ({x} : Set S) :=
      Set.disjoint_singleton_right.mpr (by
        rintro (hb | ha)
        · exact hdis x (Finset.mem_insert_self _ _) hb
        · exact hx ha)
    obtain ⟨ψ, hzero, hone, _⟩ := exists_continuous_zero_one_of_isClosed
      (hB.union a.finite_toSet.isClosed) isClosed_singleton hd
    let f : C(S, ℂ) := ⟨fun y => G y * Complex.exp ((ψ y : ℂ) * Complex.log (G x)⁻¹),
      by fun_prop⟩
    have unchanged {y : S} (hy : y ∈ B ∪ (a : Set S)) : f y = G y := by
      have hψ : ψ y = 0 := hzero hy
      simp [f, hψ]
    refine ⟨f, fun y => mul_ne_zero (hn y) (Complex.exp_ne_zero _), ?_, ?_⟩
    · intro y hy
      exact (unchanged (Or.inl hy)).trans (hGB hy)
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | ha
      · have hψ : ψ y = 1 := hone (Set.mem_singleton _)
        simp [f, hψ, Complex.exp_log (inv_ne_zero (hn y)), hn y]
      · exact (unchanged (Or.inr ha)).trans (hGa y ha)

/-- Once the exterior residual has a nonvanishing extension across the
compact surface core, finite multiple fibers cause no further obstruction.
The returned bound is uniform on the whole space of block readings. -/
theorem fromCompactCore {S X : Type} [TopologicalSpace S] [T1Space S] [NormalSpace S]
    [TopologicalSpace X] [NormalSpace X] (e : C(S, X)) (he : IsClosedMap e)
    (old common : C(X, ℂ)) (core : Set S) (hcore : IsCompact core)
    (a : Finset S) (ha : ∀ x ∈ a, x ∈ interior core)
    (multiple : ∀ x y, x ≠ y → e x = e y → x ∈ a)
    (g : C(S, ℂ)) (hn : ∀ x, g x ≠ 0)
    (outside : ∀ x ∉ interior core, g x = old (e x) - common (e x)) :
    ∃ (R : ℝ) (D : C(X, ℂ)), 0 < R ∧ (∀ y, ‖D y‖ ≤ R) ∧
      ∀ x, old (e x) + D (e x) ≠ common (e x) := by
  classical
  obtain ⟨G, hG, hGB, hGa⟩ := retuneFinite g hn (interior core)ᶜ
    isOpen_interior.isClosed_compl a (fun x hx h => h (ha x hx))
  have consistent : Function.FactorsThrough G e := by
    intro x y heq
    by_cases hxy : x = y
    · rw [hxy]
    · rw [hGa x (multiple x y hxy heq), hGa y (multiple y x (Ne.symm hxy) heq.symm)]
  let size : S → ℝ := fun x => ‖G x - (old (e x) - common (e x))‖
  have hs : Continuous size := by dsimp [size]; fun_prop
  obtain ⟨M, hM⟩ := (hcore.image hs).bddAbove
  let R := max 1 M
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb (x : S) : size x ≤ R := by
    by_cases hx : x ∈ core
    · exact (hM (Set.mem_image_of_mem size hx)).trans (le_max_right _ _)
    · have hxi : x ∉ interior core := fun h => hx (interior_subset h)
      have heq : G x = g x := hGB hxi
      simpa [size, heq, outside x hxi] using hR.le
  obtain ⟨D, hD, havoid⟩ := avoidCommonValue e he old common G hG consistent hR hb
  exact ⟨R, D, hR, hD, havoid⟩

end NRR.Descent
