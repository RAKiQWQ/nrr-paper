import NRR.SurfaceEnds
import NRR.SurfaceExtension
import NRR.PlanarCorrection

/-! Boundary winding of the old residual from the adjacent two-branch sums. -/

open Finset Set Topology
open scoped unitInterval
noncomputable section

namespace NRR.Surface

def positiveCount {m : ℕ} (signs : Fin m → Bool) :=
  (Finset.univ.filter (fun i => signs i = false)).card

theorem positiveCount_le {m : ℕ} (signs : Fin m → Bool) : positiveCount signs ≤ m := by
  simpa [positiveCount] using Finset.card_le_card
    (Finset.filter_subset (fun i => signs i = false) (univ : Finset (Fin m)))

private theorem sum_withSign {m : ℕ} (signs : Fin m → Bool) (h : ℂ → ℂ) (z : ℂ) :
    ∑ i, h (withSign (signs i) z) = LocalModel.branchSum h m (positiveCount signs) z := by
  classical
  let A := Finset.univ.filter (fun i => signs i = false)
  have hsub : A ⊆ univ := subset_univ A
  have hl (i : Fin m) (hi : i ∈ A) : h (withSign (signs i) z) = h z := by
    simp [withSign, (mem_filter.mp hi).2]
  have hr (i : Fin m) (hi : i ∈ Finset.univ \ A) : h (withSign (signs i) z) = h (-z) := by
    cases he : signs i
    · exact False.elim ((mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, he⟩))
    · rfl
  rw [← sum_sdiff hsub, sum_congr rfl hl, sum_congr rfl hr]
  simp only [Finset.sum_const, Finset.card_sdiff_of_subset hsub, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change _ = (A.card : ℂ) * h z + ((m - A.card : ℕ) : ℂ) * h (-z)
  exact add_comm _ _

/-- The tested plane loop with j positive preimages out of n. -/
def branchLoop (h : ℂ ≃ₜ ℂ) (n j : ℕ) : C(Circle, ℂ) :=
  ⟨fun u => LocalModel.branchSum h n j u, by unfold LocalModel.branchSum; fun_prop⟩

/-- Winding of a nonvanishing complex loop, via the covering lift of its phase. -/
def complexWinding (g : C(Circle, ℂ)) (hn : ∀ u, g u ≠ 0) : ℝ := winding (phaseOf g hn)

theorem complexWinding_homotopy (g h : C(Circle, ℂ)) (gn : ∀ u, g u ≠ 0) (hn : ∀ u, h u ≠ 0)
    (H : C(I × Circle, ℂ)) (hH : ∀ p, H p ≠ 0) (h0 : ∀ u, H (0,u) = g u)
    (h1 : ∀ u, H (1,u) = h u) : complexWinding g gn = complexWinding h hn := by
  apply winding_homotopy _ _ (phaseOf H hH)
  · intro u
    apply Circle.ext
    change H (0,u) / (‖H (0,u)‖ : ℂ) = g u / (‖g u‖ : ℂ)
    rw [h0]
  · intro u
    apply Circle.ext
    change H (1,u) / (‖H (1,u)‖ : ℂ) = h u / (‖h u‖ : ℂ)
    rw [h1]

theorem complexWinding_mul (g h : C(Circle, ℂ)) (gn : ∀ u, g u ≠ 0) (hn : ∀ u, h u ≠ 0) :
    complexWinding (g*h) (fun u => mul_ne_zero (gn u) (hn u)) =
      complexWinding g gn + complexWinding h hn := by
  have he : phaseOf (g*h) (fun u => mul_ne_zero (gn u) (hn u)) = phaseOf g gn * phaseOf h hn := by
    ext u
    change g u * h u / (‖g u * h u‖ : ℂ) =
      (g u / (‖g u‖ : ℂ)) * (h u / (‖h u‖ : ℂ))
    rw [norm_mul, Complex.ofReal_mul, div_mul_div_comm]
  exact (congrArg winding he).trans (winding_mul _ _)

def limitingResidual {m : ℕ} (h : ℂ ≃ₜ ℂ) (signs : Fin m → Bool) : C(Circle, ℂ) :=
  ⟨fun u => (h.symm (-(∑ i, h (withSign (signs i) u))))^2 - (u : ℂ)^2, by
    have c (i : Fin m) : Continuous (fun u : Circle => h (withSign (signs i) u)) :=
      h.continuous.comp ((continuous_withSign _).comp continuous_subtype_val)
    exact ((h.symm.continuous.comp (continuous_finset_sum _ fun i _ => c i).neg).pow 2).sub
      (continuous_subtype_val.pow 2)⟩

private theorem adjacent_sums {m : ℕ} (signs : Fin m → Bool) (h : ℂ ≃ₜ ℂ) (u : Circle) :
    h u + (∑ i, h (withSign (signs i) u)) = branchLoop h (m+1) (positiveCount signs+1) u ∧
    h (-(u : ℂ)) + (∑ i, h (withSign (signs i) u)) = branchLoop h (m+1) (positiveCount signs) u := by
  rw [sum_withSign]
  have hle := positiveCount_le signs
  change _ = LocalModel.branchSum _ _ _ _ ∧ _ = LocalModel.branchSum _ _ _ _
  simp [LocalModel.branchSum, Nat.cast_sub hle, Nat.cast_sub (show positiveCount signs ≤ m+1 by omega)]
  constructor <;> ring

/-- Both roots of the limiting difference move under the very same isotopy.
Differences cannot vanish since every time slice is injective. -/
theorem limitingResidual_winding {m : ℕ} [NeZero m] (h : ℂ ≃ₜ ℂ) (hzero : h 0 = 0)
    (H : C(I × ℂ, ℂ)) (inj : ∀ s, Function.Injective (fun z => H (s,z)))
    (id₀ : ∀ z, H (0,z) = z) (end₁ : ∀ z, H (1,z) = h z)
    (avoid : ∀ z ≠ 0, ∀ j ≤ m+1, LocalModel.branchSum h (m+1) j z ≠ 0)
    (signs : Fin m → Bool) :
    complexWinding (limitingResidual h signs)
      (fun u => sub_ne_zero.mpr (end_limit_of_avoid h hzero avoid signs u)) =
      complexWinding (branchLoop h (m+1) (positiveCount signs + 1))
        (fun u => avoid u u.coe_ne_zero _ (by have := positiveCount_le signs; omega)) +
      complexWinding (branchLoop h (m+1) (positiveCount signs))
        (fun u => avoid u u.coe_ne_zero _ (by have := positiveCount_le signs; omega)) := by
  let X (u : Circle) := h.symm (-(∑ i, h (withSign (signs i) u)))
  have cX : Continuous X := by
    apply h.symm.continuous.comp
    exact (continuous_finset_sum _ fun i _ => h.continuous.comp
      ((continuous_withSign (signs i)).comp continuous_subtype_val)).neg
  let F (p : I × Circle) := (H (p.1,(p.2 : ℂ)) - H (p.1,X p.2)) *
    (H (p.1,-(p.2 : ℂ)) - H (p.1,X p.2))
  have hF : Continuous F := by unfold F; fun_prop
  have hn (p : I × Circle) : F p ≠ 0 := by
    have hne : X p.2 ^ 2 ≠ (p.2 : ℂ)^2 := end_limit_of_avoid h hzero avoid signs p.2
    apply mul_ne_zero
    · intro he
      have e := inj p.1 (sub_eq_zero.mp he)
      exact hne (congrArg (· ^ 2) e.symm)
    · intro he
      have e := inj p.1 (sub_eq_zero.mp he)
      exact hne (by rw [← e]; simp)
  let g := branchLoop h (m+1) (positiveCount signs+1)
  let k := branchLoop h (m+1) (positiveCount signs)
  have hj := positiveCount_le signs
  have gn (u : Circle) : g u ≠ 0 := avoid u u.coe_ne_zero _ (by omega)
  have kn (u : Circle) : k u ≠ 0 := avoid u u.coe_ne_zero _ (by omega)
  refine (complexWinding_homotopy _ (g*k) _ (fun u => mul_ne_zero (gn u) (kn u))
    ⟨F,hF⟩ hn ?_ ?_).trans (complexWinding_mul g k gn kn)
  · intro u
    change F (0,u) = X u ^2 - (u : ℂ)^2
    simp [F, id₀]
    ring
  · intro u
    change F (1,u) = g u * k u
    have ha := adjacent_sums signs h u
    simp only [F, end₁, X, h.apply_symm_apply, sub_neg_eq_add]
    exact congrArg₂ (·*·) ha.1 ha.2

/-- A family of homeomorphisms given by the straight angular formula is
jointly continuous in its evaluation variables. -/
def straightAction (h : ℂ ≃ₜ ℂ) : C(I × ℂ, ℂ) :=
  ⟨fun p => p.2 + (p.1.val : ℂ) * (h p.2 - p.2), by fun_prop⟩

theorem straightAction_injective_of_angular_family (h : ℂ ≃ₜ ℂ) (V : ℂ → ℂ)
    (he : ∀ z, h z = z + V z)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ k : ℂ ≃ₜ ℂ, ∀ z, k z = z + (t : ℂ)*V z) :
    ∀ s : I, Function.Injective (fun z => straightAction h (s,z)) := by
  intro s x y hxy
  obtain ⟨k,hk⟩ := hs s.val s.property
  apply k.injective
  change x + (s.val : ℂ) * (h x - x) = y + (s.val : ℂ) * (h y - y) at hxy
  simpa [hk, he] using hxy

theorem squareTest_pos_mul (h : ℂ ≃ₜ ℂ)
    (hh : ∀ r : ℝ, 0 < r → ∀ z, h ((r : ℂ)*z) = (r : ℂ)*h z)
    (r : ℝ) (hr : 0 < r) (z : ℂ) : LocalModel.squareTest h ((r : ℂ) * z) =
      (r : ℂ)^2 * LocalModel.squareTest h z := by
  have hi : h.symm ((r : ℂ)*z) = (r : ℂ)*h.symm z := by
    apply h.injective
    rw [h.apply_symm_apply, hh r hr, h.apply_symm_apply]
  change (h.symm _)^2 = _ * (h.symm _)^2
  rw [hi, mul_pow]

/-- For all sufficiently large boundary circles, the winding of the *actual*
residual on each sign component is the sum of the two adjacent plane windings. -/
theorem exists_actual_residual_winding {m : ℕ} [NeZero m] (h : ℂ ≃ₜ ℂ) (hzero : h 0 = 0)
    (hh : ∀ r : ℝ, 0 < r → ∀ z, h ((r : ℂ)*z) = (r : ℂ)*h z)
    (H : C(I × ℂ, ℂ)) (inj : ∀ s, Function.Injective (fun z => H (s,z)))
    (id₀ : ∀ z, H (0,z) = z) (end₁ : ∀ z, H (1,z) = h z)
    (avoid : ∀ z ≠ 0, ∀ j ≤ m+1, LocalModel.branchSum h (m+1) j z ≠ 0)
    (b : Fin m → ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ) (ht : 0 < t), t < ε → ∀ (signs : Fin m → Bool)
      (actual : C(Circle, ℂ)), (∀ u, actual u =
        LocalModel.squareTest h (-(∑ i, h ((endPoint b ht signs u).val i))) -
          ((endPoint b ht signs u).val 0 ^ 2 - b 0)) →
      ∃ hn : ∀ u, actual u ≠ 0, complexWinding actual hn =
        complexWinding (branchLoop h (m+1) (positiveCount signs+1))
          (fun u => avoid u u.coe_ne_zero _ (by have := positiveCount_le signs; omega)) +
        complexWinding (branchLoop h (m+1) (positiveCount signs))
          (fun u => avoid u u.coe_ne_zero _ (by have := positiveCount_le signs; omega)) := by
  obtain ⟨ε,hε,hH⟩ := exists_residual_end_homotopy h.continuous (LocalModel.squareTest h).continuous
    hh (squareTest_pos_mul h hh) b (fun signs u => end_limit_of_avoid h hzero avoid signs u)
  refine ⟨ε,hε,?_⟩
  intro t ht hsmall signs actual ha
  obtain ⟨G,hn,h0,h1⟩ := hH t ht hsmall signs
  have han (u : Circle) : actual u ≠ 0 := by rw [ha, ← h1]; exact hn (1,u)
  have limn (u : Circle) : limitingResidual h signs u ≠ 0 :=
    sub_ne_zero.mpr (end_limit_of_avoid h hzero avoid signs u)
  refine ⟨han, ?_⟩
  exact (complexWinding_homotopy (limitingResidual h signs) actual limn han G hn h0
    (fun u => (h1 u).trans (ha u).symm)).symm.trans
      (limitingResidual_winding h hzero H inj id₀ end₁ avoid signs)

end NRR.Surface

