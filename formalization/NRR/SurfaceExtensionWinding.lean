import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic

open Set Topology
open scoped unitInterval Classical
noncomputable section

namespace NRR.Surface

/-- The period translates of one local inverse give an evenly covered arc. -/
theorem circleExp_covering : IsCoveringMap Circle.exp := by
  intro p
  obtain ⟨e, ha, he⟩ := isLocalHomeomorph_circleExp (Complex.arg p)
  have hp : p ∈ e.target := by simpa [← he, Circle.exp_arg] using e.map_source ha
  let U := e.target
  let V := Circle.exp ⁻¹' U
  let l : C(U, ℝ) := ⟨fun u => e.symm u, continuousOn_iff_continuous_restrict.mp e.continuousOn_symm⟩
  have hl (u : U) : Circle.exp (l u) = u := by
    rw [he]
    exact e.right_inv u.property
  let read : C(V, U) := ⟨fun x => ⟨Circle.exp x, x.property⟩,
    (Circle.exp.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have ex (x : V) : ∃ k : ℤ, x.val = l (read x) + k * (2 * Real.pi) :=
    Circle.exp_eq_exp.mp (hl (read x)).symm
  let k (x : V) : ℤ := (ex x).choose
  have hk (x : V) : x.val = l (read x) + k x * (2 * Real.pi) := (ex x).choose_spec
  have hk' (x : V) : (k x : ℝ) = (x.val - l (read x)) / (2 * Real.pi) := by
    apply (eq_div_iff (by positivity)).mpr
    linarith [hk x]
  have ck : Continuous k := by
    apply Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.mpr
    exact ((continuous_subtype_val.sub (l.continuous.comp read.continuous)).div_const _).congr
      (fun x => (hk' x).symm)
  let back (u : U × ℤ) := l u.1 + (u.2 : ℝ) * (2 * Real.pi)
  have hb (u : U × ℤ) : Circle.exp (back u) = u.1.val := by
    rw [← hl u.1, Circle.exp_eq_exp]
    exact ⟨u.2, rfl⟩
  let lift (u : U × ℤ) : V := ⟨back u, show Circle.exp (back u) ∈ U by
    rw [hb]; exact u.1.property⟩
  let H : V ≃ₜ U × ℤ :=
    { toFun x := (read x, k x)
      invFun := lift
      left_inv x := Subtype.ext (hk x).symm
      right_inv u := by
        have hu : read (lift u) = u.1 := Subtype.ext (hb u)
        refine Prod.ext hu ?_
        suffices heq : (k (lift u) : ℝ) = u.2 by exact_mod_cast heq
        rw [hk', hu]
        apply (div_eq_iff (by positivity)).mpr
        change l u.1 + (u.2 : ℝ) * (2 * Real.pi) - l u.1 = _
        ring
      continuous_toFun := read.continuous.prodMk ck
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (l.continuous.comp continuous_fst).add
          (((continuous_of_discreteTopology : Continuous ((↑) : ℤ → ℝ)).comp continuous_snd).mul
            continuous_const) }
  suffices h : IsEvenlyCovered Circle.exp p ℤ from h.to_isEvenlyCovered_preimage
  exact ⟨inferInstance, U, hp, e.open_target, e.open_target.preimage Circle.exp.continuous,
    H, fun _ => rfl⟩

/-- The continuous phase along an interval, in radians. -/
def pathArgument (γ : C(I, Circle)) : C(I, ℝ) :=
  circleExp_covering.liftPath γ (Complex.arg (γ 0)) (Circle.exp_arg _).symm

theorem exp_pathArgument (γ : C(I, Circle)) (t : I) : Circle.exp (pathArgument γ t) = γ t :=
  congr_fun (circleExp_covering.liftPath_lifts γ _ _) t

def phaseChange (γ : C(I, Circle)) : ℝ :=
  (pathArgument γ 1 - pathArgument γ 0) / (2 * Real.pi)

theorem phaseChange_eq (γ : C(I, Circle)) (l : C(I, ℝ)) (hl : ∀ t, Circle.exp (l t) = γ t) :
    phaseChange γ = (l 1 - l 0) / (2 * Real.pi) := by
  let a := Complex.arg (γ 0)
  have hd : Circle.exp (a - l 0) = 1 := by simp [a, Circle.exp_sub, hl]
  let L : C(I, ℝ) := ⟨fun t => l t + (a - l 0), by fun_prop⟩
  have hL : L = pathArgument γ :=
    (circleExp_covering.eq_liftPath_iff' _).mpr ⟨by
      funext t
      change Circle.exp (l t + (a - l 0)) = γ t
      rw [Circle.exp_add, hd, mul_one, hl], by change l 0 + (a - l 0) = a; ring⟩
  unfold phaseChange
  rw [← hL]
  change (l 1 + (a - l 0) - (l 0 + (a - l 0))) / _ = _
  ring

theorem phaseChange_mul (γ η : C(I, Circle)) :
    phaseChange (γ * η) = phaseChange γ + phaseChange η := by
  rw [phaseChange_eq _ (pathArgument γ + pathArgument η) (by
    intro t
    simp [Circle.exp_add, exp_pathArgument])]
  simp only [ContinuousMap.add_apply, phaseChange]
  ring

theorem phaseChange_inv (γ : C(I, Circle)) : phaseChange γ⁻¹ = -phaseChange γ := by
  rw [phaseChange_eq _ (-(pathArgument γ)) (by
    intro t
    simp [Circle.exp_neg, exp_pathArgument])]
  simp only [ContinuousMap.neg_apply, phaseChange]
  ring

/-- Local lifts on either side of a subdivision may be normalized
independently: only their individual phase increments enter the answer. -/
theorem phaseChange_split (γ : C(I, Circle)) (c : I) (a d : C(I, ℝ))
    (ha : ∀ t ≤ c, Circle.exp (a t) = γ t) (hd : ∀ t ≥ c, Circle.exp (d t) = γ t) :
    phaseChange γ = ((a c - a 0) + (d 1 - d c)) / (2 * Real.pi) := by
  let L : C(I, ℝ) := ⟨fun t => if t ≤ c then a t else d t + (a c - d c),
    continuous_if_le continuous_id continuous_const a.continuous.continuousOn
      (d.continuous.add continuous_const).continuousOn (fun t h => by subst t; ring)⟩
  have hc : Circle.exp (a c - d c) = 1 := by simp [Circle.exp_sub, ha c le_rfl, hd c le_rfl]
  have hL (t : I) : Circle.exp (L t) = γ t := by
    change Circle.exp (if t ≤ c then a t else d t + (a c - d c)) = γ t
    split_ifs with ht
    · exact ha t ht
    · rw [Circle.exp_add, hc, mul_one, hd t (le_of_not_ge ht)]
  rw [phaseChange_eq γ L hL]
  change ((if 1 ≤ c then a 1 else d 1 + (a c - d c)) - (if 0 ≤ c then a 0 else _)) / _ = _
  rw [if_pos (show (0 : I) ≤ c from bot_le)]
  split_ifs with h
  · have he : c = 1 := top_unique h
    subst c
    ring
  · ring

/-- One positive turn, starting and ending at 1. -/
def periodPath : C(I, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * t.val), Circle.exp.continuous.comp (by fun_prop)⟩

theorem periodPath_surjective : Function.Surjective periodPath := by
  intro z
  let a := Complex.arg z
  let y := if 0 ≤ a then a else a + 2 * Real.pi
  have hy := Complex.arg_le_pi (z : ℂ)
  have hy' := Complex.neg_pi_lt_arg (z : ℂ)
  change a ≤ Real.pi at hy
  change -Real.pi < a at hy'
  have hy0 : 0 ≤ y := by dsimp [y]; split_ifs <;> linarith [Real.pi_pos]
  have hy1 : y ≤ 2 * Real.pi := by dsimp [y]; split_ifs <;> linarith [Real.pi_pos]
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨⟨y / (2 * Real.pi), div_nonneg hy0 hp.le, (div_le_one hp).mpr hy1⟩, ?_⟩
  change Circle.exp (2 * Real.pi * (y / (2 * Real.pi))) = z
  rw [show 2 * Real.pi * (y / (2 * Real.pi)) = y by field_simp]
  dsimp [y]
  split_ifs
  · exact Circle.exp_arg _
  · rw [Circle.exp_add_two_pi]; exact Circle.exp_arg _

theorem periodPath_fiber {t u : I} (h : periodPath t = periodPath u) :
    t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have heq : t.val = u.val + k := by
    apply mul_left_cancel₀ hp
    linarith only [hk]
  have h1 : (-1 : ℤ) ≤ k := by
    exact_mod_cast (show (-1 : ℝ) ≤ k by linarith [t.property.1,u.property.2])
  have h2 : k ≤ (1 : ℤ) := by
    exact_mod_cast (show (k : ℝ) ≤ 1 by linarith [u.property.1,t.property.2])
  interval_cases k
  · right; left
    norm_num at heq
    exact ⟨Subtype.ext (show t.val = 0 by linarith [t.property.1, u.property.2]),
      Subtype.ext (show u.val = 1 by linarith [t.property.1, u.property.2])⟩
  · left; apply Subtype.ext; simpa using heq
  · right; right
    norm_num at heq
    exact ⟨Subtype.ext (show t.val = 1 by linarith [u.property.1, t.property.2]),
      Subtype.ext (show u.val = 0 by linarith [u.property.1, t.property.2])⟩

/-- Winding measured by the lift of the standard positively oriented circle. -/
def winding (g : C(Circle, Circle)) : ℝ := phaseChange (g.comp periodPath)

theorem winding_integer (g : C(Circle, Circle)) : ∃ k : ℤ, winding g = k := by
  let l := pathArgument (g.comp periodPath)
  have hclose : Circle.exp (l 1) = Circle.exp (l 0) := by
    simp [l, exp_pathArgument, periodPath]
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hclose
  refine ⟨k, (div_eq_iff (by positivity : 2 * Real.pi ≠ 0)).mpr ?_⟩
  change l 1 - l 0 = _
  linarith only [hk]

theorem winding_mul (g h : C(Circle, Circle)) : winding (g * h) = winding g + winding h :=
  phaseChange_mul (g.comp periodPath) (h.comp periodPath)

theorem winding_inv (g : C(Circle, Circle)) : winding g⁻¹ = -winding g :=
  phaseChange_inv (g.comp periodPath)

/-- The winding number is invariant under any free homotopy of circle maps. -/
theorem winding_homotopy (g h : C(Circle, Circle)) (H : C(I × Circle, Circle))
    (h0 : ∀ u, H (0,u) = g u) (h1 : ∀ u, H (1,u) = h u) : winding g = winding h := by
  let Q : C(I × I, Circle) := ⟨fun p => H (p.1, periodPath p.2), by fun_prop⟩
  let a := pathArgument (g.comp periodPath)
  have ha (t : I) : Q (0,t) = Circle.exp (a t) := by
    exact (h0 _).trans (exp_pathArgument (g.comp periodPath) t).symm
  let F := circleExp_covering.liftHomotopy Q a ha
  have hF (s t : I) : Circle.exp (F (s,t)) = H (s, periodPath t) :=
    congr_fun (circleExp_covering.liftHomotopy_lifts Q a ha) (s,t)
  have hD (s : I) : Circle.exp (F (s,1) - F (s,0)) = 1 := by
    rw [Circle.exp_sub, hF, hF, show periodPath 1 = periodPath 0 by simp [periodPath]]
    simp
  have hd := circleExp_covering.const_of_comp (g := fun s : I => F (s,1) - F (s,0))
    (by fun_prop) (fun s t => (hD s).trans (hD t).symm) 0 1
  let slice (s : I) : C(I,ℝ) := ⟨fun t => F (s,t), by fun_prop⟩
  rw [winding, winding, phaseChange_eq _ (slice 0) (fun t => (hF 0 t).trans (h0 _)),
    phaseChange_eq _ (slice 1) (fun t => (hF 1 t).trans (h1 _))]
  exact congrArg (· / (2 * Real.pi)) hd

theorem exists_argument_iff_winding_zero (g : C(Circle, Circle)) :
    (∃ l : C(Circle, ℝ), ∀ x, Circle.exp (l x) = g x) ↔ winding g = 0 := by
  have h01 : periodPath 0 = periodPath 1 := by simp [periodPath]
  constructor
  · rintro ⟨l, hl⟩
    rw [winding, phaseChange_eq _ (l.comp periodPath) (fun t => hl _)]
    simp [h01]
  · intro h
    let L := pathArgument (g.comp periodPath)
    have hclose : L 1 = L 0 := by
      change (L 1 - L 0) / (2 * Real.pi) = 0 at h
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right (by positivity))
    have hf : Function.FactorsThrough L periodPath := by
      intro t u htu
      rcases periodPath_fiber htu with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [rfl, hclose.symm, hclose]
    have hq := periodPath.continuous.isClosedMap.isQuotientMap periodPath.continuous periodPath_surjective
    refine ⟨hq.lift L hf, ?_⟩
    intro x
    obtain ⟨t, rfl⟩ := periodPath_surjective x
    change Circle.exp (((hq.lift L hf).comp periodPath) t) = _
    rw [hq.lift_comp]
    exact exp_pathArgument _ _

end NRR.Surface
