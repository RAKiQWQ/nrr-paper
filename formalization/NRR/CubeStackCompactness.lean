import NRR.CubeEqualVolumeLayers

/-! Compactness of all ordered affine stacks with fixed exterior faces. -/

noncomputable section
open Set MeasureTheory

namespace NRR.CubeFourMomentReadout

/-- The intercepts of an equal-volume stack. -/
def stackIntercept (n : ℕ) (j : Fin (n+1)) : ℝ :=
  -1 + (j.val : ℝ) * (2 / n)

@[simp] theorem stackIntercept_zero (n : ℕ) : stackIntercept n 0 = -1 := by
  simp [stackIntercept]

@[simp] theorem stackIntercept_last (n : ℕ) (hn : 0 < n) :
    stackIntercept n (Fin.last n) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [stackIntercept, Fin.val_last]
  field_simp; ring

/-- Ordered stacks whose bottom and top slopes vanish. -/
def stackSlopes (n : ℕ) : Set (Fin (n+1) → Plane) :=
  {p | p 0 = 0 ∧ p (Fin.last n) = 0 ∧
    ∀ i : Fin n, ∀ x ∈ squareBase,
      slabHeight (2/n) (stackIntercept n i.castSucc) (p i.castSucc) x.1 x.2 ≤
        slabHeight (2/n) (stackIntercept n i.succ) (p i.succ) x.1 x.2}

theorem isClosed_stackSlopes (n : ℕ) : IsClosed (stackSlopes n) := by
  unfold stackSlopes
  simp only [setOf_and, setOf_forall]
  refine (isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_eq (by fun_prop) continuous_const).inter ?_)
  exact isClosed_iInter fun i => isClosed_iInter fun x =>
    isClosed_iInter fun _ => isClosed_le (by unfold slabHeight; fun_prop)
      (by unfold slabHeight; fun_prop)

private theorem stack_height_bounds {n : ℕ} (hn : 0 < n)
    {p : Fin (n+1) → Plane} (hp : p ∈ stackSlopes n)
    (j : Fin (n+1)) (x : Plane) (hx : x ∈ squareBase) :
    -1 ≤ slabHeight (2/n) (stackIntercept n j) (p j) x.1 x.2 ∧
      slabHeight (2/n) (stackIntercept n j) (p j) x.1 x.2 ≤ 1 := by
  have mono : Monotone (fun j =>
      slabHeight (2/n) (stackIntercept n j) (p j) x.1 x.2) :=
    Fin.monotone_iff_le_succ.mpr (fun i => hp.2.2 i x hx)
  have lo := mono (Fin.zero_le j)
  have hi := mono (Fin.le_last j)
  simpa [hp.1, hp.2.1, stackIntercept_last n hn, slabHeight] using And.intro lo hi

/-- No small-slope restriction is needed: ordering between the two exterior
faces bounds each coordinate of every slope. -/
theorem isCompact_stackSlopes (n : ℕ) (hn : 0 < n) : IsCompact (stackSlopes n) := by
  let m : ℝ := 2/n
  have hm : 0 < m := div_pos (by norm_num) (by exact_mod_cast hn)
  let R : ℝ := 1 / (3*m)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply (isCompact_closedBall (0 : Fin (n+1) → Plane) R).of_isClosed_subset
    (isClosed_stackSlopes n)
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  have xp := stack_height_bounds hn hp j (1, 0) (by norm_num [squareBase])
  have xm := stack_height_bounds hn hp j (-1, 0) (by norm_num [squareBase])
  have yp := stack_height_bounds hn hp j (0, 1) (by norm_num [squareBase])
  have ym := stack_height_bounds hn hp j (0, -1) (by norm_num [squareBase])
  change -1 ≤ _ ∧ _ ≤ 1 at xp xm yp ym
  simp only [slabHeight, mul_one, mul_zero, add_zero, zero_add, mul_neg_one] at xp xm yp ym
  have bx : |(p j).1| ≤ R := by
    apply (le_div_iff₀ (by positivity : 0 < 3*m)).mpr
    rcases le_total 0 (p j).1 with h | h
    · rw [abs_of_nonneg h]; dsimp [m] at *; nlinarith [xp.2, xm.1]
    · rw [abs_of_nonpos h]; dsimp [m] at *; nlinarith [xp.1, xm.2]
  have by' : |(p j).2| ≤ R := by
    apply (le_div_iff₀ (by positivity : 0 < 3*m)).mpr
    rcases le_total 0 (p j).2 with h | h
    · rw [abs_of_nonneg h]; dsimp [m] at *; nlinarith [yp.2, ym.1]
    · rw [abs_of_nonpos h]; dsimp [m] at *; nlinarith [yp.1, ym.2]
  simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using And.intro bx by'

/-- Each cell in an ordered stack has the prescribed volume. -/
theorem volume_cutLayer_of_mem_stackSlopes {n : ℕ}
    {p : Fin (n+1) → Plane} (hp : p ∈ stackSlopes n) (i : Fin n) :
    volume.real (cutLayer (2/n) (stackIntercept n) p i) = 4*(2/n) := by
  unfold cutLayer
  rw [volume_between_affine_graphs (2/n) _ _ _ _ (hp.2.2 i)]
  simp only [stackIntercept, Fin.val_succ, Fin.coe_castSucc, Nat.cast_add, Nat.cast_one]
  ring

end NRR.CubeFourMomentReadout
