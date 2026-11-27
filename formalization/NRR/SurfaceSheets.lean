import NRR.Surface
import Mathlib.Analysis.Complex.Convex

/-! Closed half-disk parametrizations of the simultaneous square-root locus. -/

open Set Topology
noncomputable section

namespace NRR.Surface

/-- The two formulae agree in their real part. On their respective closed
half-planes they give square roots continuous up to the real axis. -/
def halfRoot (upper : Bool) (z : ℂ) : ℂ :=
  ⟨Real.sqrt ((‖z‖ + z.re) / 2),
   if upper then Real.sqrt ((‖z‖ - z.re) / 2) else -Real.sqrt ((‖z‖ - z.re) / 2)⟩

def halfPlane (upper : Bool) : Set ℂ :=
  if upper then {z | 0 ≤ z.im} else {z | z.im ≤ 0}

theorem continuous_halfRoot (upper : Bool) : Continuous (halfRoot upper) := by
  have mk_eq (x y : ℝ) : Complex.mk x y = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  change Continuous (fun z => halfRoot upper z)
  cases upper <;> simp only [halfRoot, Bool.false_eq_true, ↓reduceIte, mk_eq] <;> fun_prop

@[simp] theorem halfRoot_zero (upper : Bool) : halfRoot upper 0 = 0 := by
  cases upper <;> apply Complex.ext <;> simp [halfRoot]

theorem halfRoot_sq (upper : Bool) {z : ℂ} (hz : z ∈ halfPlane upper) :
    halfRoot upper z ^ 2 = z := by
  let a := Real.sqrt ((‖z‖ + z.re) / 2)
  let b := Real.sqrt ((‖z‖ - z.re) / 2)
  obtain ⟨h₁, h₂⟩ := abs_le.mp (Complex.abs_re_le_norm z)
  have ha : a ^ 2 = (‖z‖ + z.re) / 2 := Real.sq_sqrt (by linarith)
  have hb : b ^ 2 = (‖z‖ - z.re) / 2 := Real.sq_sqrt (by linarith)
  have hsq : (2 * a * b) ^ 2 = |z.im| ^ 2 := calc
    (2 * a * b) ^ 2 = 4 * a ^ 2 * b ^ 2 := by ring
    _ = |z.im| ^ 2 := by rw [ha, hb, sq_abs]; nlinarith [Complex.sq_norm_sub_sq_re z]
  have hab : 2 * a * b = |z.im| := by
    have hn : 0 ≤ 2 * a * b := by dsimp [a, b]; positivity
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · linarith [abs_nonneg z.im]
  cases upper
  · change z.im ≤ 0 at hz
    rw [abs_of_nonpos hz] at hab
    rw [pow_two]
    apply Complex.ext
    · change a * a - (-b) * (-b) = z.re
      nlinarith
    · change a * (-b) + (-b) * a = z.im
      linarith only [hab]
  · change 0 ≤ z.im at hz
    rw [abs_of_nonneg hz] at hab
    rw [pow_two]
    apply Complex.ext
    · change a * a - b * b = z.re
      nlinarith
    · change a * b + b * a = z.im
      linarith only [hab]

def halfDisk (T : ℝ) (upper : Bool) : Set ℂ := Metric.closedBall 0 T ∩ halfPlane upper

theorem isCompact_halfDisk (T : ℝ) (upper : Bool) : IsCompact (halfDisk T upper) := by
  apply (isCompact_closedBall _ _).inter_right
  cases upper
  · exact isClosed_le Complex.continuous_im continuous_const
  · exact isClosed_le continuous_const Complex.continuous_im

theorem isConnected_halfDisk {T : ℝ} (hT : 0 ≤ T) (upper : Bool) : IsConnected (halfDisk T upper) := by
  have hcv : Convex ℝ (halfDisk T upper) := by
    apply (convex_closedBall _ _).inter
    cases upper
    · exact convex_halfSpace_im_le 0
    · exact convex_halfSpace_im_ge 0
  apply hcv.isConnected
  exact ⟨0, Metric.mem_closedBall_self hT, by cases upper <;> simp [halfPlane]⟩

variable {m : ℕ} [NeZero m]

def realLocus (b : Fin m → ℝ) := locus (fun i => (b i : ℂ))

def projection (b : Fin m → ℝ) : C(realLocus b, ℂ) where
  toFun z := z.val 0 ^ 2 - b 0
  continuous_toFun := (((continuous_apply (0 : Fin m)).comp continuous_subtype_val).pow 2).sub
    continuous_const

def diskCore (b : Fin m → ℝ) (T : ℝ) : Set (realLocus b) :=
  projection b ⁻¹' Metric.closedBall 0 T

private def signedRoot (upper neg : Bool) (z : ℂ) : ℂ :=
  if neg then -halfRoot upper z else halfRoot upper z

private theorem signedRoot_sq (upper neg : Bool) {z : ℂ} (hz : z ∈ halfPlane upper) :
    signedRoot upper neg z ^ 2 = z := by
  cases neg <;> simpa [signedRoot] using halfRoot_sq upper hz

private theorem translate_mem_halfPlane {upper : Bool} {q : ℂ} (hq : q ∈ halfPlane upper) (r : ℝ) :
    q + (r : ℂ) ∈ halfPlane upper := by
  cases upper <;> simpa [halfPlane] using hq

/-- Each sign vector selects one continuous sheet over the closed half-disk. -/
def halfSheet (b : Fin m → ℝ) (T : ℝ) (upper : Bool) (σ : Fin m → Bool) :
    C(halfDisk T upper, realLocus b) where
  toFun q := ⟨fun i => signedRoot upper (σ i) (q.val + b i), by
    intro i
    have h (j : Fin m) := signedRoot_sq upper (σ j) (translate_mem_halfPlane q.property.2 (b j))
    rw [h i, h 0]
    ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hr : Continuous (fun q : halfDisk T upper => halfRoot upper (q.val + b i)) :=
      (continuous_halfRoot upper).comp
      (continuous_subtype_val.add (continuous_const (y := (b i : ℂ))))
    cases σ i <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
    · exact hr
    · exact hr.neg

@[simp] theorem projection_halfSheet (b : Fin m → ℝ) (T : ℝ) (upper : Bool)
    (σ : Fin m → Bool) (q : halfDisk T upper) :
    projection b (halfSheet b T upper σ q) = q.val := by
  change signedRoot upper (σ 0) _ ^ 2 - _ = _
  rw [signedRoot_sq upper (σ 0) (translate_mem_halfPlane q.property.2 (b 0))]
  ring

/-- Given all the roots over a point, one can recover a sign vector on
either half-disk that contains the point, also at the branch values. -/
theorem exists_halfSheet {b : Fin m → ℝ} {T : ℝ} {upper : Bool} (x : realLocus b)
    (hx : projection b x ∈ halfDisk T upper) :
    ∃ σ : Fin m → Bool, x ∈ range (halfSheet b T upper σ) := by
  let q : halfDisk T upper := ⟨projection b x, hx⟩
  have h (i : Fin m) : ∃ e : Bool, signedRoot upper e (q.val + b i) = x.val i := by
    have hsq : x.val i ^ 2 = halfRoot upper (q.val + b i) ^ 2 := by
      rw [halfRoot_sq upper (translate_mem_halfPlane hx.2 (b i))]
      change x.val i ^ 2 = (x.val 0 ^ 2 - (b 0 : ℂ)) + (b i : ℂ)
      linear_combination x.property i
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hi | hi
    · exact ⟨false, hi.symm⟩
    · exact ⟨true, hi.symm⟩
  choose σ hσ using h
  exact ⟨σ, q, Subtype.ext (funext hσ)⟩

theorem diskCore_eq_sheets (b : Fin m → ℝ) (T : ℝ) :
    diskCore b T = ⋃ (upper : Bool) (σ : Fin m → Bool), range (halfSheet b T upper σ) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · intro hx
    rcases le_total 0 (projection b x).im with h | h
    · exact ⟨true, exists_halfSheet x ⟨hx, h⟩⟩
    · exact ⟨false, exists_halfSheet x ⟨hx, h⟩⟩
  · rintro ⟨upper, σ, q, rfl⟩
    change projection b _ ∈ Metric.closedBall _ _
    rw [projection_halfSheet]
    exact q.property.1

theorem isCompact_diskCore (b : Fin m → ℝ) (T : ℝ) : IsCompact (diskCore b T) := by
  rw [diskCore_eq_sheets]
  apply isCompact_iUnion
  intro upper
  letI := isCompact_iff_compactSpace.mp (isCompact_halfDisk T upper)
  exact isCompact_iUnion fun σ => isCompact_range (halfSheet b T upper σ).continuous

/-- Two sheets on the same half-disk share the point over `-b i` when
their signs agree except possibly at `i`. -/
theorem halfSheets_meet {b : Fin m → ℝ} {T : ℝ} (upper : Bool) (i : Fin m)
    (hi : |b i| ≤ T) {σ τ : Fin m → Bool} (h : ∀ j, j ≠ i → σ j = τ j) :
    (range (halfSheet b T upper σ) ∩ range (halfSheet b T upper τ)).Nonempty := by
  let q : halfDisk T upper := ⟨-(b i : ℂ), by
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_closedBall, Complex.norm_real] using hi
    · cases upper <;> simp [halfPlane]⟩
  refine ⟨halfSheet b T upper σ q, ⟨q, rfl⟩, q, ?_⟩
  apply Subtype.ext
  funext j
  change signedRoot upper (τ j) (-(b i : ℂ) + b j) =
    signedRoot upper (σ j) (-(b i : ℂ) + b j)
  by_cases hj : j = i
  · subst j
    simp [signedRoot]
  · rw [h j hj]

theorem isConnected_halfSheets {b : Fin m → ℝ} {T : ℝ}
    (hb : ∀ i, |b i| ≤ T) (upper : Bool) :
    IsConnected (⋃ σ : Fin m → Bool, range (halfSheet b T upper σ)) := by
  let pieces := fun σ => range (halfSheet b T upper σ)
  let meet := fun σ τ => (pieces σ ∩ pieces τ).Nonempty
  have hT : 0 ≤ T := (abs_nonneg _).trans (hb 0)
  letI := isConnected_iff_connectedSpace.mp (isConnected_halfDisk hT upper)
  apply IsConnected.iUnion_of_reflTransGen
    (fun σ => isConnected_range (halfSheet b T upper σ).continuous)
  intro σ τ
  let replace (s : Finset (Fin m)) (j : Fin m) := if j ∈ s then τ j else σ j
  have walk (s : Finset (Fin m)) : Relation.ReflTransGen meet σ (replace s) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa [replace] using (Relation.ReflTransGen.refl : Relation.ReflTransGen meet σ σ)
    | insert i s hi ih =>
      apply ih.tail
      apply halfSheets_meet upper i (hb i)
      intro j hj
      simp [replace, hj]
  simpa [replace, meet, pieces] using walk Finset.univ

/-- The actual disk core in the root locus is connected whenever it
contains every branch value. Repeated shifts are allowed. -/
theorem isConnected_diskCore {b : Fin m → ℝ} {T : ℝ} (hb : ∀ i, |b i| ≤ T) :
    IsConnected (diskCore b T) := by
  let pieces := fun upper => ⋃ σ : Fin m → Bool, range (halfSheet b T upper σ)
  have hcore : diskCore b T = pieces true ∪ pieces false := by
    rw [diskCore_eq_sheets]
    exact iSup_bool_eq
  rw [hcore]
  apply IsConnected.union _ (isConnected_halfSheets hb true) (isConnected_halfSheets hb false)
  have hT : 0 ≤ T := (abs_nonneg _).trans (hb 0)
  let q : halfDisk T true := ⟨0, Metric.mem_closedBall_self hT, by simp [halfPlane]⟩
  let σ : Fin m → Bool := fun _ => false
  let x := halfSheet b T true σ q
  have hx : projection b x = 0 := projection_halfSheet b T true σ q
  refine ⟨x, mem_iUnion.mpr ⟨σ, q, rfl⟩, mem_iUnion.mpr ?_⟩
  apply exists_halfSheet x
  rw [hx]
  exact ⟨Metric.mem_closedBall_self hT, by simp [halfPlane]⟩

end NRR.Surface

