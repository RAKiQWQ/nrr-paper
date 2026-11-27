import NRR.CubePolynomialTests
import NRR.CubeStackCompactness

/-! One pair of rational four-moment polynomials for every equal-volume
affine stack, including stacks with large slopes and their cube products. -/

noncomputable section
open Set Filter Topology

namespace NRR.CubeFourMomentReadout

open CubeMomentCorrection RationalMomentApproximation

theorem EqualVolumeStack.intercept_eq {n : ℕ} (hn : 0 < n) (A : EqualVolumeStack n) :
    A.intercept = stackIntercept n :=
  funext (equalVolume_cut_intercepts hn _ _ _ A.bottom A.top A.ordered A.equalVolume)

def EqualVolumeStack.parameters {n : ℕ} (hn : 0 < n) (A : EqualVolumeStack n) : stackSlopes n :=
  ⟨A.slope, A.lowerFace, A.upperFace, by simpa only [A.intercept_eq hn] using A.ordered⟩

def stackOfSlopes {n : ℕ} (hn : 0 < n) (p : stackSlopes n) : EqualVolumeStack n where
  intercept := stackIntercept n
  slope := p.val
  bottom := stackIntercept_zero n
  top := stackIntercept_last n hn
  lowerFace := p.property.1
  upperFace := p.property.2.1
  ordered := p.property.2.2
  equalVolume i j := (volume_cutLayer_of_mem_stackSlopes p.property i).trans
    (volume_cutLayer_of_mem_stackSlopes p.property j).symm

def stackMomentMap {n : ℕ} (i : Fin n) : C(stackSlopes n,Input) :=
  ⟨fun p => cubeFourMoments (2/n) (stackIntercept n i.succ) (p.val i.castSucc) (p.val i.succ),
    by
      have model : Continuous (fun q : Plane × Plane =>
          cubeFourMoments (2/n) (stackIntercept n i.succ) q.1 q.2) := by
        unfold cubeFourMoments
        fun_prop
      exact model.comp (((continuous_apply i.castSucc).comp (continuous_subtype_val : Continuous (fun x : stackSlopes n => x.1))).prodMk
        ((continuous_apply i.succ).comp (continuous_subtype_val : Continuous (fun x : stackSlopes n => x.1))))⟩

theorem EqualVolumeStack.moments_eq {n : ℕ} (hn : 0 < n) (A : EqualVolumeStack n) (i : Fin n) :
    A.moments i = stackMomentMap i (A.parameters hn) := by
  have step : stackIntercept n i.succ - 2/(n : ℝ) = stackIntercept n i.castSucc := by
    simp only [stackIntercept, Fin.val_succ, Fin.coe_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  have eq : cutLayer (2/n) A.intercept A.slope i =
      affineSlab (2/n) (stackIntercept n i.succ) (A.slope i.castSucc) (A.slope i.succ) := by
    simp only [A.intercept_eq hn, cutLayer, affineSlab, step]
  unfold EqualVolumeStack.moments
  rw [eq]
  apply volumeFourMoments_affineSlab _ _ _ _ (by positivity)
  simpa only [step, A.intercept_eq hn] using A.ordered i

private theorem horizontal_stackMomentMap {n : ℕ} (p : stackSlopes n) (i : Fin n) :
    horizontal (stackMomentMap i p) = toComplex (p.val i.succ) - toComplex (p.val i.castSucc) :=
  rfl

/-- The coefficients and the strict gap are independent of all interface
slopes. The integrals in the conclusion are taken over the actual closed cells. -/
theorem exists_rational_polynomials_for_stacks (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ A : EqualVolumeStack (r+2), ∃ i j k,
        γ < |eval (P k) (fourCoordinates (A.moments i)) -
          eval (P k) (fourCoordinates (A.moments j))| := by
  let n := r+2
  have hn' : 0 < n := by dsimp [n]; omega
  letI : CompactSpace (stackSlopes n) := isCompact_iff_compactSpace.mp (isCompact_stackSlopes n hn')
  have balance (p : stackSlopes n) : ∑ i, horizontal (stackMomentMap i p) = 0 := by
    simp_rw [horizontal_stackMomentMap]
    exact sum_consecutive_slope_differences _ (p.property.2.1.trans p.property.1.symm)
  have charts (δ : ℝ) (hδ : 0 < δ) (p : stackSlopes n)
      (hz : ∀ i, horizontal (stackMomentMap i p) = 0) :
      ∀ᶠ q in 𝓝 p, ∃ (A : EqualVolumeStack n) (σ : Equiv.Perm (Fin n)),
        (∀ j, ‖A.slope j‖ ≤ δ) ∧ ∀ i, stackMomentMap (σ i) q = A.moments i := by
    have zero (j : Fin (n+1)) : p.val j = 0 := by
      induction j using Fin.induction with
      | zero => exact p.property.1
      | succ i ih =>
        have he := hz i
        rw [horizontal_stackMomentMap, ih, show toComplex 0 = 0 from rfl, sub_zero] at he
        exact Prod.ext (congrArg Complex.re he) (congrArg Complex.im he)
    have near (j : Fin (n+1)) : ∀ᶠ q : stackSlopes n in 𝓝 p, ‖q.val j‖ ≤ δ := by
      have hc : Continuous (fun q : stackSlopes n => ‖q.val j‖) :=
        ((continuous_apply j).comp (continuous_subtype_val : Continuous (fun x : stackSlopes n => x.1))).norm
      have at_p : ‖p.val j‖ < δ := by simpa only [zero, norm_zero] using hδ
      have ht : ∀ᶠ q : stackSlopes n in 𝓝 p, ‖q.val j‖ < δ :=
        (isOpen_lt hc continuous_const).mem_nhds at_p
      exact ht.mono fun _ h => h.le
    filter_upwards [Filter.eventually_all.mpr near] with q bound
    exact ⟨stackOfSlopes hn' q, Equiv.refl _, bound, fun i =>
      ((stackOfSlopes hn' q).moments_eq hn' i).symm⟩
  obtain ⟨P,γ,hγ,gap⟩ := rational_cube_tests_of_local_stacks r hn stackMomentMap balance charts
  refine ⟨P,γ,hγ,fun A => ?_⟩
  simpa only [A.moments_eq hn'] using gap (A.parameters hn')

/-- The very same two polynomials and gap apply in every product dimension,
with the prescribed normalization of the higher-dimensional Lebesgue integrals. -/
theorem exists_rational_polynomials_for_product_stacks (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ (d : ℕ) (A : EqualVolumeStack (r+2)), ∃ i j k,
        let feature := fun a => CubeProductMoments.productMoments d (r+2 : ℕ)
          (cutLayer (2/(r+2 : ℕ)) A.intercept A.slope a)
        γ < |eval (P k) (feature i) - eval (P k) (feature j)| := by
  obtain ⟨P,γ,hγ,gap⟩ := exists_rational_polynomials_for_stacks r hn
  refine ⟨P,γ,hγ,fun d A => ?_⟩
  obtain ⟨i,j,k,h⟩ := gap A
  refine ⟨i,j,k,?_⟩
  simpa only [CubeProductMoments.productMoments_eq, EqualVolumeStack.moments,
    fourCoordinates_volumeFourMoments (by omega : 0 < r+2)] using h

end NRR.CubeFourMomentReadout
