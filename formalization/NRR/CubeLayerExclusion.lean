import NRR.CubeEqualVolumeLayers
import NRR.CubeMomentCorrection
import NRR.PrefixMoments

/-! The planar obstruction applied to actual equal-volume cube layers.
The correction can be made uniformly small on the entire four-moment space. -/

noncomputable section
open MeasureTheory

namespace NRR.CubeFourMomentReadout

open CubeMomentCorrection LocalModel GlobalAssembly

/-- Consecutive affine cuts over the square, with the two horizontal cube faces
as their endpoints. The internal intercepts are not prescribed. -/
structure EqualVolumeStack (n : ℕ) where
  intercept : Fin (n+1) → ℝ
  slope : Fin (n+1) → Plane
  bottom : intercept 0 = -1
  top : intercept (Fin.last n) = 1
  lowerFace : slope 0 = 0
  upperFace : slope (Fin.last n) = 0
  ordered : ∀ i : Fin n, ∀ u ∈ squareBase,
    slabHeight (2/n) (intercept i.castSucc) (slope i.castSucc) u.1 u.2 ≤
    slabHeight (2/n) (intercept i.succ) (slope i.succ) u.1 u.2
  equalVolume : ∀ i j, volume.real (cutLayer (2/n) intercept slope i) =
    volume.real (cutLayer (2/n) intercept slope j)

def EqualVolumeStack.moments {n : ℕ} (A : EqualVolumeStack n) (i : Fin n) : Input :=
  volumeFourMoments (2/n) (cutLayer (2/n) A.intercept A.slope i)

theorem sum_consecutive_slope_differences {n : ℕ} (p : Fin (n+1) → Plane)
    (ends : p (Fin.last n) = p 0) :
    ∑ i : Fin n, (toComplex (p i.succ) - toComplex (p i.castSucc)) = 0 := by
  let g (j : Fin (n+1)) := toComplex (p j)
  have he : g (Fin.last n) = g 0 := congrArg toComplex ends
  rw [Finset.sum_sub_distrib]
  change (∑ i : Fin n, g i.succ) - (∑ i : Fin n, g i.castSucc) = 0
  linear_combination Fin.sum_univ_castSucc g - Fin.sum_univ_succ g + he

private theorem secondCellLabels_val (r : ℕ) (j : Option (Fin (r+1))) :
    (secondCellLabels r j).val = layerNumber j := by
  cases j with
  | none => simp [layerNumber]
  | some i =>
    by_cases h : i.val = 0
    · have he : i = 0 := Fin.ext h
      subst i
      simp [layerNumber]
    · have above : (1 : Fin (r+2)) ≤ i.castSucc := by change 1 ≤ i.val; omega
      simp [secondCellLabels, finSuccEquiv'_symm_some_above above, layerNumber, h]

/-- For each non-prime-power count the same base test admits arbitrarily
small global perturbations excluding every equal-volume affine stack in a
fixed slope neighborhood. The base test also detects nonzero balanced
horizontal moment families away from that neighborhood. -/
theorem exists_cube_layer_tests (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ (δ : ℝ) (F : C(Input,ℂ)), 0 < δ ∧
      (∀ b : Fin (r+2) → Input, (∑ i, horizontal (b i)) = 0 →
        (∀ i j, F (b i) = F (b j)) → ∀ i, horizontal (b i) = 0) ∧
      ∀ ε > (0 : ℝ), ∃ G : C(Input,ℂ), (∀ x, dist (F x) (G x) ≤ ε) ∧
        ∀ A : EqualVolumeStack (r+2), (∀ j, ‖A.slope j‖ ≤ δ) →
          ∃ i j, G (A.moments i) ≠ G (A.moments j) := by
  let n := r+2
  have hn' : 0 < n := by dsimp [n]; omega
  let m : ℝ := 2/(n : ℝ)
  have hm : 0 < m := div_pos (by norm_num) (by exact_mod_cast hn')
  obtain ⟨δ, hδ, readout⟩ := exists_equalVolume_layer_readout hn'
  obtain ⟨h, hz, _, hom, branches, M, D, hM, hD, avoid⟩ := exists_planar_correction r hn
  let F := (squareTest h).comp horizontal
  refine ⟨δ, F, hδ, fun b balanced fair =>
    balanced_square_rigidity h.toEquiv hz branches _ balanced fair, ?_⟩
  intro ε hε
  obtain ⟨σ, hσ, small⟩ := exists_small_quadratic
    (TwoInterfaceChart.bound_pos (m := r+1) hM) hε
  let E := cubeCorrection (m := r+1) m hm σ D
  refine ⟨F + E, fun x => ?_, ?_⟩
  · change dist (F x) (F x + E x) ≤ ε
    rw [dist_eq_norm, show F x - (F x + E x) = -E x by abel, norm_neg]
    exact (cubeCorrection_bound m hm σ D hD x).trans small
  intro A slopes
  let t := A.intercept
  let p := A.slope
  let label := secondCellLabels r
  let b (j : Option (Fin (r+1))) := A.moments (label j)
  have exactRead := readout t p A.bottom A.top slopes A.ordered A.equalVolume
  have levels := equalVolume_cut_intercepts hn' m t p A.bottom A.top A.ordered A.equalVolume
  have center (j : Option (Fin (r+1))) : cubeCenter m j = t (label j).succ - m/2 := by
    rw [levels]
    unfold cubeCenter
    rw [Fin.val_succ, show (label j).val = layerNumber j from secondCellLabels_val r j]
  have windows (i j) : window m (cubeCenter m) j (b i) = if j = i then 1 else 0 := by
    unfold window
    rw [center]
    calc
      _ = if label j = label i then 1 else 0 := (exactRead (label i)).2.1 (label j)
      _ = _ := by simp only [show (label j = label i) ↔ j = i from label.injective.eq_iff]
  have w (i : Fin n) : horizontal (A.moments i) =
      toComplex (p i.succ) - toComplex (p i.castSucc) := by
    obtain ⟨_, _, hl, hu⟩ := exactRead i
    rw [hl] at hu
    change toComplex (A.moments i).1 = _
    rw [← toComplex_sub]
    apply congrArg toComplex
    change p i.castSucc + (A.moments i).1 = p i.succ at hu
    rw [← hu]
    abel
  have balance : (∑ i : Fin n, horizontal (A.moments i)) = 0 := by
    simp_rw [w]
    exact sum_consecutive_slope_differences p (A.upperFace.trans A.lowerFace.symm)
  have balance' := label.sum_comp (fun i => horizontal (A.moments i))
  rw [balance, Fintype.sum_option] at balance'
  have balanced : (∑ i : Fin (r+1), horizontal (b (some i))) + horizontal (b none) = 0 := by
    rw [add_comm]
    exact balance'
  have first : horizontal (A.moments 0) = toComplex (p (1 : Fin (n+1))) := by
    rw [w]
    change toComplex (p 1) - toComplex (A.slope 0) = _
    rw [A.lowerFace]
    exact sub_zero _
  have next := w (1 : Fin n)
  have specialTop : t (1 : Fin n).succ = -1 + 2*m := by
    have hi : (1 : Fin n).val = 1 := by simp [n]
    calc
      _ = -1 + ((1 : Fin n).succ.val : ℝ)*m := levels _
      _ = _ := by rw [Fin.val_succ, hi]; norm_num
  have readings : interfaceReading m (-1+2*m) hm (b none) =
      (horizontal (b (some 0)), (∑ i : Fin (r+1), horizontal (b (some i))) -
        horizontal (b (some 0))) := by
    obtain ⟨_, _, hl, hu⟩ := exactRead (1 : Fin n)
    change lowerReadout m (t (1 : Fin n).succ) (A.moments 1) = _ at hl
    change lowerReadout m (t (1 : Fin n).succ) (A.moments 1) + (A.moments 1).1 = _ at hu
    rw [specialTop] at hl hu
    change (toComplex (lowerReadout m (-1+2*m) (A.moments (label none))),
        -toComplex (lowerReadout m (-1+2*m) (A.moments (label none)) +
          (A.moments (label none)).1)) = _
    rw [show label none = 1 from secondCellLabels_none r, hl]
    rw [hl] at hu
    rw [hu]
    apply Eq.trans _ (secondCellLabels_reading (fun i => horizontal (A.moments i)) balance)
    dsimp only
    rw [first, next]
    change (toComplex (p 1), -toComplex (p (1 : Fin n).succ)) =
      (toComplex (p 1), -(toComplex (p 1) + (toComplex (p (1 : Fin n).succ) - toComplex (p 1))))
    congr 1
    abel
  obtain ⟨i,j,diff⟩ := rejects_ordered m (-1+2*m) hm (cubeCenter m) h hom D avoid hσ
    b windows balanced readings
  exact ⟨label i, label j, diff⟩

end NRR.CubeFourMomentReadout
