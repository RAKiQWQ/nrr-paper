import NRR.CubeVolumeMoments
import NRR.CubeProductMoments

/-! Equal-volume affine layers over the square. Consecutive cuts can have
different slopes. Their intercepts are determined by the common volume. -/

noncomputable section
open Set MeasureTheory

namespace NRR.CubeFourMomentReadout

/-- The actual closed cell bounded by consecutive members of a list of planes. -/
def cutLayer {n : ℕ} (m : ℝ) (t : Fin (n+1) → ℝ) (p : Fin (n+1) → Plane)
    (i : Fin n) : Set (Plane × ℝ) :=
  graphSlab (fun u => slabHeight m (t i.castSucc) (p i.castSucc) u.1 u.2)
    (fun u => slabHeight m (t i.succ) (p i.succ) u.1 u.2)

/-- With bottom and top at heights `-1` and `1`, equality of the true layer
volumes fixes every intercept, including for tilted, nonparallel cuts. -/
theorem equalVolume_cut_intercepts {n : ℕ} (hn : 0 < n) (m : ℝ)
    (t : Fin (n+1) → ℝ) (p : Fin (n+1) → Plane)
    (bottom : t 0 = -1) (top : t (Fin.last n) = 1)
    (ordered : ∀ i : Fin n, ∀ u ∈ squareBase,
      slabHeight m (t i.castSucc) (p i.castSucc) u.1 u.2 ≤
        slabHeight m (t i.succ) (p i.succ) u.1 u.2)
    (equal : ∀ i j, volume.real (cutLayer m t p i) = volume.real (cutLayer m t p j)) :
    ∀ j, t j = -1 + (j.val : ℝ) * (2 / n) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let step := t i₀.succ - t i₀.castSucc
  have mass (i : Fin n) : volume.real (cutLayer m t p i) = 4*(t i.succ-t i.castSucc) :=
    volume_between_affine_graphs m _ _ _ _ (ordered i)
  have diff (i : Fin n) : t i.succ - t i.castSucc = step := by
    have e := equal i i₀
    rw [mass i, mass i₀] at e
    dsimp [step]
    linarith
  have levels (j : Fin (n+1)) : t j = -1 + (j.val : ℝ)*step := by
    induction j using Fin.induction with
    | zero => simpa using bottom
    | succ i ih =>
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      simp only [Fin.coe_castSucc] at ih
      linarith [diff i]
  have atTop := levels (Fin.last n)
  rw [top, Fin.val_last] at atTop
  have hs : step = 2 / n := (eq_div_iff (by exact_mod_cast hn.ne')).mpr (by linarith)
  simpa only [hs] using levels

/-- Coordinates in the order used by the two rational polynomials. -/
def fourCoordinates (M : Plane × Plane) : Fin 4 → ℝ :=
  ![M.1.1, M.1.2, M.2.1, M.2.2]

theorem continuous_fourCoordinates : Continuous fourCoordinates := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [fourCoordinates] <;> fun_prop

theorem fourCoordinates_volumeFourMoments {n : ℕ} (hn : 0 < n) (B : Set (Plane × ℝ)) :
    fourCoordinates (volumeFourMoments (2/n) B) = CubeProductMoments.moments3 n B := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have scale : 1 / (4*(2/(n : ℝ))) = (n : ℝ)/8 := by field_simp; norm_num
  funext i
  fin_cases i <;>
    simp [fourCoordinates, volumeFourMoments, CubeProductMoments.moments3,
      CubeProductMoments.density, scale]

private theorem separated_centers {n : ℕ} {m : ℝ} (hm : 0 < m)
    (t : Fin (n+1) → ℝ) (levels : ∀ j, t j = -1 + (j.val : ℝ)*m)
    {i j : Fin n} (hne : i ≠ j) :
    m ≤ |(t i.succ-m/2) - (t j.succ-m/2)| := by
  have gap (a b : Fin n) (h : a < b) : m ≤ t b.succ - t a.succ := by
    have hcast : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast (show a.val+1 ≤ b.val from h)
    rw [levels, levels]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hcast hm.le]
  rcases lt_or_gt_of_ne hne with h | h
  · exact le_trans (by linarith [gap i j h] : m ≤ -((t i.succ-m/2)-(t j.succ-m/2))) (neg_le_abs _)
  · exact le_trans (by linarith [gap j i h] : m ≤ (t i.succ-m/2)-(t j.succ-m/2)) (le_abs_self _)

/-- A single neighborhood in slope space works for all cells. Each actual
equal-volume cell selects precisely its own index and recovers both slopes. -/
theorem exists_equalVolume_layer_readout {n : ℕ} (hn : 0 < n) :
    let m : ℝ := 2/n
    ∃ δ > (0 : ℝ), ∀ (t : Fin (n+1) → ℝ) (p : Fin (n+1) → Plane),
      t 0 = -1 → t (Fin.last n) = 1 → (∀ j, ‖p j‖ ≤ δ) →
      (∀ i : Fin n, ∀ u ∈ squareBase, slabHeight m (t i.castSucc) (p i.castSucc) u.1 u.2 ≤
        slabHeight m (t i.succ) (p i.succ) u.1 u.2) →
      (∀ i j, volume.real (cutLayer m t p i) = volume.real (cutLayer m t p j)) →
      ∀ i : Fin n, let M := volumeFourMoments m (cutLayer m t p i)
        volume.real (cutLayer m t p i) = 8 / n ∧
        (∀ j : Fin n, layerWindow m (t j.succ-m/2) M.2.1 = if j = i then 1 else 0) ∧
        lowerReadout m (t i.succ) M = p i.castSucc ∧
        lowerReadout m (t i.succ) M + M.1 = p i.succ := by
  let m : ℝ := 2/n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < m := div_pos (by norm_num) hn'
  obtain ⟨δ, hδ, small, bound⟩ := exists_readout_radius m 1 hm
  refine ⟨δ, hδ, ?_⟩
  intro t p bot top slopes ordered equal i
  have levels := equalVolume_cut_intercepts hn m t p bot top ordered equal
  have step : t i.succ - m = t i.castSucc := by
    rw [levels, levels]
    simp only [Fin.val_succ, Fin.coe_castSucc, Nat.cast_add, Nat.cast_one, m]
    ring
  have heightBound : |t i.succ| ≤ 1 := by
    rw [levels, abs_le]
    have hle : (i.succ.val : ℝ) ≤ n := by exact_mod_cast (show i.succ.val ≤ n by omega)
    have hmul := mul_le_mul_of_nonneg_right hle hm.le
    have hnm : (n : ℝ)*m = 2 := by dsimp [m]; field_simp
    constructor <;> nlinarith [mul_nonneg (by positivity : 0 ≤ (i.succ.val : ℝ)) hm.le,
      show m = 2/(n : ℝ) from rfl]
  have b₁ (j) : |(p j).1| ≤ δ := (norm_fst_le _).trans (slopes j)
  have b₂ (j) : |(p j).2| ≤ δ := (norm_snd_le _).trans (slopes j)
  have u := b₁ i.succ
  have l := b₁ i.castSucc
  have hslope : -(1/6 : ℝ) < (p i.succ).1 - (p i.castSucc).1 := by
    linarith [(abs_le.mp l).2, (abs_le.mp u).1]
  have repr : cutLayer m t p i = affineSlab m (t i.succ) (p i.castSucc) (p i.succ) := by
    simp only [cutLayer, affineSlab, step]
  have ord : ∀ x ∈ squareBase, slabHeight m (t i.succ-m) (p i.castSucc) x.1 x.2 ≤
      slabHeight m (t i.succ) (p i.succ) x.1 x.2 := by simpa only [step] using ordered i
  change _ ∧ _ ∧ _ ∧ _
  rw [repr, volumeFourMoments_affineSlab _ _ _ _ hm ord, volume_affineSlab _ _ _ _ ord]
  have indexBound := model_V1_center_bound m (t i.succ) δ _ _ hm hδ.le
    l (b₂ i.castSucc) u (b₂ i.succ)
  have active := layerWindow_eq_one m (t i.succ-m/2) _ hm (indexBound.trans (by
    rw [abs_one] at bound
    nlinarith [mul_le_mul_of_nonneg_right heightBound hδ.le]))
  refine ⟨by dsimp [m]; ring, ?_, lowerReadout_model _ _ _ _ hm hslope,
    upperReadout_model _ _ _ _ hm hslope⟩
  intro j
  split_ifs with h
  · simpa only [h] using active
  · exact layerWindows_disjoint m hm (separated_centers hm t levels (Ne.symm h))
      (active.symm ▸ zero_lt_one)

end NRR.CubeFourMomentReadout
