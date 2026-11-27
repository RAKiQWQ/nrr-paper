import NRR.Descent
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.Bounded

open Set Topology
noncomputable section

namespace NRR.Surface

variable {m : ℕ} [NeZero m]

/-- The simultaneous square-root surface in root coordinates. The omitted
q coordinate is recovered by reading the first root. -/
def locus (b : Fin m → ℂ) : Set (Fin m → ℂ) :=
  {z | ∀ i, z i ^ 2 - b i = z 0 ^ 2 - b 0}

theorem isClosed_locus (b : Fin m → ℂ) : IsClosed (locus b) := by
  rw [locus, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (by fun_prop) (by fun_prop)

def reading {b : Fin m → ℂ} (h : ℂ ≃ₜ ℂ) (R : C(locus b, ℂ)) : C(locus b, ℂ × ℂ) :=
  ⟨fun z => (h (z.val 0), R z), (h.continuous.comp ((continuous_apply 0).comp
    continuous_subtype_val)).prodMk R.continuous⟩

def commonValue (b : Fin m → ℂ) (h : ℂ ≃ₜ ℂ) : C(ℂ × ℂ, ℂ) :=
  ⟨fun p => (h.symm p.1) ^ 2 - b 0, by fun_prop⟩

theorem commonValue_reading (b : Fin m → ℂ) (h : ℂ ≃ₜ ℂ) (R : C(locus b, ℂ))
    (z : locus b) (i : Fin m) :
    commonValue b h (reading h R z) = z.val i ^ 2 - b i := by
  simpa [commonValue, reading] using (z.property i).symm

/-- Compactness at infinity is forced by the first block reading. The
second reading can be any continuous function of all the square roots. -/
theorem proper_reading (b : Fin m → ℂ) (h : ℂ ≃ₜ ℂ) (R : C(locus b, ℂ)) :
    IsProperMap (reading h R) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨(reading h R).continuous, ?_⟩
  intro K hK
  obtain ⟨M, hMpos, hM⟩ := (hK.image (h.symm.continuous.comp continuous_fst)).isBounded.exists_pos_norm_le
  let T (i : Fin m) := Metric.closedBall (0 : ℂ) (M^2 + ‖b 0‖ + ‖b i‖ + 1)
  have box := (isClosed_locus b).isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage
    (isCompact_univ_pi (fun i => isCompact_closedBall (0 : ℂ) (M^2 + ‖b 0‖ + ‖b i‖ + 1)))
  apply box.of_isClosed_subset (hK.isClosed.preimage (reading h R).continuous)
  intro z hz i _
  have h0 : ‖z.val 0‖ ≤ M := by
    apply hM
    exact ⟨reading h R z, hz, h.symm_apply_apply _⟩
  have hi : z.val i ^ 2 = (z.val 0 ^ 2 - b 0) + b i := by
    linear_combination z.property i
  have hnorm : ‖z.val i‖ ^ 2 ≤ ‖z.val 0‖ ^ 2 + ‖b 0‖ + ‖b i‖ := calc
    ‖z.val i‖ ^ 2 = ‖z.val i ^ 2‖ := (norm_pow _ _).symm
    _ = ‖(z.val 0 ^ 2 - b 0) + b i‖ := congrArg norm hi
    _ ≤ (‖z.val 0 ^ 2‖ + ‖b 0‖) + ‖b i‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ = _ := by rw [norm_pow]
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [sq_nonneg (‖z.val i‖ - 1), sq_nonneg ‖z.val i‖,
    mul_nonneg (sub_nonneg.mpr h0) (by positivity : 0 ≤ M + ‖z.val 0‖)]

/-- Apply descent to the actual root equations. What remains to supply is
finite coincidence of the chosen R and a zero-free extension on the core. -/
theorem correction_of_extension (b : Fin m → ℂ) (h : ℂ ≃ₜ ℂ) (R : C(locus b, ℂ))
    (old : C(ℂ × ℂ, ℂ)) (core : Set (locus b)) (hcore : IsCompact core)
    (a : Finset (locus b)) (ha : ∀ x ∈ a, x ∈ interior core)
    (multiple : ∀ x y, x ≠ y → reading h R x = reading h R y → x ∈ a)
    (g : C(locus b, ℂ)) (hn : ∀ x, g x ≠ 0)
    (outside : ∀ x ∉ interior core, g x = old (reading h R x) - (x.val 0 ^ 2 - b 0)) :
    ∃ (M : ℝ) (D : C(ℂ × ℂ, ℂ)), 0 < M ∧ (∀ y, ‖D y‖ ≤ M) ∧
       ∀ x : locus b, old (reading h R x) + D (reading h R x) ≠ x.val 0 ^ 2 - b 0 := by
  simpa only [commonValue_reading b h R _ 0] using
    Descent.fromCompactCore (reading h R) (proper_reading b h R).isClosedMap
      old (commonValue b h) core hcore a ha multiple g hn
      (by simpa only [commonValue_reading b h R _ 0] using outside)

end NRR.Surface
