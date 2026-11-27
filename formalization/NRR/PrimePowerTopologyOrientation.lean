import NRR.PrimePowerTopologyCanonicalNormal
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Determinant

/-! Actual determinant characters of the permutation representations
appearing in the canonical section and its configuration-space source. -/

noncomputable section
open Set Topology
open scoped Matrix
open NRR.PrimePower

namespace NRR.PrimePowerTopology

def labelPermutationLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun i => v (σ.symm i)
  invFun v := fun i => v (σ i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem det_labelPermutationLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (labelPermutationLinear σ).toLinearMap = (Equiv.Perm.sign σ : ℝ) := by
  have eq : (labelPermutationLinear σ).toLinearMap =
      Matrix.toLin' (Equiv.Perm.permMatrix ℝ (σ.symm : Equiv.Perm (Fin n))) := by
    apply LinearMap.ext
    intro v
    funext i
    change v (σ.symm i) = ((Equiv.Perm.permMatrix ℝ (σ.symm : Equiv.Perm (Fin n))) *ᵥ v) i
    rw [Matrix.permMatrix_mulVec]
    rfl
  rw [eq,LinearMap.det_toLin',Matrix.det_permutation,Equiv.Perm.sign_symm]

def meanReducedEquiv (n : ℕ) [NeZero n] :
    (Fin n → ℝ) ≃ₗ[ℝ] ℝ × ReducedValues 2 n where
  toFun v := (rowMean v,⟨fun _ => centered v,
    fun _ => sum_centered (Nat.pos_of_ne_zero (NeZero.ne n)) v⟩)
  invFun p := fun i => p.1+p.2.val 0 i
  left_inv v := by
    funext i
    change rowMean v+(v i-rowMean v) = v i
    ring
  right_inv p := by
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have mean : rowMean (fun i => p.1+p.2.val 0 i) = p.1 := by
      simp only [rowMean,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,p.2.property 0,add_zero]
      exact mul_div_cancel_left₀ _ hn
    apply Prod.ext
    · exact mean
    · apply Subtype.ext
      funext k i
      have hk : k = 0 := by apply Fin.ext; have h := k.isLt; omega
      subst k
      change p.1+p.2.val 0 i-rowMean (fun j => p.1+p.2.val 0 j) = p.2.val 0 i
      rw [mean]
      ring
  map_add' v w := by
    apply Prod.ext
    · change rowMean (v+w) = rowMean v+rowMean w
      simp only [rowMean,Pi.add_apply,Finset.sum_add_distrib,add_div]
    · apply Subtype.ext
      funext k i
      change centered (v+w) i = centered v i+centered w i
      simp only [centered,rowMean,Pi.add_apply,Finset.sum_add_distrib,add_div]
      ring
  map_smul' a v := by
    apply Prod.ext
    · change rowMean (a • v) = a*rowMean v
      simp only [rowMean,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
      ring
    · apply Subtype.ext
      funext k i
      change centered (a • v) i = a*centered v i
      simp only [centered,rowMean,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
      ring

theorem meanReducedEquiv_intertwines {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) :
    meanReducedEquiv n (labelPermutationLinear σ v) =
      (rowMean v,relabelValues (d := 2) σ (meanReducedEquiv n v).2) := by
  apply Prod.ext
  · exact rowMean_reindex σ.symm v
  · apply Subtype.ext
    funext k
    exact centered_reindex σ.symm v

theorem det_reduced_row {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (relabelValues (d := 2) σ).toLinearEquiv.toLinearMap =
      (Equiv.Perm.sign σ : ℝ) := by
  let e := meanReducedEquiv n
  have conjugate : e.toLinearMap ∘ₗ (labelPermutationLinear σ).toLinearMap ∘ₗ e.symm.toLinearMap =
      LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        (relabelValues (d := 2) σ).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro p
    change e (labelPermutationLinear σ (e.symm p)) = (p.1,relabelValues σ p.2)
    rw [meanReducedEquiv_intertwines]
    have he := e.apply_symm_apply p
    exact congrArg (fun z : ℝ × ReducedValues 2 n => (z.1,relabelValues σ z.2)) he
  have det := LinearMap.det_conj (labelPermutationLinear σ).toLinearMap e
  rw [conjugate,LinearMap.det_prodMap,LinearMap.det_id,one_mul,det_labelPermutationLinear] at det
  exact det

end NRR.PrimePowerTopology
