import NRR.PrimePowerTopologyOrientation

/-! Determinant characters in all source and target dimensions. These
calculate the actual linear permutation actions, rather than assigning
formal signs to cells without identifying their representation. -/

noncomputable section
open Set Topology
open NRR.PrimePower

namespace NRR.PrimePowerTopology

def reducedRowsEquiv (d n : ℕ) :
    ReducedValues (d+1) n ≃ₗ[ℝ] (Fin d → ReducedValues 2 n) where
  toFun v := fun k => ⟨fun _ => v.val k,fun _ => v.property k⟩
  invFun w := ⟨fun k => (w k).val 0,fun k => (w k).property 0⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv w := by
    funext k
    apply Subtype.ext
    funext j i
    have hj : j = 0 := by apply Fin.ext; have h := j.isLt; omega
    subst j
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The target is `d` copies of the reduced permutation representation,
so its actual orientation character is the `d`-th power of the sign. -/
theorem det_relabelValues {d n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (relabelValues (d := d+1) σ).toLinearEquiv.toLinearMap =
      (Equiv.Perm.sign σ : ℝ)^d := by
  let e := reducedRowsEquiv d n
  have conjugate : e.toLinearMap ∘ₗ
      (relabelValues (d := d+1) σ).toLinearEquiv.toLinearMap ∘ₗ e.symm.toLinearMap =
      LinearMap.pi (fun k : Fin d =>
        (relabelValues (d := 2) σ).toLinearEquiv.toLinearMap.comp (LinearMap.proj k)) := by
    apply LinearMap.ext
    intro w
    funext k
    apply Subtype.ext
    funext j i
    have hj : j = 0 := by apply Fin.ext; have h := j.isLt; omega
    subst j
    rfl
  have det := LinearMap.det_conj
    (relabelValues (d := d+1) σ).toLinearEquiv.toLinearMap e
  rw [conjugate,LinearMap.det_pi] at det
  simp only [det_reduced_row,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at det
  exact det.symm

def ambientRelabel (d : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → Space d) ≃ₗ[ℝ] (Fin n → Space d) where
  toFun x := fun i => x (σ.symm i)
  invFun x := fun i => x (σ i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ambientRowsEquiv (d n : ℕ) :
    (Fin n → Space d) ≃ₗ[ℝ] (Fin d → Fin n → ℝ) where
  toFun x := fun k i => x i k
  invFun w := fun i => WithLp.toLp 2 (fun k => w k i)
  left_inv x := by funext i; ext k; rfl
  right_inv w := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Permuting labelled sites in `Space d` has the same sign in each of
the `d` coordinate rows. In the application `d` is the ambient dimension. -/
theorem det_ambientRelabel (d : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (ambientRelabel d σ).toLinearMap = (Equiv.Perm.sign σ : ℝ)^d := by
  let e := ambientRowsEquiv d n
  have conjugate : e.toLinearMap ∘ₗ (ambientRelabel d σ).toLinearMap ∘ₗ e.symm.toLinearMap =
      LinearMap.pi (fun k : Fin d =>
        (labelPermutationLinear σ).toLinearMap.comp (LinearMap.proj k)) := by
    apply LinearMap.ext
    intro w
    funext k i
    rfl
  have det := LinearMap.det_conj (ambientRelabel d σ).toLinearMap e
  rw [conjugate,LinearMap.det_pi] at det
  simp only [det_labelPermutationLinear,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at det
  exact det.symm

@[simp] theorem ambientRelabel_configuration {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Configuration d n) : ambientRelabel d σ x.val = (σ • x).val := rfl

/-- The source/target orientation quotient in the canonical section is
exactly the permutation sign used in the signed transfer calculation. -/
theorem source_target_orientation_ratio {d n : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (ambientRelabel (d+1) σ).toLinearMap /
      LinearMap.det (relabelValues (d := d+1) σ).toLinearEquiv.toLinearMap =
        (Equiv.Perm.sign σ : ℝ) := by
  rw [det_ambientRelabel,det_relabelValues,pow_succ']
  have nonzero : (Equiv.Perm.sign σ : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_div_cancel_right₀ _ (pow_ne_zero d nonzero)

end NRR.PrimePowerTopology
