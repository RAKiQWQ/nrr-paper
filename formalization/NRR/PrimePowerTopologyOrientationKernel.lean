import NRR.PrimePowerTopologyOrientationRows

/-! The zero-stratum tangent action in the actual canonical splitting.
Its determinant is the permutation sign, not a formally assigned character. -/

noncomputable section
open Set Topology
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

theorem canonicalLinear_ambientRelabel (σ : Equiv.Perm (Fin n))
    (x : Fin n → Space (d+1)) :
    canonicalLinear d n (ambientRelabel (d+1) σ x) =
      relabelValues (d := d+1) σ (canonicalLinear d n x) := by
  apply Subtype.ext
  funext k
  exact centered_reindex σ.symm (fun i => (horizontalHeight d (x i)).1 k)

theorem canonicalLift_relabelValues (σ : Equiv.Perm (Fin n))
    (v : ReducedValues (d+1) n) :
    canonicalLift d n (relabelValues (d := d+1) σ v) =
      ambientRelabel (d+1) σ (canonicalLift d n v) := rfl

def canonicalKernelRelabel (σ : Equiv.Perm (Fin n)) :
    CanonicalKernel d n ≃ₗ[ℝ] CanonicalKernel d n where
  toFun u := ⟨ambientRelabel (d+1) σ u.val,by
    change canonicalLinear d n (ambientRelabel (d+1) σ u.val) = 0
    rw [canonicalLinear_ambientRelabel,show canonicalLinear d n u.val = 0 from u.property,map_zero]⟩
  invFun u := ⟨ambientRelabel (d+1) σ⁻¹ u.val,by
    change canonicalLinear d n (ambientRelabel (d+1) σ⁻¹ u.val) = 0
    rw [canonicalLinear_ambientRelabel,show canonicalLinear d n u.val = 0 from u.property,map_zero]⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    change u.val (σ.symm (σ i)) = u.val i
    rw [σ.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    funext i
    change u.val (σ (σ.symm i)) = u.val i
    rw [σ.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem canonicalNormalLinearEquiv_intertwines (σ : Equiv.Perm (Fin n))
    (x : Fin n → Space (d+1)) :
    canonicalNormalLinearEquiv d n (ambientRelabel (d+1) σ x) =
      (canonicalKernelRelabel σ (canonicalNormalLinearEquiv d n x).1,
        relabelValues (d := d+1) σ (canonicalNormalLinearEquiv d n x).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change ambientRelabel (d+1) σ x-
        canonicalLift d n (canonicalLinear d n (ambientRelabel (d+1) σ x)) =
      ambientRelabel (d+1) σ (x-canonicalLift d n (canonicalLinear d n x))
    rw [map_sub,canonicalLinear_ambientRelabel,canonicalLift_relabelValues]
  · exact canonicalLinear_ambientRelabel σ x

/-- The actual normal splitting diagonalizes the permutation action into
the zero-stratum tangent action and the reduced target action. -/
theorem canonicalNormalRelabel_conjugate (σ : Equiv.Perm (Fin n)) :
    (canonicalNormalLinearEquiv d n).toLinearMap ∘ₗ
      (ambientRelabel (d+1) σ).toLinearMap ∘ₗ (canonicalNormalLinearEquiv d n).symm.toLinearMap =
    LinearMap.prodMap (canonicalKernelRelabel (d := d) σ).toLinearMap
      (relabelValues (d := d+1) σ).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro p
  change canonicalNormalLinearEquiv d n
    (ambientRelabel (d+1) σ ((canonicalNormalLinearEquiv d n).symm p)) = _
  rw [canonicalNormalLinearEquiv_intertwines,(canonicalNormalLinearEquiv d n).apply_symm_apply]
  rfl

theorem det_canonicalKernelRelabel (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (canonicalKernelRelabel (d := d) σ).toLinearMap =
      (Equiv.Perm.sign σ : ℝ) := by
  have conjugate := LinearMap.det_conj (ambientRelabel (d+1) σ).toLinearMap
    (canonicalNormalLinearEquiv d n)
  rw [canonicalNormalRelabel_conjugate,LinearMap.det_prodMap,
    det_relabelValues,det_ambientRelabel] at conjugate
  have nonzero : (Equiv.Perm.sign σ : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  apply (mul_right_inj' (pow_ne_zero d nonzero)).mp
  calc
    _ = LinearMap.det (canonicalKernelRelabel (d := d) σ).toLinearMap *
        (Equiv.Perm.sign σ : ℝ)^d := mul_comm _ _
    _ = (Equiv.Perm.sign σ : ℝ)^(d+1) := conjugate
    _ = _ := pow_succ _ _

end NRR.PrimePowerTopology
