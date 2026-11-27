import NRR.PrimePowerExistenceTestMap

/-!
The configuration space and permutation representation for the prime-power
existence problem. These are explicit spaces and actions, not a replacement
assumption for the missing configuration-space obstruction theorem.
-/

noncomputable section
open Set MeasureTheory

namespace NRR.PrimePower

/-- Ordered configurations of n pairwise distinct sites in Euclidean space. -/
abbrev Configuration (d n : ℕ) :=
  {x : Fin n → Space d // Function.Injective x}

/-- Relabeling is an actual homeomorphism of the distinct-site configuration
space. The inverse in the formula gives a left action of permutations. -/
def relabelConfiguration {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Configuration d n ≃ₜ Configuration d n where
  toFun x := ⟨fun i => x.val (σ.symm i), x.property.comp σ.symm.injective⟩
  invFun x := ⟨fun i => x.val (σ i), x.property.comp σ.injective⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (σ.symm i)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (σ i)).comp continuous_subtype_val

instance configurationAction {d n : ℕ} :
    MulAction (Equiv.Perm (Fin n)) (Configuration d n) where
  smul σ x := relabelConfiguration σ x
  one_smul x := by apply Subtype.ext; funext i; rfl
  mul_smul σ τ x := by apply Subtype.ext; funext i; rfl

/-- No nonidentity permutation fixes a configuration of distinct sites. -/
theorem configuration_action_free {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Configuration d n) (h : σ • x = x) : σ = 1 := by
  apply Equiv.ext
  intro i
  have hv := congrArg (fun y : Configuration d n => y.val (σ i)) h
  change x.val (σ.symm (σ i)) = x.val (σ i) at hv
  exact (x.property (by simpa using hv)).symm

private theorem norm_reindex_rows {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (v : Fin (d - 1) → Fin n → ℝ) :
    ‖fun k i => v k (σ i)‖ = ‖v‖ := by
  have bound (τ : Equiv.Perm (Fin n)) (w : Fin (d - 1) → Fin n → ℝ) :
      ‖fun k i => w k (τ i)‖ ≤ ‖w‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact (norm_le_pi_norm (w k) (τ i)).trans (norm_le_pi_norm w k)
  refine le_antisymm (bound σ v) ?_
  simpa only [Equiv.apply_symm_apply] using bound σ.symm (fun k i => v k (σ i))

/-- The permutation action on the characteristic target preserves its norm
and its zero-sum defining equations. -/
def relabelValues {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ReducedValues d n ≃ₗᵢ[ℝ] ReducedValues d n where
  toFun v := ⟨fun k i => v.val k (σ.symm i), by
    intro k
    rw [Equiv.sum_comp σ.symm (v.val k)]
    exact v.property k⟩
  invFun v := ⟨fun k i => v.val k (σ i), by
    intro k
    rw [Equiv.sum_comp σ (v.val k)]
    exact v.property k⟩
  left_inv v := by apply Subtype.ext; funext k i; simp
  right_inv v := by apply Subtype.ext; funext k i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' v := norm_reindex_rows σ.symm v.val

instance valuesAction {d n : ℕ} :
    MulAction (Equiv.Perm (Fin n)) (ReducedValues d n) where
  smul σ v := relabelValues σ v
  one_smul v := by apply Subtype.ext; funext k i; rfl
  mul_smul σ τ v := by apply Subtype.ext; funext k i; rfl

/-- Equivariance of the actual characteristic evaluation map, with the same
permutation action on cells and target coordinates. -/
theorem evaluation_equivariant {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (σ : Equiv.Perm (Fin n))
    (S : Fin n → Body d) :
    evaluation hn φ (fun i => S (σ.symm i)) = σ • evaluation hn φ S := by
  apply Subtype.ext
  exact evaluation_reindex hn φ σ.symm S

/-- Equivariance is inherited from a continuously varying, equivariantly
relabeled geometric family of cells. -/
theorem testMap_equivariant {X : Type*} [TopologicalSpace X] {d n : ℕ}
    [MulAction (Equiv.Perm (Fin n)) X] (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (cell : Fin n → C(X, Body d))
    (relabel : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : X),
      cell i (σ • x) = cell (σ.symm i) x)
    (σ : Equiv.Perm (Fin n)) (x : X) :
    testMap hn φ cell (σ • x) = σ • testMap hn φ cell x := by
  change evaluation hn φ (fun i => cell i (σ • x)) =
    σ • evaluation hn φ (fun i => cell i x)
  simp_rw [relabel σ]
  exact evaluation_equivariant hn φ σ (fun i => cell i x)

abbrev UnitValues (d n : ℕ) := Metric.sphere (0 : ReducedValues d n) 1

/-- A zero-free test vector normalizes continuously to the unit sphere.
This works also in degenerate dimensions, when the punctured domain is empty. -/
def unitNormalization (d n : ℕ) :
    C({v : ReducedValues d n // v ≠ 0}, UnitValues d n) where
  toFun v := ⟨‖v.val‖⁻¹ • v.val, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr v.property)]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun v => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val

instance unitValuesAction {d n : ℕ} :
    MulAction (Equiv.Perm (Fin n)) (UnitValues d n) where
  smul σ v := ⟨σ • v.val, by
    change ‖relabelValues σ v.val - 0‖ = 1
    rw [sub_zero, (relabelValues σ).norm_map]
    exact mem_sphere_zero_iff_norm.mp v.property⟩
  one_smul v := by apply Subtype.ext; exact one_smul _ v.val
  mul_smul σ τ v := by apply Subtype.ext; exact mul_smul σ τ v.val

theorem unitNormalization_equivariant {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (v : ReducedValues d n) (hv : v ≠ 0) (hσ : σ • v ≠ 0) :
    unitNormalization d n ⟨σ • v, hσ⟩ = σ • unitNormalization d n ⟨v, hv⟩ := by
  apply Subtype.ext
  change ‖relabelValues σ v‖⁻¹ • relabelValues σ v =
    relabelValues σ (‖v‖⁻¹ • v)
  rw [(relabelValues σ).norm_map, (relabelValues σ).map_smul]

/-- The sphere-valued map to which the missing prime-power obstruction applies
if a geometric test map had no zero. -/
def sphereTestMap {X : Type*} [TopologicalSpace X] {d n : ℕ} (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (cell : Fin n → C(X, Body d))
    (nonzero : ∀ x, testMap hn φ cell x ≠ 0) : C(X, UnitValues d n) :=
  (unitNormalization d n).comp
    ⟨fun x => ⟨testMap hn φ cell x, nonzero x⟩,
      (testMap hn φ cell).continuous.subtype_mk nonzero⟩

theorem sphereTestMap_equivariant {X : Type*} [TopologicalSpace X] {d n : ℕ}
    [MulAction (Equiv.Perm (Fin n)) X] (hn : 0 < n)
    (φ : Fin (d - 1) → C(CompactConvex d, ℝ)) (cell : Fin n → C(X, Body d))
    (relabel : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : X),
      cell i (σ • x) = cell (σ.symm i) x)
    (nonzero : ∀ x, testMap hn φ cell x ≠ 0)
    (σ : Equiv.Perm (Fin n)) (x : X) :
    sphereTestMap hn φ cell nonzero (σ • x) = σ • sphereTestMap hn φ cell nonzero x := by
  change unitNormalization d n ⟨testMap hn φ cell (σ • x), nonzero (σ • x)⟩ =
    σ • unitNormalization d n ⟨testMap hn φ cell x, nonzero x⟩
  have he := testMap_equivariant hn φ cell relabel σ x
  have hs : σ • testMap hn φ cell x ≠ 0 := he ▸ nonzero (σ • x)
  rw [show (⟨testMap hn φ cell (σ • x), nonzero (σ • x)⟩ :
      {v : ReducedValues d n // v ≠ 0}) = ⟨σ • testMap hn φ cell x, hs⟩ from Subtype.ext he]
  exact unitNormalization_equivariant σ (testMap hn φ cell x) (nonzero x) hs

end NRR.PrimePower
