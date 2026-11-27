import NRR.PrimePowerTopologyPermutationDegree
import NRR.PrimePowerTopologyOrientationRows

/-! Genuine top homology characters of the reduced and ambient permutation
representations, with an arbitrary finite-dimensional fixed factor. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- The actual map of one-point compactifications of a linear automorphism. -/
def fiberLinearOnePointMap {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (a : V ≃ₗ[ℝ] V) :
    TopCat.of (OnePoint V) ⟶ TopCat.of (OnePoint V) :=
  let e := a.toContinuousLinearEquiv.toHomeomorph.onePointCongr
  TopCat.ofHom ⟨e, e.continuous⟩

@[simp] theorem fiberLinearOnePointMap_refl (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    fiberLinearOnePointMap (LinearEquiv.refl ℝ V) = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  induction x using OnePoint.rec <;> rfl

theorem fiberLinearOnePointMap_trans {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (a b : V ≃ₗ[ℝ] V) :
    fiberLinearOnePointMap (a.trans b) =
      fiberLinearOnePointMap a ≫ fiberLinearOnePointMap b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  induction x using OnePoint.rec <;> rfl

/-- A scalar homology character transports through an actual linear
conjugacy, without an orientation choice for the conjugating map. -/
theorem fiberLinearOnePointMap_conjugate (R : Type) [Ring R] (k : ℕ) (z : ℤ)
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (a : V ≃ₗ[ℝ] V) (b : W ≃ₗ[ℝ] W) (e : V ≃ₗ[ℝ] W)
    (he : ∀ v, e (a v) = b (e v))
    (hb : HabsMap R k (fiberLinearOnePointMap b) = z • 𝟙 _) :
    HabsMap R k (fiberLinearOnePointMap a) = z • 𝟙 _ := by
  let h := e.toContinuousLinearEquiv.toHomeomorph.onePointCongr
  let E := HabsIsoOfHomotopyEquiv R k h.toHomotopyEquiv
  have hc : fiberLinearOnePointMap a ≫ TopCat.ofHom h.toHomotopyEquiv.toFun =
      TopCat.ofHom h.toHomotopyEquiv.toFun ≫ fiberLinearOnePointMap b := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    induction x using OnePoint.rec with
    | infty => rfl
    | coe v => exact congrArg OnePoint.some (he v)
  apply (cancel_mono E.hom).mp
  change HabsMap R k (fiberLinearOnePointMap a) ≫ HabsMap R k _ =
    (z • 𝟙 _) ≫ HabsMap R k _
  rw [← HabsMap_comp, hc, HabsMap_comp, hb]
  simp

/-- Apply the same linear automorphism to every row. -/
def fiberRowsLinear {V : Type} [AddCommGroup V] [Module ℝ V]
    (a : V ≃ₗ[ℝ] V) (d : ℕ) : (Fin d → V) ≃ₗ[ℝ] (Fin d → V) where
  toFun v k := a (v k)
  invFun v k := a.symm (v k)
  left_inv v := by funext k; simp
  right_inv v := by funext k; simp
  map_add' v w := by funext k; exact a.map_add _ _
  map_smul' c v := by funext k; exact a.map_smul _ _

private def fiberRowsSuccSplit (X V : Type) [AddCommGroup X] [Module ℝ X]
    [AddCommGroup V] [Module ℝ V] (d : ℕ) :
    (X × (Fin (d+1) → V)) ≃ₗ[ℝ] (X × V) × (Fin d → V) :=
  ((LinearEquiv.refl ℝ X).prodCongr
    (Fin.consLinearEquiv ℝ (fun _ : Fin (d+1) => V)).symm).trans
      (LinearEquiv.prodAssoc ℝ X V (Fin d → V)).symm

private def fiberMiddleSwap (X V W : Type) [AddCommGroup X] [Module ℝ X]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] :
    ((X × V) × W) ≃ₗ[ℝ] (X × W) × V :=
  (LinearEquiv.prodAssoc ℝ X V W).trans
    (((LinearEquiv.refl ℝ X).prodCongr (LinearEquiv.prodComm ℝ V W)).trans
      (LinearEquiv.prodAssoc ℝ X W V).symm)

/-- If one row has character `z` with every fixed factor, then `d` rows
have character `z^d`. The proof composes genuine compactified maps. -/
theorem fiberRowsLinearOnePointMap_top (R : Type) [Ring R]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a : V ≃ₗ[ℝ] V) (z : ℤ)
    (ha : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [FiniteDimensional ℝ X],
      HabsMap R (Module.finrank ℝ (X × V))
        (fiberLinearOnePointMap ((LinearEquiv.refl ℝ X).prodCongr a)) = z • 𝟙 _)
    (d : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    HabsMap R (Module.finrank ℝ (X × (Fin d → V)))
      (fiberLinearOnePointMap
        ((LinearEquiv.refl ℝ X).prodCongr (fiberRowsLinear a d))) = z^d • 𝟙 _ := by
  induction d generalizing X with
  | zero =>
    have he : (LinearEquiv.refl ℝ X).prodCongr (fiberRowsLinear a 0) =
        LinearEquiv.refl ℝ (X × (Fin 0 → V)) := by
      apply LinearEquiv.ext
      intro p
      apply Prod.ext
      · rfl
      · funext i; exact Fin.elim0 i
    simp [he]
  | succ d ih =>
    let W := Fin d → V
    let A : ((X × V) × W) ≃ₗ[ℝ] ((X × V) × W) :=
      ((LinearEquiv.refl ℝ X).prodCongr a).prodCongr (LinearEquiv.refl ℝ W)
    let B : ((X × V) × W) ≃ₗ[ℝ] ((X × V) × W) :=
      (LinearEquiv.refl ℝ (X × V)).prodCongr (fiberRowsLinear a d)
    let e := fiberRowsSuccSplit X V d
    let c := fiberMiddleSwap X V W
    have hA : HabsMap R (Module.finrank ℝ ((X × V) × W))
        (fiberLinearOnePointMap A) = z • 𝟙 _ := by
      apply fiberLinearOnePointMap_conjugate R _ z A
        ((LinearEquiv.refl ℝ (X × W)).prodCongr a) c (fun _ => rfl)
      rw [c.finrank_eq]
      exact ha (X × W)
    have hB := ih (X × V)
    apply fiberLinearOnePointMap_conjugate R _ (z^(d+1))
      ((LinearEquiv.refl ℝ X).prodCongr (fiberRowsLinear a (d+1)))
      (A.trans B) e (fun _ => rfl)
    rw [e.finrank_eq, fiberLinearOnePointMap_trans, HabsMap_comp, hA]
    change (z • 𝟙 _) ≫ HabsMap R _ (fiberLinearOnePointMap B) = _
    rw [show HabsMap R (Module.finrank ℝ ((X × V) × W))
      (fiberLinearOnePointMap B) = z^d • 𝟙 _ from hB]
    simp [smul_smul, pow_succ', mul_comm, W]

section ReducedRow

variable {n : ℕ} (i j : Fin n) (hij : i ≠ j)

private theorem heightTranspositionSplit_sum (v : Fin n → ℝ) :
    (∑ k, (heightTranspositionSplit i j hij v).2.val k) = ∑ k, v k := by
  have havg (k : Fin n) :
      (heightTranspositionSplit i j hij v).2.val k =
        (v k + v ((Equiv.swap i j) k)) / 2 := by
    by_cases hki : k = i
    · subst k
      simp [heightTranspositionSplit]
    · by_cases hkj : k = j
      · subst k
        simp [heightTranspositionSplit, hij.symm]
        ring
      · simp [heightTranspositionSplit, hki, hkj, Equiv.swap_apply_of_ne_of_ne]
  simp_rw [havg]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Equiv.sum_comp]
  ring

/-- The fixed hyperplane inside one zero-sum permutation row. -/
def reducedRowTranspositionFixed : Submodule ℝ (heightTranspositionFixed i j) where
  carrier := {v | ∑ k, v.val k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change (∑ k : Fin n, (v.val k + w.val k)) = 0
    rw [Finset.sum_add_distrib, hv, hw, add_zero]
  smul_mem' := by
    intro a v hv
    change (∑ k, a * v.val k) = 0
    rw [← Finset.mul_sum, hv, mul_zero]

/-- The antisymmetric direction is `e_i-e_j`. Averaging the two entries
retains the zero-sum equation and provides the fixed complementary space. -/
def reducedRowTranspositionSplit :
    ReducedValues 2 n ≃ₗ[ℝ] ℝ × reducedRowTranspositionFixed i j where
  toFun v := ((heightTranspositionSplit i j hij (v.val 0)).1,
    ⟨(heightTranspositionSplit i j hij (v.val 0)).2, by
      change (∑ k, (heightTranspositionSplit i j hij (v.val 0)).2.val k) = 0
      rw [heightTranspositionSplit_sum, v.property 0]⟩)
  invFun p := ⟨fun _ => (heightTranspositionSplit i j hij).symm (p.1, p.2.val), by
    intro k
    have hs := heightTranspositionSplit_sum i j hij
      ((heightTranspositionSplit i j hij).symm (p.1, p.2.val))
    rw [LinearEquiv.apply_symm_apply] at hs
    exact hs.symm.trans p.2.property⟩
  left_inv v := by
    apply Subtype.ext
    funext k l
    have hk : k = 0 := by apply Fin.ext; have h := k.isLt; omega
    subst k
    exact congrFun ((heightTranspositionSplit i j hij).symm_apply_apply (v.val 0)) l
  right_inv p := by
    have hp := (heightTranspositionSplit i j hij).apply_symm_apply (p.1, p.2.val)
    apply Prod.ext
    · exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.1) hp
    · apply Subtype.ext
      exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.2) hp
  map_add' v w := by
    have hp := (heightTranspositionSplit i j hij).map_add (v.val 0) (w.val 0)
    apply Prod.ext
    · exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.1) hp
    · apply Subtype.ext
      exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.2) hp
  map_smul' a v := by
    have hp := (heightTranspositionSplit i j hij).map_smul a (v.val 0)
    apply Prod.ext
    · exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.1) hp
    · apply Subtype.ext
      exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.2) hp

theorem reducedRowTranspositionSplit_intertwines (v : ReducedValues 2 n) :
    reducedRowTranspositionSplit i j hij (relabelValues (Equiv.swap i j) v) =
      (-(reducedRowTranspositionSplit i j hij v).1,
        (reducedRowTranspositionSplit i j hij v).2) := by
  have hp := heightTranspositionSplit_intertwines i j hij (v.val 0)
  apply Prod.ext
  · exact congrArg (fun z : ℝ × heightTranspositionFixed i j => z.1) hp
  · apply Subtype.ext
    simpa only [reducedRowTranspositionSplit] using
      congrArg (fun z : ℝ × heightTranspositionFixed i j => z.2) hp

private def reducedRowReflectionSplit (X : Type) [AddCommGroup X] [Module ℝ X] :
    (X × ReducedValues 2 n) ≃ₗ[ℝ] ℝ × (X × reducedRowTranspositionFixed i j) :=
  ((LinearEquiv.refl ℝ X).prodCongr (reducedRowTranspositionSplit i j hij)).trans
    ((LinearEquiv.prodAssoc ℝ X ℝ (reducedRowTranspositionFixed i j)).symm.trans
      (((LinearEquiv.prodComm ℝ X ℝ).prodCongr
        (LinearEquiv.refl ℝ (reducedRowTranspositionFixed i j))).trans
          (LinearEquiv.prodAssoc ℝ ℝ X (reducedRowTranspositionFixed i j))))

include hij in
theorem reducedRowPermutationOnePointMap_swap_top (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    HabsMap R (Module.finrank ℝ (X × ReducedValues 2 n))
      (fiberLinearOnePointMap ((LinearEquiv.refl ℝ X).prodCongr
        (relabelValues (d := 2) (Equiv.swap i j)).toLinearEquiv)) = (-1 : ℤ) • 𝟙 _ := by
  let W := X × reducedRowTranspositionFixed i j
  letI : Module.Free ℝ W := Module.Free.of_divisionRing ℝ W
  let e := reducedRowReflectionSplit i j hij X
  apply fiberLinearOnePointMap_conjugate R _ (-1) (W := ℝ × W)
    ((LinearEquiv.refl ℝ X).prodCongr
      (relabelValues (d := 2) (Equiv.swap i j)).toLinearEquiv)
    ((LinearEquiv.neg ℝ : ℝ ≃ₗ[ℝ] ℝ).prodCongr (LinearEquiv.refl ℝ W)) e
  · intro p
    change ((reducedRowTranspositionSplit i j hij
      (relabelValues (Equiv.swap i j) p.2)).1,
      (p.1, (reducedRowTranspositionSplit i j hij
        (relabelValues (Equiv.swap i j) p.2)).2)) = _
    rw [reducedRowTranspositionSplit_intertwines]
    rfl
  · rw [e.finrank_eq]
    change HabsMap R (Module.finrank ℝ (ℝ × W))
      (scalarProductOnePointReflectionMap W) = (-1 : ℤ) • 𝟙 _
    rw [Module.finrank_prod,Module.finrank_self,Nat.add_comm]
    simpa only [neg_one_zsmul] using scalarProductOnePointReflectionMap_top R W

end ReducedRow

/-- The genuine compactified target action, retaining an arbitrary fixed
vector-space factor. On finite points this is `(x,v) ↦ (x,σ • v)`. -/
def reducedPermutationOnePointMap (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (X × ReducedValues (d+1) n)) ⟶
      TopCat.of (OnePoint (X × ReducedValues (d+1) n)) :=
  fiberLinearOnePointMap ((LinearEquiv.refl ℝ X).prodCongr
    (relabelValues (d := d+1) σ).toLinearEquiv)

@[simp] theorem reducedPermutationOnePointMap_coe (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) (p : X × ReducedValues (d+1) n) :
    reducedPermutationOnePointMap X σ (p : OnePoint (X × ReducedValues (d+1) n)) =
      ((p.1, σ • p.2) : X × ReducedValues (d+1) n) := rfl

@[simp] theorem reducedPermutationOnePointMap_infty (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    reducedPermutationOnePointMap X (d := d) σ ∞ = ∞ := rfl

@[simp] theorem reducedPermutationOnePointMap_one (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (d n : ℕ) :
    reducedPermutationOnePointMap X (d := d) (1 : Equiv.Perm (Fin n)) = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  induction p using OnePoint.rec <;> rfl

theorem reducedPermutationOnePointMap_mul (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {d n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    reducedPermutationOnePointMap X (d := d) (σ*τ) =
      reducedPermutationOnePointMap X (d := d) τ ≫
        reducedPermutationOnePointMap X (d := d) σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  induction p using OnePoint.rec <;> rfl

/-- A transposition reverses one scalar direction in each reduced row. -/
theorem reducedPermutationOnePointMap_swap_top (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (d : ℕ) {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    HabsMap R (Module.finrank ℝ (X × ReducedValues (d+1) n))
      (reducedPermutationOnePointMap X (d := d) (Equiv.swap i j)) =
        (-1 : ℤ)^d • 𝟙 _ := by
  let a := (relabelValues (d := 2) (Equiv.swap i j)).toLinearEquiv
  let e := (LinearEquiv.refl ℝ X).prodCongr (reducedRowsEquiv d n)
  apply fiberLinearOnePointMap_conjugate R _ ((-1 : ℤ)^d)
    ((LinearEquiv.refl ℝ X).prodCongr
      (relabelValues (d := d+1) (Equiv.swap i j)).toLinearEquiv)
    ((LinearEquiv.refl ℝ X).prodCongr (fiberRowsLinear a d)) e (fun _ => rfl)
  rw [e.finrank_eq]
  exact fiberRowsLinearOnePointMap_top R a (-1)
    (fun Y _ _ _ => reducedRowPermutationOnePointMap_swap_top i j hij R Y) d X

/-- The real top singular homology action is the `d`-th power of the
permutation sign. This includes all fixed factors and degenerate dimensions. -/
theorem reducedPermutationOnePointMap_top_finrank (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HabsMap R (Module.finrank ℝ (X × ReducedValues (d+1) n))
      (reducedPermutationOnePointMap X (d := d) σ) =
        (Equiv.Perm.sign σ : ℤ)^d • 𝟙 _ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul σ i j hij ih =>
    rw [reducedPermutationOnePointMap_mul, HabsMap_comp, ih,
      reducedPermutationOnePointMap_swap_top R X d i j hij]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, smul_smul]
    rw [← mul_pow,neg_one_mul]

theorem fiberReducedValues_finrank (d n : ℕ) :
    Module.finrank ℝ (ReducedValues (d+1) n) = d*(n-1) := by
  cases n with
  | zero =>
    rw [Module.finrank_zero_of_subsingleton]
    simp
  | succ n => simpa using finrank_reducedValues (d+1) n

/-- Explicit top degree of `(x,v) ↦ (x,σ • v)` on the actual one-point
compactification of a fixed factor times the reduced permutation target. -/
theorem reducedPermutationOnePointMap_top (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HabsMap R (Module.finrank ℝ X + d*(n-1))
      (reducedPermutationOnePointMap X (d := d) σ) =
        (Equiv.Perm.sign σ : ℤ)^d • 𝟙 _ := by
  have hd : Module.finrank ℝ (X × ReducedValues (d+1) n) =
      Module.finrank ℝ X + d*(n-1) := by
    rw [Module.finrank_prod,fiberReducedValues_finrank]
  rw [← hd]
  exact reducedPermutationOnePointMap_top_finrank R X (d := d) σ

/-- The genuine compactified permutation of ambient sites, with a fixed
factor carried along. -/
def ambientPermutationOnePointMap (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (D : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (X × (Fin n → Space D))) ⟶
      TopCat.of (OnePoint (X × (Fin n → Space D))) :=
  fiberLinearOnePointMap ((LinearEquiv.refl ℝ X).prodCongr (ambientRelabel D σ))

/-- Each of the `D` ambient coordinate rows contributes one copy of the
permutation sign, for the actual top homology map over every ring. -/
theorem ambientPermutationOnePointMap_top_finrank (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (D : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HabsMap R (Module.finrank ℝ (X × (Fin n → Space D)))
      (ambientPermutationOnePointMap X D σ) =
        (Equiv.Perm.sign σ : ℤ)^D • 𝟙 _ := by
  let e := (LinearEquiv.refl ℝ X).prodCongr (ambientRowsEquiv D n)
  apply fiberLinearOnePointMap_conjugate R _ ((Equiv.Perm.sign σ : ℤ)^D)
    ((LinearEquiv.refl ℝ X).prodCongr (ambientRelabel D σ))
    ((LinearEquiv.refl ℝ X).prodCongr (fiberRowsLinear (labelPermutationLinear σ) D))
    e (fun _ => rfl)
  rw [e.finrank_eq]
  apply fiberRowsLinearOnePointMap_top R (labelPermutationLinear σ) (Equiv.Perm.sign σ)
  intro Y _ _ _
  change HabsMap R (Module.finrank ℝ (Y × (Fin n → ℝ)))
    (heightPermutationOnePointMap Y σ) = _
  rw [Module.finrank_prod,Module.finrank_pi,Fintype.card_fin]
  exact heightPermutationOnePointMap_top R Y σ

theorem ambientPermutationOnePointMap_top (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (D : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HabsMap R (Module.finrank ℝ X + n*D) (ambientPermutationOnePointMap X D σ) =
      (Equiv.Perm.sign σ : ℤ)^D • 𝟙 _ := by
  have hd : Module.finrank ℝ (X × (Fin n → Space D)) = Module.finrank ℝ X + n*D := by
    rw [Module.finrank_prod,Module.finrank_pi_fintype]
    simp only [finrank_euclideanSpace_fin,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul]
  rw [← hd]
  exact ambientPermutationOnePointMap_top_finrank R X D σ

/-- Ambient relabeling on its own genuine one-point compactification. -/
def ambientRelabelOnePointMap (D : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (Fin n → Space D)) ⟶
      TopCat.of (OnePoint (Fin n → Space D)) :=
  fiberLinearOnePointMap (ambientRelabel D σ)

/-- The actual ambient permutation has top degree `sign(σ)^D`. -/
theorem ambientRelabelOnePointMap_top (R : Type) [Ring R]
    (D : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HabsMap R (n*D) (ambientRelabelOnePointMap D σ) =
      (Equiv.Perm.sign σ : ℤ)^D • 𝟙 _ := by
  let Z := Fin 0 → ℝ
  let e : (Fin n → Space D) ≃ₗ[ℝ] Z × (Fin n → Space D) :=
    (LinearEquiv.uniqueProd (R := ℝ) (M := Fin n → Space D) (M₂ := Z)).symm
  apply fiberLinearOnePointMap_conjugate R (n*D) ((Equiv.Perm.sign σ : ℤ)^D)
    (ambientRelabel D σ) ((LinearEquiv.refl ℝ Z).prodCongr (ambientRelabel D σ))
    e (fun _ => rfl)
  have h := ambientPermutationOnePointMap_top R Z D σ
  rw [Module.finrank_zero_of_subsingleton,zero_add] at h
  exact h

end NRR.PrimePowerTopology
