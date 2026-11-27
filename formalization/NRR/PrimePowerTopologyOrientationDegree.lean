import NRR.PrimePowerTopologyLocalDegree

/-! Genuine permutation actions on the local relative homology groups.

The determinant character has already been computed in
`PrimePowerTopologyOrientationKernel`. Here we construct the actual maps of
disk-boundary pairs and punctured target pairs, prove they induce homology
isomorphisms, and identify their naturality with the canonical section.
No numerical degree or nonzero sphere generator is assumed.
-/

noncomputable section
open Set Topology Metric CategoryTheory
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

def homeomorphMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨e,e.continuous⟩

def reducedDiskRelabel (σ : Equiv.Perm (Fin n)) (r : ℝ) :
    closedBall (0 : ReducedValues (d+1) n) r ≃ₜ
      closedBall (0 : ReducedValues (d+1) n) r :=
  (relabelValues (d := d+1) σ).toHomeomorph.subtype (fun v => by
    simp only [mem_closedBall,dist_zero_right]
    change ‖v‖ ≤ r ↔ ‖relabelValues σ v‖ ≤ r
    rw [(relabelValues σ).norm_map])

def reducedSphereRelabel (σ : Equiv.Perm (Fin n)) (r : ℝ) :
    sphere (0 : ReducedValues (d+1) n) r ≃ₜ
      sphere (0 : ReducedValues (d+1) n) r :=
  (relabelValues (d := d+1) σ).toHomeomorph.subtype (fun v => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖v‖ = r ↔ ‖relabelValues σ v‖ = r
    rw [(relabelValues σ).norm_map])

theorem relabelValues_zero_iff (σ : Equiv.Perm (Fin n))
    (v : ReducedValues (d+1) n) : relabelValues σ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (relabelValues σ).injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

def reducedNonzeroRelabel (σ : Equiv.Perm (Fin n)) :
    reducedNonzeroSet d n ≃ₜ reducedNonzeroSet d n :=
  (relabelValues (d := d+1) σ).toHomeomorph.subtype (fun v => by
    exact (not_congr (relabelValues_zero_iff σ v)).symm)

def canonicalNonzeroRelabel (σ : Equiv.Perm (Fin n)) :
    canonicalNonzeroSet d n ≃ₜ canonicalNonzeroSet d n :=
  (relabelConfiguration (d := d+1) σ).subtype (fun x => by
    change canonicalSection d n x ≠ 0 ↔ canonicalSection d n (σ • x) ≠ 0
    rw [canonicalSection_equivariant]
    exact (not_congr (relabelValues_zero_iff σ (canonicalSection d n x))).symm)

theorem reducedDiskRelabel_pair_comm (σ : Equiv.Perm (Fin n)) (r : ℝ) :
    normalBoundaryIncl d n r ≫ homeomorphMap (reducedDiskRelabel (d := d) σ r) =
      homeomorphMap (reducedSphereRelabel (d := d) σ r) ≫
        normalBoundaryIncl d n r := rfl

theorem reducedNonzeroRelabel_pair_comm (σ : Equiv.Perm (Fin n)) :
    subIncl (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) ≫
        homeomorphMap (relabelValues (d := d+1) σ).toHomeomorph =
      homeomorphMap (reducedNonzeroRelabel (d := d) σ) ≫
        subIncl (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) := rfl

theorem canonicalNonzeroRelabel_pair_comm (σ : Equiv.Perm (Fin n)) :
    subIncl (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) ≫
        homeomorphMap (relabelConfiguration (d := d+1) σ) =
      homeomorphMap (canonicalNonzeroRelabel (d := d) σ) ≫
        subIncl (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) := rfl

def reducedDiskRelativeRelabel (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) (r : ℝ) :
    Hrel R k (normalBoundaryIncl d n r) ⟶ Hrel R k (normalBoundaryIncl d n r) :=
  HrelMap R k _ _ (reducedDiskRelabel_pair_comm (d := d) σ r)

def reducedNonzeroRelativeRelabel (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    HrelSet R k (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) ⟶
      HrelSet R k (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) :=
  HrelMap R k _ _ (reducedNonzeroRelabel_pair_comm (d := d) σ)

def canonicalNonzeroRelativeRelabel (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    HrelSet R k (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) ⟶
      HrelSet R k (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) :=
  HrelMap R k _ _ (canonicalNonzeroRelabel_pair_comm (d := d) σ)

theorem isIso_homeomorph_hom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : IsIso (homeomorphMap e) :=
  (TopCat.isIso_iff_isHomeomorph _).mpr e.isHomeomorph

instance isIso_reducedDiskRelativeRelabel (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) (r : ℝ) :
    IsIso (reducedDiskRelativeRelabel (d := d) R k σ r) := by
  letI := isIso_homeomorph_hom (reducedDiskRelabel (d := d) σ r)
  letI := isIso_homeomorph_hom (reducedSphereRelabel (d := d) σ r)
  exact isIso_HrelMap_of_isIso R k _ _ _

instance isIso_reducedNonzeroRelativeRelabel (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    IsIso (reducedNonzeroRelativeRelabel (d := d) R k σ) := by
  letI := isIso_homeomorph_hom (relabelValues (d := d+1) σ).toHomeomorph
  letI := isIso_homeomorph_hom (reducedNonzeroRelabel (d := d) σ)
  exact isIso_HrelMap_of_isIso R k _ _ _

instance isIso_canonicalNonzeroRelativeRelabel (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    IsIso (canonicalNonzeroRelativeRelabel (d := d) R k σ) := by
  letI := isIso_homeomorph_hom (relabelConfiguration (d := d+1) σ)
  letI := isIso_homeomorph_hom (canonicalNonzeroRelabel (d := d) σ)
  exact isIso_HrelMap_of_isIso R k _ _ _

theorem canonicalSection_relabel_comm (σ : Equiv.Perm (Fin n)) :
    homeomorphMap (relabelConfiguration (d := d+1) σ) ≫
        TopCat.ofHom (canonicalSection d n) =
      TopCat.ofHom (canonicalSection d n) ≫
        homeomorphMap (relabelValues (d := d+1) σ).toHomeomorph := by
  apply TopCat.ext
  intro x
  exact canonicalSection_equivariant σ x

theorem canonicalSectionNonzero_relabel_comm (σ : Equiv.Perm (Fin n)) :
    homeomorphMap (canonicalNonzeroRelabel (d := d) σ) ≫
        canonicalSectionNonzero d n =
      canonicalSectionNonzero d n ≫
        homeomorphMap (reducedNonzeroRelabel (d := d) σ) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  exact canonicalSection_equivariant σ x.val

/-- Actual equivariance on relative singular homology, including the
subspace maps; no choice of an orientation generator is needed here. -/
theorem canonicalSectionRelative_relabel_comm (R : Type) [Ring R] (k : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    canonicalNonzeroRelativeRelabel (d := d) R k σ ≫ canonicalSectionRelative R k =
      canonicalSectionRelative R k ≫ reducedNonzeroRelativeRelabel (d := d) R k σ := by
  unfold canonicalNonzeroRelativeRelabel canonicalSectionRelative reducedNonzeroRelativeRelabel
  rw [HrelMap_comp,HrelMap_comp]
  congr 1
  · exact canonicalSectionNonzero_relabel_comm σ
  · exact canonicalSection_relabel_comm σ

/-- Relabeling preserves the radius of every actual normal disk: distinct
sites stay distinct and the normal target action is an isometry. -/
theorem normalFiber_closedBall_relabel (u : CanonicalKernel d n)
    (σ : Equiv.Perm (Fin n)) (r : ℝ)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    closedBall (0 : ReducedValues (d+1) n) r ⊆
      canonicalNormalFiberDomain (canonicalKernelRelabel σ u) := by
  intro v hv
  let w := (relabelValues (d := d+1) σ).symm v
  have hw : w ∈ closedBall (0 : ReducedValues (d+1) n) r := by
    rw [mem_closedBall,dist_zero_right] at hv ⊢
    exact ((relabelValues (d := d+1) σ).symm.norm_map v).le.trans hv
  have hi : Function.Injective (u.val+canonicalLift d n w) := small hw
  have he : (canonicalKernelRelabel σ u).val+canonicalLift d n v =
      ambientRelabel (d+1) σ (u.val+canonicalLift d n w) := by
    rw [map_add,← canonicalLift_relabelValues]
    change ambientRelabel (d+1) σ u.val+canonicalLift d n v =
      ambientRelabel (d+1) σ u.val+
        canonicalLift d n (relabelValues σ ((relabelValues σ).symm v))
    rw [LinearIsometryEquiv.apply_symm_apply]
  change Function.Injective ((canonicalKernelRelabel σ u).val+canonicalLift d n v)
  rw [he]
  exact hi.comp σ.symm.injective

theorem normalDiskConfiguration_relabel_comm (u : CanonicalKernel d n)
    (σ : Equiv.Perm (Fin n)) (r : ℝ)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (small' : closedBall (0 : ReducedValues (d+1) n) r ⊆
      canonicalNormalFiberDomain (canonicalKernelRelabel σ u)) :
    homeomorphMap (reducedDiskRelabel (d := d) σ r) ≫
        TopCat.ofHom (normalDiskConfiguration (canonicalKernelRelabel σ u) r small') =
      TopCat.ofHom (normalDiskConfiguration u r small) ≫
        homeomorphMap (relabelConfiguration (d := d+1) σ) := by
  apply TopCat.ext
  intro v
  apply Subtype.ext
  change ambientRelabel (d+1) σ u.val+canonicalLift d n (relabelValues σ v.val) =
    ambientRelabel (d+1) σ (u.val+canonicalLift d n v.val)
  rw [canonicalLift_relabelValues,map_add]

theorem normalSphereConfigurationNonzero_relabel_comm (u : CanonicalKernel d n)
    (σ : Equiv.Perm (Fin n)) {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (small' : closedBall (0 : ReducedValues (d+1) n) r ⊆
      canonicalNormalFiberDomain (canonicalKernelRelabel σ u)) :
    homeomorphMap (reducedSphereRelabel (d := d) σ r) ≫
        normalSphereConfigurationNonzero (canonicalKernelRelabel σ u) hr small' =
      normalSphereConfigurationNonzero u hr small ≫
        homeomorphMap (canonicalNonzeroRelabel (d := d) σ) := by
  apply TopCat.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  change ambientRelabel (d+1) σ u.val+canonicalLift d n (relabelValues σ v.val) =
    ambientRelabel (d+1) σ (u.val+canonicalLift d n v.val)
  rw [canonicalLift_relabelValues,map_add]

/-- The actual normal class at a relabeled vertical configuration is the
permutation image of the original normal class. This includes the boundary
maps and is valid over arbitrary coefficient rings. -/
theorem normalDiskConfigurationRelative_relabel_comm
    (R : Type) [Ring R] (k : ℕ) (u : CanonicalKernel d n)
    (σ : Equiv.Perm (Fin n)) {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (small' : closedBall (0 : ReducedValues (d+1) n) r ⊆
      canonicalNormalFiberDomain (canonicalKernelRelabel σ u)) :
    reducedDiskRelativeRelabel (d := d) R k σ r ≫
        normalDiskConfigurationRelative R k (canonicalKernelRelabel σ u) hr small' =
      normalDiskConfigurationRelative R k u hr small ≫
        canonicalNonzeroRelativeRelabel (d := d) R k σ := by
  unfold reducedDiskRelativeRelabel normalDiskConfigurationRelative canonicalNonzeroRelativeRelabel
  rw [HrelMap_comp,HrelMap_comp]

end NRR.PrimePowerTopology
