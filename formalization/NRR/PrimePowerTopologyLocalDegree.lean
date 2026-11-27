import NRR.PrimePowerTopologyNormalHomology
import NRR.PrimePowerTopologyOrientationKernel
import NRR.SingularHomologyRelMap

/-! Actual relative normal-disk maps for the canonical section.

The normal disk lies in the genuine distinct-site configuration space. Its
boundary lies in the complement of the vertical zero stratum. Applying the
canonical section to this map of pairs gives precisely the ordinary disk
map into its vector space, also on relative singular homology. Thus local
normalization is an equality of actual homology maps, with arbitrary ring
coefficients, rather than a formally assigned local degree.

This file does not assert that the resulting local class survives globally,
or that the homology of a sphere has already been computed.
-/

noncomputable section
open Set Topology Metric CategoryTheory
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

def normalBoundaryIncl (d n : ℕ) [NeZero n] (r : ℝ) :
    TopCat.of (sphere (0 : ReducedValues (d+1) n) r) ⟶
      TopCat.of (closedBall (0 : ReducedValues (d+1) n) r) :=
  TopCat.ofHom ⟨fun v => ⟨v.val,sphere_subset_closedBall v.property⟩,
    continuous_subtype_val.subtype_mk _⟩

instance mono_normalBoundaryIncl (r : ℝ) : Mono (normalBoundaryIncl d n r) := by
  rw [TopCat.mono_iff_injective]
  intro v w he
  apply Subtype.ext
  exact congrArg (fun z : closedBall (0 : ReducedValues (d+1) n) r => z.val) he

def canonicalNonzeroSet (d n : ℕ) [NeZero n] : Set (Configuration (d+1) n) :=
  {x | canonicalSection d n x ≠ 0}

theorem canonicalNonzeroSet_eq_compl_vertical :
    canonicalNonzeroSet d n = (verticalSet d n)ᶜ := by
  ext x
  exact not_congr (canonicalSection_zero_iff x)

def reducedNonzeroSet (d n : ℕ) : Set (ReducedValues (d+1) n) := {v | v ≠ 0}

def canonicalSectionNonzero (d n : ℕ) [NeZero n] :
    TopCat.of (canonicalNonzeroSet d n) ⟶ TopCat.of (reducedNonzeroSet d n) :=
  TopCat.ofHom ⟨fun x => ⟨canonicalSection d n x.val,x.property⟩,
    ((canonicalSection d n).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem canonicalSection_pair_comm :
    subIncl (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) ≫
        TopCat.ofHom (canonicalSection d n) =
      canonicalSectionNonzero d n ≫
        subIncl (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) := rfl

def canonicalSectionRelative (R : Type) [Ring R] (k : ℕ) :
    HrelSet R k (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) ⟶
      HrelSet R k (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) :=
  HrelMap R k _ _ (canonicalSection_pair_comm (d := d) (n := n))

theorem nonzero_of_mem_normalSphere {r : ℝ} (hr : 0 < r)
    (v : sphere (0 : ReducedValues (d+1) n) r) : v.val ≠ 0 := by
  intro hz
  have hn := mem_sphere_zero_iff_norm.mp v.property
  rw [hz,norm_zero] at hn
  exact hr.ne' hn.symm

def standardNormalDisk (d n : ℕ) (r : ℝ) :
    TopCat.of (closedBall (0 : ReducedValues (d+1) n) r) ⟶
      TopCat.of (ReducedValues (d+1) n) :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

def standardNormalSphereNonzero {r : ℝ} (hr : 0 < r) :
    TopCat.of (sphere (0 : ReducedValues (d+1) n) r) ⟶
      TopCat.of (reducedNonzeroSet d n) :=
  TopCat.ofHom ⟨fun v => ⟨v.val,nonzero_of_mem_normalSphere hr v⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem standardNormalDisk_pair_comm {r : ℝ} (hr : 0 < r) :
    normalBoundaryIncl d n r ≫ standardNormalDisk d n r =
      standardNormalSphereNonzero (d := d) (n := n) hr ≫
        subIncl (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) := rfl

def standardNormalDiskRelative (R : Type) [Ring R] (k : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Hrel R k (normalBoundaryIncl d n r) ⟶
      HrelSet R k (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n) :=
  HrelMap R k _ _ (standardNormalDisk_pair_comm (d := d) (n := n) hr)

theorem normalSphereConfiguration_mem_nonzero (u : CanonicalKernel d n)
    {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (v : sphere (0 : ReducedValues (d+1) n) r) :
    normalSphereConfiguration u r (sphere_subset_closedBall.trans small) v ∈
      canonicalNonzeroSet d n := by
  change canonicalSection d n
    (normalSphereConfiguration u r (sphere_subset_closedBall.trans small) v) ≠ 0
  rw [canonicalSection_normalSphereConfiguration]
  exact nonzero_of_mem_normalSphere hr v

def normalSphereConfigurationNonzero (u : CanonicalKernel d n)
    {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    TopCat.of (sphere (0 : ReducedValues (d+1) n) r) ⟶
      TopCat.of (canonicalNonzeroSet d n) :=
  TopCat.ofHom ⟨fun v =>
    ⟨normalSphereConfiguration u r (sphere_subset_closedBall.trans small) v,
      normalSphereConfiguration_mem_nonzero u hr small v⟩,
    (normalSphereConfiguration u r (sphere_subset_closedBall.trans small)).continuous.subtype_mk _⟩

theorem normalDiskConfiguration_pair_comm (u : CanonicalKernel d n)
    {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    normalBoundaryIncl d n r ≫ TopCat.ofHom (normalDiskConfiguration u r small) =
      normalSphereConfigurationNonzero u hr small ≫
        subIncl (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) := rfl

def normalDiskConfigurationRelative (R : Type) [Ring R] (k : ℕ)
    (u : CanonicalKernel d n) {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    Hrel R k (normalBoundaryIncl d n r) ⟶
      HrelSet R k (Y := TopCat.of (Configuration (d+1) n)) (canonicalNonzeroSet d n) :=
  HrelMap R k _ _ (normalDiskConfiguration_pair_comm u hr small)

@[simp] theorem normalDiskConfiguration_comp_section (u : CanonicalKernel d n)
    (r : ℝ)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    TopCat.ofHom (normalDiskConfiguration u r small) ≫ TopCat.ofHom (canonicalSection d n) =
      standardNormalDisk d n r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  exact canonicalLinear_normalSlice u v.val

@[simp] theorem normalSphereConfigurationNonzero_comp_section (u : CanonicalKernel d n)
    {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    normalSphereConfigurationNonzero u hr small ≫ canonicalSectionNonzero d n =
      standardNormalSphereNonzero (d := d) (n := n) hr := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  exact canonicalSection_normalSphereConfiguration u r _ v

/-- Local normalization as an equality of real relative singular-homology
maps. All maps are induced by the displayed geometric maps of pairs. -/
theorem normalDiskConfigurationRelative_comp_section
    (R : Type) [Ring R] (k : ℕ) (u : CanonicalKernel d n)
    {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    normalDiskConfigurationRelative R k u hr small ≫ canonicalSectionRelative R k =
      standardNormalDiskRelative (d := d) (n := n) R k hr := by
  unfold normalDiskConfigurationRelative canonicalSectionRelative standardNormalDiskRelative
  rw [HrelMap_comp]
  congr 1
  · exact normalSphereConfigurationNonzero_comp_section u hr small
  · exact normalDiskConfiguration_comp_section u r small

/-- Any standard normal-disk class whose image in local vector-space
homology is nonzero has a nonzero actual image under the canonical section.
No nonzero sphere generator is postulated by this implication. -/
theorem canonicalSectionRelative_nonzero_of_local_class
    (R : Type) [Ring R] (k : ℕ) (u : CanonicalKernel d n)
    {r : ℝ} (hr : 0 < r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (c : Hrel R k (normalBoundaryIncl d n r))
    (nonzero : standardNormalDiskRelative (d := d) (n := n) R k hr c ≠ 0) :
    canonicalSectionRelative (d := d) (n := n) R k ≠ 0 := by
  intro hz
  apply nonzero
  have he := normalDiskConfigurationRelative_comp_section R k u hr small
  rw [hz,Limits.comp_zero] at he
  rw [← he]
  rfl

end NRR.PrimePowerTopology
