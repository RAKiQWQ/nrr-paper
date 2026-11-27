import NRR.PrimePowerTopologyTwistedChains

/-! Actual relative singular chain complexes for the compactified Fuks
filtration, with orientation-twisted permutation coinvariants. All maps
are induced by the genuine compactified configuration-space action. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

def compactifiedConfigurationRelabel {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OnePoint (Configuration d n) ≃ₜ OnePoint (Configuration d n) :=
  (relabelConfiguration σ).onePointCongr

theorem compactifiedConfigurationRelabel_fix {d n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : OnePoint (Configuration d n))
    (fixed : compactifiedConfigurationRelabel σ x = x) : σ = 1 ∨ x = ∞ := by
  induction x using OnePoint.rec with
  | infty => exact Or.inr rfl
  | coe x =>
    left
    apply configuration_action_free σ x
    exact Option.some.inj fixed

/-- After deleting the constant-at-infinity simplex, the genuine action
on singular simplex labels is free. This is the basis fact needed for
twisted relative-chain exactness in prime characteristic. -/
theorem nonconstantInfinityMap_action_free {d n : ℕ} {A : Type*}
    (σ : Equiv.Perm (Fin n)) (s : A → OnePoint (Configuration d n))
    (nonconstant : ∃ a,s a ≠ ∞)
    (fixed : ∀ a,compactifiedConfigurationRelabel σ (s a) = s a) : σ = 1 := by
  obtain ⟨a,ha⟩ := nonconstant
  exact (compactifiedConfigurationRelabel_fix σ (s a) (fixed a)).resolve_right ha

theorem compactifiedFuksLevel_relabel_mem_iff {d n k : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) (x : OnePoint (Configuration (d+1) n)) :
    compactifiedConfigurationRelabel σ x ∈ compactifiedFuksLevel d n k ↔
      x ∈ compactifiedFuksLevel d n k := by
  induction x using OnePoint.rec with
  | infty => simp [compactifiedConfigurationRelabel,compactifiedFuksLevel]
  | coe x =>
    simpa only [compactifiedConfigurationRelabel,Homeomorph.onePointCongr_apply,
      OnePoint.map_some,compactifiedFuksLevel,mem_union,mem_singleton_iff,
      OnePoint.coe_ne_infty,false_or,OnePoint.coe_injective.mem_set_image] using
      smul_mem_fuksLevel_iff (k := k) σ x

def compactifiedFuksRelabel {d n k : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    compactifiedFuksLevel d n k ≃ₜ compactifiedFuksLevel d n k :=
  (compactifiedConfigurationRelabel σ).subtype
    (fun x => (compactifiedFuksLevel_relabel_mem_iff σ x).symm)

def compactifiedFuksRelabelMap {d n k : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    TopCat.of (compactifiedFuksLevel d n k) ⟶ TopCat.of (compactifiedFuksLevel d n k) :=
  TopCat.ofHom ⟨compactifiedFuksRelabel σ,(compactifiedFuksRelabel σ).continuous⟩

def compactifiedFuksInclusion {d n k l : ℕ} (hkl : k ≤ l) :
    TopCat.of (compactifiedFuksLevel d n k) ⟶ TopCat.of (compactifiedFuksLevel d n l) :=
  TopCat.ofHom ⟨fun x => ⟨x.val,compactifiedFuksLevel_mono d n hkl x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

instance mono_compactifiedFuksInclusion {d n k l : ℕ} (hkl : k ≤ l) :
    Mono (compactifiedFuksInclusion (d := d) (n := n) hkl) := by
  apply (TopCat.mono_iff_injective _).mpr
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : compactifiedFuksLevel d n l => z.val) he

theorem compactifiedFuksInclusion_equivariant {d n k l : ℕ} [NeZero n]
    (hkl : k ≤ l) (σ : Equiv.Perm (Fin n)) :
    compactifiedFuksInclusion (d := d) (n := n) hkl ≫ compactifiedFuksRelabelMap σ =
      compactifiedFuksRelabelMap σ ≫ compactifiedFuksInclusion hkl := by
  ext x
  rfl

theorem compactifiedFuksInclusion_square {d n k l k' l' : ℕ}
    (hkl : k ≤ l) (hkl' : k' ≤ l') (hk : k ≤ k') (hl : l ≤ l') :
    compactifiedFuksInclusion (d := d) (n := n) hkl ≫ compactifiedFuksInclusion hl =
      compactifiedFuksInclusion hk ≫ compactifiedFuksInclusion hkl' := by
  ext x
  rfl

variable (R : Type) [CommRing R]

def fuksRelativeComplex {d n k l : ℕ} (hkl : k ≤ l) : ChainComplex (ModuleCat R) ℕ :=
  relComplex R (compactifiedFuksInclusion (d := d) (n := n) hkl)

def fuksRelativeRelabel {d n k l : ℕ} [NeZero n]
    (hkl : k ≤ l) (σ : Equiv.Perm (Fin n)) :
    fuksRelativeComplex R (d := d) (n := n) hkl ⟶
      fuksRelativeComplex R (d := d) (n := n) hkl :=
  relComplexMap R (compactifiedFuksInclusion hkl) (compactifiedFuksInclusion hkl)
    (compactifiedFuksInclusion_equivariant hkl σ)

def fuksRelativeMap {d n k l k' l' : ℕ} (hkl : k ≤ l) (hkl' : k' ≤ l')
    (hk : k ≤ k') (hl : l ≤ l') :
    fuksRelativeComplex R (d := d) (n := n) hkl ⟶
      fuksRelativeComplex R (d := d) (n := n) hkl' :=
  relComplexMap R (compactifiedFuksInclusion hkl) (compactifiedFuksInclusion hkl')
    (compactifiedFuksInclusion_square hkl hkl' hk hl)

theorem fuksRelativeMap_equivariant {d n k l k' l' : ℕ} [NeZero n]
    (hkl : k ≤ l) (hkl' : k' ≤ l') (hk : k ≤ k') (hl : l ≤ l')
    (σ : Equiv.Perm (Fin n)) :
    fuksRelativeRelabel R (d := d) (n := n) hkl σ ≫ fuksRelativeMap R hkl hkl' hk hl =
      fuksRelativeMap R hkl hkl' hk hl ≫ fuksRelativeRelabel R hkl' σ := by
  have hepi : Epi (relProj R (compactifiedFuksInclusion (d := d) (n := n) hkl)) :=
    coequalizer.π_epi
  apply hepi.left_cancellation
  simp only [fuksRelativeRelabel,fuksRelativeMap,relProj_comp_relComplexMap_assoc,
    relProj_comp_relComplexMap]
  rw [← Category.assoc,← CsingMap_comp,← compactifiedFuksInclusion_equivariant,
    CsingMap_comp,Category.assoc]

/-- These are the genuine twisted relative complexes to which a cellular
boundary calculation must be compared. No comparison theorem is built into
their definition. -/
def twistedFuksRelativeComplex {d n k l : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hkl : k ≤ l) :
    ChainComplex (ModuleCat R) ℕ :=
  twistedChainComplex R χ (fuksRelativeComplex R (d := d) hkl) (fuksRelativeRelabel R hkl)

def twistedFuksRelativeProj {d n k l : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hkl : k ≤ l) :
    fuksRelativeComplex R (d := d) (n := n) hkl ⟶
      twistedFuksRelativeComplex R (d := d) χ hkl :=
  twistedChainProj R χ (fuksRelativeComplex R hkl) (fuksRelativeRelabel R hkl)

theorem fuksRelativeRelabel_proj {d n k l : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hkl : k ≤ l) (σ : Equiv.Perm (Fin n)) :
    fuksRelativeRelabel R (d := d) hkl σ ≫ twistedFuksRelativeProj R χ hkl =
      (χ σ : R) • twistedFuksRelativeProj R χ hkl :=
  chainAction_proj R χ (fuksRelativeComplex R hkl) (fuksRelativeRelabel R hkl) σ

def twistedFuksRelativeMap {d n k l k' l' : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hkl : k ≤ l) (hkl' : k' ≤ l')
    (hk : k ≤ k') (hl : l ≤ l') :
    twistedFuksRelativeComplex R (d := d) χ hkl ⟶
      twistedFuksRelativeComplex R (d := d) χ hkl' :=
  twistedChainMap R χ (fuksRelativeComplex R (d := d) hkl)
    (fuksRelativeRelabel R hkl) (fuksRelativeRelabel R hkl')
    (fuksRelativeMap R hkl hkl' hk hl) (fuksRelativeMap_equivariant R hkl hkl' hk hl)

@[reassoc (attr := simp)] theorem twistedFuksRelativeProj_map
    {d n k l k' l' : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hkl : k ≤ l) (hkl' : k' ≤ l')
    (hk : k ≤ k') (hl : l ≤ l') :
    twistedFuksRelativeProj R (d := d) χ hkl ≫ twistedFuksRelativeMap R χ hkl hkl' hk hl =
      fuksRelativeMap R hkl hkl' hk hl ≫ twistedFuksRelativeProj R χ hkl' :=
  twistedChainProj_map R χ (fuksRelativeComplex R hkl) (fuksRelativeRelabel R hkl)
    (fuksRelativeRelabel R hkl') (fuksRelativeMap R hkl hkl' hk hl)
    (fuksRelativeMap_equivariant R hkl hkl' hk hl)

theorem compactifiedFuksLevel_eq_infty_of_lt {d n k : ℕ} [NeZero n] (hk : k < d) :
    compactifiedFuksLevel d n k = {∞} := by
  rw [compactifiedFuksLevel,fuksLevel_eq_empty_of_lt hk,image_empty,union_empty]

end NRR.PrimePowerTopology
