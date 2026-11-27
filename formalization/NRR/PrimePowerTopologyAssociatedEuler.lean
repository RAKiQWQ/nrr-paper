import NRR.PrimePowerTopologyAssociatedBundle
import NRR.PrimePowerTopologyTwistedHomotopy

/-!
Actual twisted relative chain maps for the associated configuration bundle.
The target is the cokernel of the punctured-cover inclusion after genuine
orientation-twisted coinvariants.  A zero-free equivariant map makes the
zero-section map zero on homology, by the explicit equivariant singular
prism.  No global Thom isomorphism or nonvanishing statement is assumed.
-/

noncomputable section
open Set Topology CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

abbrev AssociatedCover (d n : ℕ) := Configuration d n × ReducedValues d n
abbrev AssociatedPuncturedCover (d n : ℕ) :=
  {p : AssociatedCover d n // p.2 ≠ 0}

def associatedCoverRelabel {d n : ℕ} (σ : ConfigurationGroup n) :
    TopCat.of (AssociatedCover d n) ⟶ TopCat.of (AssociatedCover d n) :=
  TopCat.ofHom ⟨fun p => σ • p,continuous_const_smul σ⟩

def associatedPuncturedRelabel {d n : ℕ} (σ : ConfigurationGroup n) :
    TopCat.of (AssociatedPuncturedCover d n) ⟶ TopCat.of (AssociatedPuncturedCover d n) :=
  TopCat.ofHom ⟨fun p => ⟨σ • p.val,by
    intro h
    apply p.property
    exact (relabelValues σ).injective (h.trans (relabelValues σ).map_zero.symm)⟩,
    ((continuous_const_smul σ).comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem associatedCoverRelabel_one (d n : ℕ) :
    associatedCoverRelabel (d := d) (1 : ConfigurationGroup n) = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change (1 : ConfigurationGroup n) • p = p
  exact one_smul _ p

@[simp] theorem associatedCoverRelabel_mul {d n : ℕ} (σ τ : ConfigurationGroup n) :
    associatedCoverRelabel (d := d) (σ*τ) =
      associatedCoverRelabel τ ≫ associatedCoverRelabel σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact mul_smul σ τ p

@[simp] theorem associatedPuncturedRelabel_one (d n : ℕ) :
    associatedPuncturedRelabel (d := d) (1 : ConfigurationGroup n) = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact one_smul _ p.val

@[simp] theorem associatedPuncturedRelabel_mul {d n : ℕ} (σ τ : ConfigurationGroup n) :
    associatedPuncturedRelabel (d := d) (σ*τ) =
      associatedPuncturedRelabel τ ≫ associatedPuncturedRelabel σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact mul_smul σ τ p.val

def associatedPuncturedIncl (d n : ℕ) :
    TopCat.of (AssociatedPuncturedCover d n) ⟶ TopCat.of (AssociatedCover d n) :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

theorem associatedPuncturedIncl_equivariant {d n : ℕ} (σ : ConfigurationGroup n) :
    associatedPuncturedRelabel σ ≫ associatedPuncturedIncl d n =
      associatedPuncturedIncl d n ≫ associatedCoverRelabel σ := rfl

def associatedCoverGraph {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    TopCat.of (Configuration d n) ⟶ TopCat.of (AssociatedCover d n) :=
  TopCat.ofHom ⟨fun x => (x,f x),continuous_id.prodMk f.continuous⟩

def associatedCoverZero (d n : ℕ) :
    TopCat.of (Configuration d n) ⟶ TopCat.of (AssociatedCover d n) :=
  associatedCoverGraph (ContinuousMap.const _ 0)

theorem associatedCoverGraph_equivariant {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (σ : ConfigurationGroup n) :
    configurationRelabelMap σ ≫ associatedCoverGraph f =
      associatedCoverGraph f ≫ associatedCoverRelabel σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact Prod.ext rfl (he σ x)

theorem associatedCoverZero_equivariant {d n : ℕ} (σ : ConfigurationGroup n) :
    configurationRelabelMap σ ≫ associatedCoverZero d n =
      associatedCoverZero d n ≫ associatedCoverRelabel σ :=
  associatedCoverGraph_equivariant (ContinuousMap.const _ 0)
    (fun τ _x => (values_smul_zero τ).symm) σ

/-- The graph-to-zero homotopy on the genuine principal cover. -/
def associatedCoverGraphZeroHomotopy {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) :
    (associatedCoverGraph f).hom.Homotopy (associatedCoverZero d n).hom where
  toFun p := (p.2,(1-(p.1 : ℝ)) • f p.2)
  continuous_toFun := continuous_snd.prodMk
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (f.continuous.comp continuous_snd))
  map_zero_left x := by simp [associatedCoverGraph]
  map_one_left x := by simp [associatedCoverZero,associatedCoverGraph]

theorem associatedCoverGraphZeroHomotopy_equivariant {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (σ : ConfigurationGroup n) (t : unitInterval) (x : Configuration d n) :
    associatedCoverGraphZeroHomotopy f (t,(configurationRelabelMap σ).hom x) =
      (associatedCoverRelabel σ).hom (associatedCoverGraphZeroHomotopy f (t,x)) := by
  change (σ • x,(1-(t : ℝ)) • f (σ • x)) =
    (σ • x,σ • ((1-(t : ℝ)) • f x))
  apply Prod.ext
  · rfl
  · exact (congrArg (fun v => (1-(t : ℝ)) • v) (he σ x)).trans
      (values_smul_real_smul σ _ (f x)).symm

def associatedCoverNonzeroGraph {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (hnz : ∀ x, f x ≠ 0) :
    TopCat.of (Configuration d n) ⟶ TopCat.of (AssociatedPuncturedCover d n) :=
  TopCat.ofHom ⟨fun x => ⟨(x,f x),hnz x⟩,
    (continuous_id.prodMk f.continuous).subtype_mk _⟩

theorem associatedCoverNonzeroGraph_equivariant {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) (σ : ConfigurationGroup n) :
    configurationRelabelMap σ ≫ associatedCoverNonzeroGraph f hnz =
      associatedCoverNonzeroGraph f hnz ≫ associatedPuncturedRelabel σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact Prod.ext rfl (he σ x)

@[simp] theorem associatedCoverNonzeroGraph_factor {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (hnz : ∀ x, f x ≠ 0) :
    associatedCoverNonzeroGraph f hnz ≫ associatedPuncturedIncl d n =
      associatedCoverGraph f := rfl

section Twisted

variable (R : Type) [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)

abbrev associatedTwistedSource :=
  twistedChainComplex R χ (Csing R (TopCat.of (Configuration d n)))
    (singularConfigurationRelabel R)

abbrev associatedTwistedCover :=
  twistedChainComplex R χ (Csing R (TopCat.of (AssociatedCover d n)))
    (fun σ => CsingMap R (associatedCoverRelabel σ))

abbrev associatedTwistedPunctured :=
  twistedChainComplex R χ (Csing R (TopCat.of (AssociatedPuncturedCover d n)))
    (fun σ => CsingMap R (associatedPuncturedRelabel σ))

/-- Inclusion of the actual punctured singular chain complex after twisted
coinvariants.  This does not invert the order of the permutation group. -/
def associatedTwistedPuncturedIncl :
    associatedTwistedPunctured R (d := d) χ ⟶ associatedTwistedCover R (d := d) χ :=
  twistedChainMap R χ _ _ _ (CsingMap R (associatedPuncturedIncl d n))
    (CsingMap_equivariant R associatedPuncturedRelabel associatedCoverRelabel
      (associatedPuncturedIncl d n) associatedPuncturedIncl_equivariant)

/-- The genuine twisted relative complex of the cover and its punctured
subspace, defined by an actual chain cokernel. -/
def associatedTwistedRelative : ChainComplex (ModuleCat R) ℕ :=
  cokernel (associatedTwistedPuncturedIncl R (d := d) χ)

def associatedTwistedRelProj :
    associatedTwistedCover R (d := d) χ ⟶ associatedTwistedRelative R (d := d) χ :=
  cokernel.π (associatedTwistedPuncturedIncl R (d := d) χ)

def associatedTwistedZeroChainMap :
    associatedTwistedSource R (d := d) χ ⟶ associatedTwistedCover R (d := d) χ :=
  twistedChainMap R χ _ _ _ (CsingMap R (associatedCoverZero d n))
    (CsingMap_equivariant R configurationRelabelMap associatedCoverRelabel
      (associatedCoverZero d n) associatedCoverZero_equivariant)

def associatedTwistedGraphChainMap
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    associatedTwistedSource R (d := d) χ ⟶ associatedTwistedCover R (d := d) χ :=
  twistedChainMap R χ _ _ _ (CsingMap R (associatedCoverGraph f))
    (CsingMap_equivariant R configurationRelabelMap associatedCoverRelabel
      (associatedCoverGraph f) (associatedCoverGraph_equivariant f he))

def associatedTwistedNonzeroGraphChainMap
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) :
    associatedTwistedSource R (d := d) χ ⟶ associatedTwistedPunctured R (d := d) χ :=
  twistedChainMap R χ _ _ _ (CsingMap R (associatedCoverNonzeroGraph f hnz))
    (CsingMap_equivariant R configurationRelabelMap associatedPuncturedRelabel
      (associatedCoverNonzeroGraph f hnz) (associatedCoverNonzeroGraph_equivariant f he hnz))

/-- Actual equivariant graph homotopy, descended by the singular prism. -/
def associatedTwistedGraphZeroChainHomotopy
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    Homotopy (associatedTwistedGraphChainMap R χ f he)
      (associatedTwistedZeroChainMap R (d := d) χ) :=
  twistedSingularChainHomotopy R χ configurationRelabelMap associatedCoverRelabel
    (associatedCoverGraph_equivariant f he) associatedCoverZero_equivariant
    (associatedCoverGraphZeroHomotopy f) (associatedCoverGraphZeroHomotopy_equivariant f he)

/-- The zero-free factorization holds before taking homology. -/
theorem associatedTwistedNonzeroGraph_factor
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) :
    associatedTwistedNonzeroGraphChainMap R χ f he hnz ≫
        associatedTwistedPuncturedIncl R (d := d) χ = associatedTwistedGraphChainMap R χ f he := by
  unfold associatedTwistedNonzeroGraphChainMap associatedTwistedPuncturedIncl
    associatedTwistedGraphChainMap
  have hπ : Epi (twistedChainProj R χ
      (Csing R (TopCat.of (Configuration d n))) (singularConfigurationRelabel R)) :=
    coequalizer.π_epi
  apply hπ.left_cancellation
  rw [twistedChainProj_map_assoc,twistedChainProj_map,twistedChainProj_map,
    ← Category.assoc,← CsingMap_comp,associatedCoverNonzeroGraph_factor]

/-- The Euler-type zero-section morphism in actual twisted relative homology.
Its nonvanishing requires a separate genuine global comparison. -/
def associatedTwistedZeroRelativeMap (k : ℕ) :
    (associatedTwistedSource R (d := d) χ).homology k ⟶
      (associatedTwistedRelative R (d := d) χ).homology k :=
  HomologicalComplex.homologyMap
    (associatedTwistedZeroChainMap R (d := d) χ ≫ associatedTwistedRelProj R (d := d) χ) k

/-- A nowhere-zero equivariant map annihilates the actual twisted
zero-section relative morphism.  This works in every characteristic,
including primes dividing the order of the acting permutation group. -/
theorem associatedTwistedZeroRelativeMap_eq_zero_of_nonzero (k : ℕ)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) : associatedTwistedZeroRelativeMap R (d := d) χ k = 0 := by
  have hhom := (associatedTwistedGraphZeroChainHomotopy R χ f he).homologyMap_eq k
  unfold associatedTwistedZeroRelativeMap
  rw [HomologicalComplex.homologyMap_comp,← hhom,← HomologicalComplex.homologyMap_comp,
    ← associatedTwistedNonzeroGraph_factor R χ f he hnz,Category.assoc]
  change HomologicalComplex.homologyMap
    (associatedTwistedNonzeroGraphChainMap R χ f he hnz ≫
      associatedTwistedPuncturedIncl R (d := d) χ ≫ cokernel.π (associatedTwistedPuncturedIncl R (d := d) χ)) k = 0
  rw [cokernel.condition,comp_zero,HomologicalComplex.homologyMap_zero]

/-- This theorem exposes the precise nonvanishing target without assuming
that the needed nonvanishing has already been established. -/
theorem equivariant_has_zero_of_associatedTwistedZeroRelativeMap_ne_zero (k : ℕ)
    (h : associatedTwistedZeroRelativeMap R (d := d) χ k ≠ 0)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) : ∃ x, f x = 0 := by
  by_contra hnz
  exact h (associatedTwistedZeroRelativeMap_eq_zero_of_nonzero R χ k f he
    (fun x hx => hnz ⟨x,hx⟩))

end Twisted
end NRR.PrimePowerTopology