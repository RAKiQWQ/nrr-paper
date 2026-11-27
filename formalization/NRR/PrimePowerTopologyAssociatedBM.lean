import NRR.PrimePowerTopologyAssociatedCompactification
import NRR.PrimePowerTopologyTwistedPairHomotopy

/-!
Compactified pair maps for the actual associated-bundle zero section.
The source pair is (OnePoint Configuration, infinity); the target pair is
(OnePoint (Configuration × V), complement of the finite zero section).
The compactified graph-to-zero homotopy is an actual equivariant pair
homotopy.  This module supplies the Borel--Moore geometric chain interface;
it does not assert the global Thom comparison or its nonzero Euler class.
-/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- The complement includes infinity and all nonzero finite fiber vectors. -/
def associatedBMComplement (d n : ℕ) : Set (OnePoint (AssociatedCover d n)) :=
  (Set.range (fun x : Configuration d n => (((x,0) : AssociatedCover d n) :
    OnePoint (AssociatedCover d n))))ᶜ

@[simp] theorem associatedBMComplement_infty (d n : ℕ) :
    (∞ : OnePoint (AssociatedCover d n)) ∈ associatedBMComplement d n := by
  rintro ⟨x,hx⟩
  exact OnePoint.coe_ne_infty (x,0) hx

@[simp] theorem associatedBMComplement_coe_iff {d n : ℕ} (p : AssociatedCover d n) :
    (p : OnePoint (AssociatedCover d n)) ∈ associatedBMComplement d n ↔ p.2 ≠ 0 := by
  rcases p with ⟨x,v⟩
  simp only [associatedBMComplement,mem_compl_iff,mem_range,OnePoint.coe_eq_coe,
    Prod.mk.injEq,exists_eq_left',ne_eq,eq_comm]

def associatedBMSourceIncl (d n : ℕ) :
    TopCat.of ({∞} : Set (OnePoint (Configuration d n))) ⟶
      TopCat.of (OnePoint (Configuration d n)) :=
  subIncl (Y := TopCat.of (OnePoint (Configuration d n))) {∞}

def associatedBMTargetIncl (d n : ℕ) :
    TopCat.of (associatedBMComplement d n) ⟶ TopCat.of (OnePoint (AssociatedCover d n)) :=
  subIncl (Y := TopCat.of (OnePoint (AssociatedCover d n))) (associatedBMComplement d n)

instance mono_associatedBMSourceIncl (d n : ℕ) : Mono (associatedBMSourceIncl d n) :=
  mono_subIncl (Y := TopCat.of (OnePoint (Configuration d n))) _
instance mono_associatedBMTargetIncl (d n : ℕ) : Mono (associatedBMTargetIncl d n) :=
  mono_subIncl (Y := TopCat.of (OnePoint (AssociatedCover d n))) _

def associatedBMInfinityMap (d n : ℕ) :
    TopCat.of ({∞} : Set (OnePoint (Configuration d n))) ⟶
      TopCat.of (associatedBMComplement d n) :=
  TopCat.ofHom (ContinuousMap.const _ ⟨∞,associatedBMComplement_infty d n⟩)

def associatedBMGraph {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    TopCat.of (OnePoint (Configuration d n)) ⟶ TopCat.of (OnePoint (AssociatedCover d n)) :=
  TopCat.ofHom (onePointGraph f)

def associatedBMZero (d n : ℕ) :
    TopCat.of (OnePoint (Configuration d n)) ⟶ TopCat.of (OnePoint (AssociatedCover d n)) :=
  associatedBMGraph (ContinuousMap.const _ 0)

theorem associatedBMGraph_pair_comm {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) :
    associatedBMSourceIncl d n ≫ associatedBMGraph f =
      associatedBMInfinityMap d n ≫ associatedBMTargetIncl d n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨z,hz⟩
  have hz' : z = ∞ := hz
  subst z
  rfl

def associatedBMGraphZeroPairHomotopy {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) :
    ContinuousPairHomotopy (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
      (associatedBMGraph_pair_comm f)
      (associatedBMGraph_pair_comm (ContinuousMap.const _ 0)) where
  sub := ContinuousMap.Homotopy.refl (associatedBMInfinityMap d n).hom
  amb := associatedCompactGraphZeroHomotopy f
  compat := by
    rintro t ⟨z,hz⟩
    have hz' : z = ∞ := hz
    subst z
    rfl

/-- A zero-free proper graph factors through the actual complement in the
compactification, including the point at infinity. -/
def associatedBMNonzeroGraph {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (hnz : ∀ x, f x ≠ 0) :
    TopCat.of (OnePoint (Configuration d n)) ⟶ TopCat.of (associatedBMComplement d n) :=
  TopCat.ofHom ⟨fun z => ⟨onePointGraph f z,by
    induction z using OnePoint.rec with
    | infty => exact associatedBMComplement_infty d n
    | coe x => exact (associatedBMComplement_coe_iff (x,f x)).mpr (hnz x)⟩,
    (onePointGraph f).continuous.subtype_mk _⟩

@[simp] theorem associatedBMNonzeroGraph_factor {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (hnz : ∀ x, f x ≠ 0) :
    associatedBMNonzeroGraph f hnz ≫ associatedBMTargetIncl d n = associatedBMGraph f := rfl

/-- The relative graph map is already the zero chain map when f is zero-free. -/
theorem associatedBMGraphRelative_eq_zero_of_nonzero {d n : ℕ}
    (R : Type) [Ring R] (f : C(Configuration d n,ReducedValues d n))
    (hnz : ∀ x, f x ≠ 0) :
    relComplexMap R (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
      (associatedBMGraph_pair_comm f) = 0 := by
  have hπ : Epi (relProj R (associatedBMSourceIncl d n)) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [relProj_comp_relComplexMap,comp_zero,
    ← associatedBMNonzeroGraph_factor f hnz,CsingMap_comp,Category.assoc]
  change CsingMap R (associatedBMNonzeroGraph f hnz) ≫
    CsingMap R (associatedBMTargetIncl d n) ≫ cokernel.π (CsingMap R (associatedBMTargetIncl d n)) = 0
  rw [cokernel.condition,comp_zero]

/-- Proper homotopy proves vanishing of the actual compactified zero-section
relative homology map for every zero-free continuous section. -/
theorem associatedBMZeroRelative_eq_zero_of_nonzero {d n : ℕ}
    (R : Type) [Ring R] (k : ℕ) (f : C(Configuration d n,ReducedValues d n))
    (hnz : ∀ x, f x ≠ 0) :
    HrelMap R k (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
      (associatedBMGraph_pair_comm (ContinuousMap.const _ 0)) = 0 := by
  rw [← HrelMap_eq_of_continuousPairHomotopy R _ _ (associatedBMGraph_pair_comm f)
    (associatedBMGraph_pair_comm (ContinuousMap.const _ 0)) (associatedBMGraphZeroPairHomotopy f) k]
  unfold HrelMap
  rw [associatedBMGraphRelative_eq_zero_of_nonzero R f hnz,HomologicalComplex.homologyMap_zero]

/-- The actual compactified diagonal action on the cover. -/
def associatedBMCoverRelabel {d n : ℕ} (σ : ConfigurationGroup n) :
    OnePoint (AssociatedCover d n) ≃ₜ OnePoint (AssociatedCover d n) :=
  (Homeomorph.smul σ : AssociatedCover d n ≃ₜ AssociatedCover d n).onePointCongr

theorem associatedBMComplement_relabel_mem_iff {d n : ℕ}
    (σ : ConfigurationGroup n) (z : OnePoint (AssociatedCover d n)) :
    associatedBMCoverRelabel σ z ∈ associatedBMComplement d n ↔ z ∈ associatedBMComplement d n := by
  induction z using OnePoint.rec with
  | infty => simp [associatedBMCoverRelabel]
  | coe p =>
    change ((σ • p : AssociatedCover d n) : OnePoint (AssociatedCover d n)) ∈
      associatedBMComplement d n ↔ (p : OnePoint (AssociatedCover d n)) ∈ associatedBMComplement d n
    rw [associatedBMComplement_coe_iff,associatedBMComplement_coe_iff]
    constructor
    · intro h hp
      apply h
      change σ • p.2 = 0
      rw [hp,values_smul_zero]
    · intro h hp
      apply h
      exact (relabelValues σ).injective (hp.trans (relabelValues σ).map_zero.symm)

def associatedBMComplementRelabel {d n : ℕ} (σ : ConfigurationGroup n) :
    associatedBMComplement d n ≃ₜ associatedBMComplement d n :=
  (associatedBMCoverRelabel σ).subtype
    (fun z => (associatedBMComplement_relabel_mem_iff σ z).symm)

def associatedBMSourceRelabelMap {d n : ℕ} (σ : ConfigurationGroup n) :
    TopCat.of (OnePoint (Configuration d n)) ⟶ TopCat.of (OnePoint (Configuration d n)) :=
  TopCat.ofHom ⟨compactifiedConfigurationRelabel σ,(compactifiedConfigurationRelabel σ).continuous⟩

def associatedBMCoverRelabelMap {d n : ℕ} (σ : ConfigurationGroup n) :
    TopCat.of (OnePoint (AssociatedCover d n)) ⟶ TopCat.of (OnePoint (AssociatedCover d n)) :=
  TopCat.ofHom ⟨associatedBMCoverRelabel σ,(associatedBMCoverRelabel σ).continuous⟩

def associatedBMComplementRelabelMap {d n : ℕ} (σ : ConfigurationGroup n) :
    TopCat.of (associatedBMComplement d n) ⟶ TopCat.of (associatedBMComplement d n) :=
  TopCat.ofHom ⟨associatedBMComplementRelabel σ,(associatedBMComplementRelabel σ).continuous⟩

theorem associatedBMSourceIncl_equivariant {d n : ℕ} (σ : ConfigurationGroup n) :
    associatedBMSourceIncl d n ≫ associatedBMSourceRelabelMap σ =
      𝟙 _ ≫ associatedBMSourceIncl d n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨z,hz⟩
  have hz' : z = ∞ := hz
  subst z
  rfl

theorem associatedBMTargetIncl_equivariant {d n : ℕ} (σ : ConfigurationGroup n) :
    associatedBMTargetIncl d n ≫ associatedBMCoverRelabelMap σ =
      associatedBMComplementRelabelMap σ ≫ associatedBMTargetIncl d n := rfl

theorem associatedBMGraph_equivariant {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) (σ : ConfigurationGroup n) :
    associatedBMSourceRelabelMap σ ≫ associatedBMGraph f =
      associatedBMGraph f ≫ associatedBMCoverRelabelMap σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change (((σ • x,f (σ • x)) : AssociatedCover d n) : OnePoint (AssociatedCover d n)) =
      (((σ • x,σ • f x) : AssociatedCover d n) : OnePoint (AssociatedCover d n))
    rw [he]

theorem associatedBMGraphZeroPairHomotopy_equivariant {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (σ : ConfigurationGroup n) (t : unitInterval) (z : OnePoint (Configuration d n)) :
    (associatedBMGraphZeroPairHomotopy f).amb (t,(associatedBMSourceRelabelMap σ).hom z) =
      (associatedBMCoverRelabelMap σ).hom ((associatedBMGraphZeroPairHomotopy f).amb (t,z)) := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change ((((σ • x,(1-(t : ℝ)) • f (σ • x)) : AssociatedCover d n)) :
      OnePoint (AssociatedCover d n)) =
      ((((σ • x,σ • ((1-(t : ℝ)) • f x)) : AssociatedCover d n)) :
      OnePoint (AssociatedCover d n))
    rw [he,values_smul_real_smul]


section TwistedBM
variable (R : Type) [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)

def associatedBMSourceRelativeAction (σ : ConfigurationGroup n) :
    relComplex R (associatedBMSourceIncl d n) ⟶ relComplex R (associatedBMSourceIncl d n) :=
  relComplexMap R _ _ (associatedBMSourceIncl_equivariant σ)

def associatedBMTargetRelativeAction (σ : ConfigurationGroup n) :
    relComplex R (associatedBMTargetIncl d n) ⟶ relComplex R (associatedBMTargetIncl d n) :=
  relComplexMap R _ _ (associatedBMTargetIncl_equivariant σ)

/-- Actual twisted BM source chains: infinity is quotiented before the
genuine permutation coinvariants. -/
def associatedBMTwistedSource : ChainComplex (ModuleCat R) ℕ :=
  twistedChainComplex R χ (relComplex R (associatedBMSourceIncl d n))
    (associatedBMSourceRelativeAction R)

/-- Actual twisted relative target chains of the compactified zero locus. -/
def associatedBMTwistedTarget : ChainComplex (ModuleCat R) ℕ :=
  twistedChainComplex R χ (relComplex R (associatedBMTargetIncl d n))
    (associatedBMTargetRelativeAction R)

theorem associatedBMRelativeGraph_equivariant
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (σ : ConfigurationGroup n) :
    associatedBMSourceRelativeAction R σ ≫
        relComplexMap R (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
          (associatedBMGraph_pair_comm f) =
      relComplexMap R (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
          (associatedBMGraph_pair_comm f) ≫ associatedBMTargetRelativeAction R σ :=
  relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) associatedBMSourceRelabelMap
    associatedBMComplementRelabelMap associatedBMCoverRelabelMap
    associatedBMSourceIncl_equivariant associatedBMTargetIncl_equivariant
    (associatedBMGraph_pair_comm f) (associatedBMGraph_equivariant f he) σ

def associatedBMTwistedGraphMap
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    associatedBMTwistedSource R (d := d) χ ⟶ associatedBMTwistedTarget R (d := d) χ :=
  twistedChainMap R χ _ (associatedBMSourceRelativeAction R) (associatedBMTargetRelativeAction R)
    (relComplexMap R (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
      (associatedBMGraph_pair_comm f)) (associatedBMRelativeGraph_equivariant R f he)

def associatedBMTwistedZeroMap :
    associatedBMTwistedSource R (d := d) χ ⟶ associatedBMTwistedTarget R (d := d) χ :=
  associatedBMTwistedGraphMap R χ (ContinuousMap.const _ 0)
    (fun σ _x => (values_smul_zero σ).symm)

/-- The compactified equivariant pair prism descends through both genuine
quotients.  This is the BM graph-to-zero chain homotopy. -/
def associatedBMTwistedGraphZeroHomotopy
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    Homotopy (associatedBMTwistedGraphMap R χ f he) (associatedBMTwistedZeroMap R (d := d) χ) :=
  twistedRelativeSingularChainHomotopy R χ (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
    (fun _ => 𝟙 _) associatedBMSourceRelabelMap
    associatedBMComplementRelabelMap associatedBMCoverRelabelMap
    associatedBMSourceIncl_equivariant associatedBMTargetIncl_equivariant
    (associatedBMGraph_pair_comm f) (associatedBMGraph_pair_comm (ContinuousMap.const _ 0))
    (associatedBMGraphZeroPairHomotopy f) (associatedBMGraph_equivariant f he)
    (associatedBMGraph_equivariant (ContinuousMap.const _ 0)
      (fun σ _x => (values_smul_zero σ).symm))
    (associatedBMGraphZeroPairHomotopy_equivariant f he)

/-- The graph map vanishes even at the twisted relative chain level when
its finite vectors are all nonzero. -/
theorem associatedBMTwistedGraphMap_eq_zero_of_nonzero
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) : associatedBMTwistedGraphMap R χ f he = 0 := by
  unfold associatedBMTwistedGraphMap
  have hπ : Epi (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
      (associatedBMSourceRelativeAction R)) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [twistedChainProj_map,associatedBMGraphRelative_eq_zero_of_nonzero R f hnz,
    zero_comp,comp_zero]

/-- The actual BM zero-section relative homology morphism. Its
nonvanishing is exactly the global Euler/Thom comparison still to compute. -/
def associatedBMTwistedEulerMap (k : ℕ) :
    (associatedBMTwistedSource R (d := d) χ).homology k ⟶
      (associatedBMTwistedTarget R (d := d) χ).homology k :=
  HomologicalComplex.homologyMap (associatedBMTwistedZeroMap R (d := d) χ) k

/-- Every zero-free equivariant map annihilates the actual BM Euler-type
morphism, proved using the explicit proper equivariant pair homotopy. -/
theorem associatedBMTwistedEulerMap_eq_zero_of_nonzero (k : ℕ)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) : associatedBMTwistedEulerMap R (d := d) χ k = 0 := by
  have hh := (associatedBMTwistedGraphZeroHomotopy R χ f he).homologyMap_eq k
  unfold associatedBMTwistedEulerMap
  rw [← hh,associatedBMTwistedGraphMap_eq_zero_of_nonzero R χ f he hnz,
    HomologicalComplex.homologyMap_zero]

theorem equivariant_has_zero_of_associatedBMTwistedEulerMap_ne_zero (k : ℕ)
    (h : associatedBMTwistedEulerMap R (d := d) χ k ≠ 0)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) : ∃ x, f x = 0 := by
  by_contra hnz
  exact h (associatedBMTwistedEulerMap_eq_zero_of_nonzero R χ k f he
    (fun x hx => hnz ⟨x,hx⟩))

end TwistedBM
end NRR.PrimePowerTopology