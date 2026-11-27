import NRR.PrimePowerTopologyAssociatedBM
import NRR.PrimePowerTopologyAssociatedBMFundamental
import NRR.PrimePowerTopologyAssociatedLocalThom
import NRR.PrimePowerTopologyCanonical

/-!
The actual BM Euler chain map localizes to the zero set of a section.
All support subspaces, maps of pairs and twisted chain maps are constructed
from the displayed continuous graph, rather than from a formal Euler axiom.
For the canonical graph the finite support is precisely the vertical Fuks
stratum.  A global Thom identification with its BM class remains separate.
-/

noncomputable section
open Set Topology Metric CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- Infinity together with the finite configurations on which f is nonzero. -/
def associatedBMSectionComplement {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) : Set (OnePoint (Configuration d n)) :=
  associatedBMGraph f ⁻¹' associatedBMComplement d n

@[simp] theorem associatedBMSectionComplement_infty {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) :
    (∞ : OnePoint (Configuration d n)) ∈ associatedBMSectionComplement f :=
  associatedBMComplement_infty d n

@[simp] theorem associatedBMSectionComplement_coe_iff {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (x : Configuration d n) :
    (x : OnePoint (Configuration d n)) ∈ associatedBMSectionComplement f ↔ f x ≠ 0 :=
  associatedBMComplement_coe_iff (x,f x)

def associatedBMSectionIncl {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    TopCat.of (associatedBMSectionComplement f) ⟶ TopCat.of (OnePoint (Configuration d n)) :=
  subIncl (Y := TopCat.of (OnePoint (Configuration d n))) (associatedBMSectionComplement f)

instance mono_associatedBMSectionIncl {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    Mono (associatedBMSectionIncl f) := mono_subIncl _

def associatedBMInfinityToSection {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    TopCat.of ({∞} : Set (OnePoint (Configuration d n))) ⟶ TopCat.of (associatedBMSectionComplement f) :=
  TopCat.ofHom (ContinuousMap.const _ ⟨∞,associatedBMSectionComplement_infty f⟩)

theorem associatedBMLocalization_square {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    associatedBMSourceIncl d n ≫ 𝟙 _ = associatedBMInfinityToSection f ≫ associatedBMSectionIncl f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨z,hz⟩
  exact hz

def associatedBMSupportedGraph {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    TopCat.of (associatedBMSectionComplement f) ⟶ TopCat.of (associatedBMComplement d n) :=
  TopCat.ofHom ⟨fun z => ⟨(associatedBMGraph f).hom z.val,z.property⟩,
    ((associatedBMGraph f).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem associatedBMSupportedGraph_square {d n : ℕ} (f : C(Configuration d n,ReducedValues d n)) :
    associatedBMSectionIncl f ≫ associatedBMGraph f =
      associatedBMSupportedGraph f ≫ associatedBMTargetIncl d n := rfl

theorem associatedBMLocalization_comp_supported {d n : ℕ}
    (R : Type) [Ring R] (f : C(Configuration d n,ReducedValues d n)) :
    relComplexMap R (associatedBMSourceIncl d n) (associatedBMSectionIncl f)
        (associatedBMLocalization_square f) ≫
      relComplexMap R (associatedBMSectionIncl f) (associatedBMTargetIncl d n)
        (associatedBMSupportedGraph_square f) =
      relComplexMap R (associatedBMSourceIncl d n) (associatedBMTargetIncl d n)
        (associatedBMGraph_pair_comm f) := by
  rw [relComplexMap_comp]

theorem associatedBMSectionComplement_relabel_iff {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (σ : ConfigurationGroup n) (z : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel σ z ∈ associatedBMSectionComplement f ↔
      z ∈ associatedBMSectionComplement f := by
  have h := congrArg (fun m => m.hom z) (associatedBMGraph_equivariant f he σ)
  change (associatedBMGraph f).hom (compactifiedConfigurationRelabel σ z) =
    associatedBMCoverRelabel σ ((associatedBMGraph f).hom z) at h
  change (associatedBMGraph f).hom (compactifiedConfigurationRelabel σ z) ∈
      associatedBMComplement d n ↔
    (associatedBMGraph f).hom z ∈ associatedBMComplement d n
  rw [h]
  exact associatedBMComplement_relabel_mem_iff σ _

def associatedBMSectionRelabel {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) (σ : ConfigurationGroup n) :
    associatedBMSectionComplement f ≃ₜ associatedBMSectionComplement f :=
  (compactifiedConfigurationRelabel σ).subtype
    (fun z => (associatedBMSectionComplement_relabel_iff f he σ z).symm)

def associatedBMSectionRelabelMap {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) (σ : ConfigurationGroup n) :
    TopCat.of (associatedBMSectionComplement f) ⟶ TopCat.of (associatedBMSectionComplement f) :=
  TopCat.ofHom ⟨associatedBMSectionRelabel f he σ,(associatedBMSectionRelabel f he σ).continuous⟩

theorem associatedBMSectionIncl_equivariant {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) (σ : ConfigurationGroup n) :
    associatedBMSectionIncl f ≫ associatedBMSourceRelabelMap σ =
      associatedBMSectionRelabelMap f he σ ≫ associatedBMSectionIncl f := rfl

section Twisted
variable (R : Type) [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)
  (f : C(Configuration d n,ReducedValues d n))
  (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)

def associatedBMLocalizedAction (σ : ConfigurationGroup n) :
    relComplex R (associatedBMSectionIncl f) ⟶ relComplex R (associatedBMSectionIncl f) :=
  relComplexMap R _ _ (associatedBMSectionIncl_equivariant f he σ)

def associatedBMTwistedLocalized : ChainComplex (ModuleCat R) ℕ :=
  twistedChainComplex R χ (relComplex R (associatedBMSectionIncl f))
    (associatedBMLocalizedAction R f he)

def associatedBMTwistedLocalization :
    associatedBMTwistedSource R (d := d) χ ⟶ associatedBMTwistedLocalized R χ f he :=
  twistedChainMap R χ _ (associatedBMSourceRelativeAction R) (associatedBMLocalizedAction R f he)
    (relComplexMap R _ _ (associatedBMLocalization_square f))
    (relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) associatedBMSourceRelabelMap
      (associatedBMSectionRelabelMap f he) associatedBMSourceRelabelMap
      associatedBMSourceIncl_equivariant (associatedBMSectionIncl_equivariant f he)
      (associatedBMLocalization_square f) (fun _ => by simp))

def associatedBMTwistedSupportedGraph :
    associatedBMTwistedLocalized R χ f he ⟶ associatedBMTwistedTarget R (d := d) χ :=
  twistedChainMap R χ _ (associatedBMLocalizedAction R f he) (associatedBMTargetRelativeAction R)
    (relComplexMap R _ _ (associatedBMSupportedGraph_square f))
    (relativeSingularChainMap_equivariant R _ _ (associatedBMSectionRelabelMap f he)
      associatedBMSourceRelabelMap associatedBMComplementRelabelMap associatedBMCoverRelabelMap
      (associatedBMSectionIncl_equivariant f he) associatedBMTargetIncl_equivariant
      (associatedBMSupportedGraph_square f) (associatedBMGraph_equivariant f he))

/-- Exact localization of the genuine twisted graph map at chain level. -/
theorem associatedBMTwistedLocalization_comp_supported :
    associatedBMTwistedLocalization R χ f he ≫ associatedBMTwistedSupportedGraph R χ f he =
      associatedBMTwistedGraphMap R χ f he := by
  unfold associatedBMTwistedLocalization associatedBMTwistedSupportedGraph associatedBMTwistedGraphMap
  have hπ : Epi (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
      (associatedBMSourceRelativeAction R)) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [twistedChainProj_map_assoc,twistedChainProj_map,twistedChainProj_map,
    ← Category.assoc,associatedBMLocalization_comp_supported]

/-- The actual twisted BM Euler morphism factors through homology supported
on the zero set of any chosen equivariant section. -/
theorem associatedBMTwistedEulerMap_localizes (k : ℕ) :
    associatedBMTwistedEulerMap R (d := d) χ k =
      HomologicalComplex.homologyMap (associatedBMTwistedLocalization R χ f he) k ≫
        HomologicalComplex.homologyMap (associatedBMTwistedSupportedGraph R χ f he) k := by
  rw [← HomologicalComplex.homologyMap_comp,associatedBMTwistedLocalization_comp_supported]
  exact (associatedBMTwistedGraphZeroHomotopy R χ f he).homologyMap_eq k |>.symm

end Twisted

/-- The displayed ambient-collapse fundamental representative after the
actual localization map. No survival or Thom identification is built in. -/
def associatedBMTwistedLocalizedFundamentalClass
    (R : Type) [CommRing R] (d n : ℕ) (χ : ConfigurationGroup n →* Rˣ)
    (hpos : 0 < n*d) (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    (associatedBMTwistedLocalized R χ f he).homology (n*d) :=
  HomologicalComplex.homologyMap (associatedBMTwistedLocalization R χ f he) (n*d)
    (associatedBMTwistedFundamentalClass R d n χ hpos)

/-- The actual Euler image is the supported graph image of the localized
fundamental representative, with arbitrary coefficient character. -/
theorem associatedBMTwistedEulerClass_localizes
    (R : Type) [CommRing R] (d n : ℕ) (χ : ConfigurationGroup n →* Rˣ)
    (hpos : 0 < n*d) (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    associatedBMTwistedEulerClass R d n χ hpos =
      HomologicalComplex.homologyMap (associatedBMTwistedSupportedGraph R χ f he) (n*d)
        (associatedBMTwistedLocalizedFundamentalClass R d n χ hpos f he) := by
  unfold associatedBMTwistedEulerClass associatedBMTwistedLocalizedFundamentalClass
  rw [associatedBMTwistedEulerMap_localizes R χ f he]
  rfl

/-- The ordinary finite cover maps to its genuine one-point compactification. -/
def associatedBMFiniteCover (d n : ℕ) :
    TopCat.of (AssociatedCover d n) ⟶ TopCat.of (OnePoint (AssociatedCover d n)) :=
  TopCat.ofHom ⟨((↑) : AssociatedCover d n → OnePoint (AssociatedCover d n)),
    OnePoint.continuous_coe⟩

def associatedBMFinitePunctured (d n : ℕ) :
    TopCat.of (AssociatedPuncturedCover d n) ⟶ TopCat.of (associatedBMComplement d n) :=
  TopCat.ofHom ⟨fun p => ⟨(p.val : OnePoint (AssociatedCover d n)),
    (associatedBMComplement_coe_iff p.val).mpr p.property⟩,
    (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _⟩

theorem associatedBMFiniteCover_pair_comm (d n : ℕ) :
    associatedPuncturedIncl d n ≫ associatedBMFiniteCover d n =
      associatedBMFinitePunctured d n ≫ associatedBMTargetIncl d n := rfl

/-- Finite relative fiber classes have a canonical map to the BM target.
This map is not declared injective: that would assert global survival. -/
def associatedBMFiniteRelative (R : Type) [Ring R] (k d n : ℕ) :
    Hrel R k (associatedPuncturedIncl d n) ⟶ Hrel R k (associatedBMTargetIncl d n) :=
  HrelMap R k _ _ (associatedBMFiniteCover_pair_comm d n)

section LocalNormalDisk
variable {d n : ℕ} [NeZero n] (u : CanonicalKernel d n) {r : ℝ} (hr : 0 < r)
  (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)

/-- The genuine normal disk in the compactified configuration space. -/
def canonicalBMNormalDisk :
    TopCat.of (closedBall (0 : ReducedValues (d+1) n) r) ⟶
      TopCat.of (OnePoint (Configuration (d+1) n)) :=
  TopCat.ofHom ⟨fun v => (normalDiskConfiguration u r small v :
    OnePoint (Configuration (d+1) n)),
    OnePoint.continuous_coe.comp (normalDiskConfiguration u r small).continuous⟩

/-- Its actual boundary lands in the canonical localization complement. -/
def canonicalBMNormalSphere :
    TopCat.of (sphere (0 : ReducedValues (d+1) n) r) ⟶
      TopCat.of (associatedBMSectionComplement (canonicalSection d n)) :=
  TopCat.ofHom ⟨fun v =>
    ⟨(normalSphereConfiguration u r (sphere_subset_closedBall.trans small) v :
      OnePoint (Configuration (d+1) n)),
      (associatedBMSectionComplement_coe_iff _ _).mpr
        (normalSphereConfiguration_mem_nonzero u hr small v)⟩,
    (OnePoint.continuous_coe.comp
      (normalSphereConfiguration u r (sphere_subset_closedBall.trans small)).continuous).subtype_mk _⟩

theorem canonicalBMNormalDisk_pair_comm :
    normalBoundaryIncl d n r ≫ canonicalBMNormalDisk u small =
      canonicalBMNormalSphere u hr small ≫ associatedBMSectionIncl (canonicalSection d n) := rfl

def canonicalBMNormalDiskRelative (R : Type) [Ring R] (k : ℕ) :
    Hrel R k (normalBoundaryIncl d n r) ⟶
      Hrel R k (associatedBMSectionIncl (canonicalSection d n)) :=
  HrelMap R k _ _ (canonicalBMNormalDisk_pair_comm u hr small)

/-- The canonical local supported graph is exactly the compactification of
the actual normal-disk graph, as maps on genuine relative homology. -/
theorem canonicalBMNormalDiskRelative_comp_supported
    (R : Type) [Ring R] (k : ℕ) :
    canonicalBMNormalDiskRelative u hr small R k ≫
        HrelMap R k _ _ (associatedBMSupportedGraph_square (canonicalSection d n)) =
      associatedNormalGraphRelative hr R k (normalDiskConfiguration u r small) ≫
        associatedBMFiniteRelative R k (d+1) n := by
  unfold canonicalBMNormalDiskRelative associatedNormalGraphRelative associatedBMFiniteRelative
  rw [HrelMap_comp,HrelMap_comp]
  congr 1
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    apply Subtype.ext
    change (((normalSphereConfiguration u r (sphere_subset_closedBall.trans small) v,
      canonicalSection d n (normalSphereConfiguration u r (sphere_subset_closedBall.trans small) v)) :
      AssociatedCover (d+1) n) : OnePoint (AssociatedCover (d+1) n)) = _
    rw [canonicalSection_normalSphereConfiguration]
    rfl
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    change (((normalDiskConfiguration u r small v,
      canonicalSection d n (normalDiskConfiguration u r small v)) : AssociatedCover (d+1) n) :
      OnePoint (AssociatedCover (d+1) n)) = _
    rw [show canonicalSection d n (normalDiskConfiguration u r small v) = v.val from
      canonicalLinear_normalSlice u v.val]
    rfl

/-- Local Thom normalization inside the actual BM localization diagram.
The canonical supported graph is the standard normal disk followed by the
fixed ordered fiber and compactification. This does not assert that a
normal class survives these global maps or the twisted quotient. -/
theorem canonicalBMNormalDiskRelative_eq_standardFiber
    (R : Type) [Ring R] (k : ℕ) :
    canonicalBMNormalDiskRelative u hr small R k ≫
        HrelMap R k _ _ (associatedBMSupportedGraph_square (canonicalSection d n)) =
      standardNormalDiskRelative (d := d) (n := n) R k hr ≫
        associatedCoverFiberRelative R k
          (normalDiskConfiguration u r small (associatedNormalDiskZero hr)) ≫
        associatedBMFiniteRelative R k (d+1) n := by
  rw [canonicalBMNormalDiskRelative_comp_supported,
    associatedNormalGraphRelative_eq_standardFiber,Category.assoc]

/-- The same local normalization for the actual twisted supported graph
used in the Euler localization. Both quotient maps are displayed; no
injectivity or nonvanishing after either quotient is assumed. -/
theorem canonicalBMTwistedNormalDiskRelative_eq_standardFiber
    (R : Type) [CommRing R] (χ : ConfigurationGroup n →* Rˣ) (k : ℕ) :
    canonicalBMNormalDiskRelative u hr small R k ≫
        HomologicalComplex.homologyMap
          (twistedChainProj R χ (relComplex R (associatedBMSectionIncl (canonicalSection d n)))
            (associatedBMLocalizedAction R (canonicalSection d n) canonicalSection_equivariant)) k ≫
        HomologicalComplex.homologyMap
          (associatedBMTwistedSupportedGraph R χ (canonicalSection d n) canonicalSection_equivariant) k =
      standardNormalDiskRelative (d := d) (n := n) R k hr ≫
        associatedCoverFiberRelative R k
          (normalDiskConfiguration u r small (associatedNormalDiskZero hr)) ≫
        associatedBMFiniteRelative R k (d+1) n ≫
        HomologicalComplex.homologyMap
          (twistedChainProj R χ (relComplex R (associatedBMTargetIncl (d+1) n))
            (associatedBMTargetRelativeAction R)) k := by
  unfold associatedBMTwistedSupportedGraph
  rw [← HomologicalComplex.homologyMap_comp,twistedChainProj_map,
    HomologicalComplex.homologyMap_comp]
  change canonicalBMNormalDiskRelative u hr small R k ≫
    HrelMap R k _ _ (associatedBMSupportedGraph_square (canonicalSection d n)) ≫ _ = _
  rw [← Category.assoc,canonicalBMNormalDiskRelative_eq_standardFiber,
    Category.assoc,Category.assoc]

end LocalNormalDisk

/-- For the canonical section the finite localization support is exactly
the genuine vertical Fuks zero stratum. -/
theorem canonicalBMSectionComplement {d n : ℕ} [NeZero n] :
    associatedBMSectionComplement (canonicalSection d n) =
      {∞} ∪ ((↑) : Configuration (d+1) n → OnePoint (Configuration (d+1) n)) '' (verticalSet d n)ᶜ := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
    simp only [associatedBMSectionComplement_coe_iff,mem_union,mem_singleton_iff,
      OnePoint.coe_ne_infty,false_or,OnePoint.coe_injective.mem_set_image,mem_compl_iff]
    exact not_congr (canonicalSection_zero_iff x)

end NRR.PrimePowerTopology
