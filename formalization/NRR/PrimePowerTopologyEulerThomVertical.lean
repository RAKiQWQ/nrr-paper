import NRR.PrimePowerTopologyEulerLocalizationBridge

/-! A global, explicit normal neighborhood of the lowest vertical stratum.
Distinct tangent heights remain distinct after every horizontal normal
displacement, so this neighborhood contains the entire normal vector space.
The global Euler endpoint factors through its actual compactified collapse.
No homology survival or global Thom isomorphism is assumed. -/

noncomputable section
open Set Topology Filter CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

/-- Every normal displacement of a genuine vertical configuration is
still a configuration: it leaves all the distinct heights unchanged. -/
theorem canonicalKernel_add_lift_injective (u : CanonicalKernel d n)
    (hu : Function.Injective u.val) (v : ReducedValues (d+1) n) :
    Function.Injective (u.val + canonicalLift d n v) := by
  have hv : (⟨u.val,hu⟩ : Configuration (d+1) n) ∈ verticalSet d n :=
    (canonicalSection_zero_iff _).mp u.property
  intro i j he
  apply hu
  apply (horizontalHeight d).injective
  refine Prod.ext (hv i j) ?_
  have hh := congrArg (fun z => (horizontalHeight d z).2) he
  simpa [Pi.add_apply,map_add,canonicalLift] using hh

def canonicalEulerThomOpen (d n : ℕ) [NeZero n] : Set (Configuration (d+1) n) :=
  {x | Function.Injective (canonicalNormalCoordinates d n x.val).1.val}

theorem isOpen_canonicalEulerThomOpen : IsOpen (canonicalEulerThomOpen d n) :=
  (isOpen_injectiveSites (d+1) n).preimage
    (continuous_subtype_val.comp
      (continuous_fst.comp ((canonicalNormalCoordinates d n).continuous.comp continuous_subtype_val)))

/-- The full actual normal bundle of the lowest vertical stratum is an
open subset of configuration space, in the canonical global coordinates. -/
def canonicalEulerThomCoordinates :
    canonicalEulerThomOpen d n ≃ₜ VerticalAssociated d n where
  toFun x := (⟨(canonicalNormalCoordinates d n x.val.val).1,x.property⟩,
    (canonicalNormalCoordinates d n x.val.val).2)
  invFun p :=
    ⟨⟨(canonicalNormalCoordinates d n).symm (p.1.val,p.2),
      canonicalKernel_add_lift_injective p.1.val p.1.property p.2⟩,by
        change Function.Injective
          (canonicalNormalCoordinates d n ((canonicalNormalCoordinates d n).symm
            (p.1.val,p.2))).1.val
        rw [ContinuousLinearEquiv.apply_symm_apply]
        exact p.1.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (canonicalNormalCoordinates d n).symm_apply_apply x.val.val
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change (canonicalNormalCoordinates d n
        ((canonicalNormalCoordinates d n).symm (p.1.val,p.2))).1 = p.1.val
      exact congrArg Prod.fst ((canonicalNormalCoordinates d n).apply_symm_apply (p.1.val,p.2))
    · change (canonicalNormalCoordinates d n
        ((canonicalNormalCoordinates d n).symm (p.1.val,p.2))).2 = p.2
      exact congrArg Prod.snd ((canonicalNormalCoordinates d n).apply_symm_apply (p.1.val,p.2))
  continuous_toFun := by
    have h : Continuous (fun x : canonicalEulerThomOpen d n =>
        canonicalNormalCoordinates d n x.val.val) := (canonicalNormalCoordinates d n).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)
    exact (h.fst.subtype_mk _).prodMk h.snd
  continuous_invFun := by
    have h : Continuous (fun p : VerticalAssociated d n =>
        (canonicalNormalCoordinates d n).symm (p.1.val,p.2)) :=
      (canonicalNormalCoordinates d n).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact (h.subtype_mk _).subtype_mk _

/-- Collapse configurations without distinct tangent heights, and express
the surviving neighborhood in genuine vertical/normal coordinates. -/
def canonicalEulerThomCollapse :
    C(OnePoint (Configuration (d+1) n),OnePoint (VerticalAssociated d n)) :=
  ⟨fun z => (canonicalEulerThomCoordinates (d := d) (n := n)).onePointCongr
      (onePointOpenCollapse (canonicalEulerThomOpen d n) z),
    (canonicalEulerThomCoordinates (d := d) (n := n)).onePointCongr.continuous.comp
      (continuous_onePointOpenCollapse _ isOpen_canonicalEulerThomOpen)⟩

@[simp] theorem canonicalEulerThomCollapse_infty :
    canonicalEulerThomCollapse (d := d) (n := n) ∞ = ∞ := rfl

@[simp] theorem canonicalEulerThomCollapse_of_mem (x : Configuration (d+1) n)
    (hx : x ∈ canonicalEulerThomOpen d n) :
    canonicalEulerThomCollapse (d := d) (n := n) (x : OnePoint (Configuration (d+1) n)) =
      ((⟨(canonicalNormalCoordinates d n x.val).1,hx⟩,
        canonicalLinear d n x.val) : VerticalAssociated d n) := by
  change (canonicalEulerThomCoordinates (d := d) (n := n)).onePointCongr
    (openCollapse (canonicalEulerThomOpen d n) x) = _
  rw [openCollapse_of_mem _ hx]
  rfl

@[simp] theorem canonicalEulerThomCollapse_of_not_mem (x : Configuration (d+1) n)
    (hx : x ∉ canonicalEulerThomOpen d n) :
    canonicalEulerThomCollapse (d := d) (n := n) (x : OnePoint (Configuration (d+1) n)) = ∞ := by
  change (canonicalEulerThomCoordinates (d := d) (n := n)).onePointCongr
    (openCollapse (canonicalEulerThomOpen d n) x) = ∞
  rw [openCollapse_of_not_mem _ hx]
  rfl

def canonicalEulerThomInclude (p : VerticalAssociated d n) : AssociatedCover (d+1) n :=
  (⟨p.1.val.val,p.1.property⟩,p.2)

def canonicalEulerThomZeroCoordinates :
    VerticalAssociated d n ≃ₜ
      {p : AssociatedCover (d+1) n // canonicalSection d n p.1 = 0} where
  toFun p := ⟨canonicalEulerThomInclude p,p.1.val.property⟩
  invFun p := (⟨⟨p.val.1.val,p.property⟩,p.val.1.property⟩,p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
      continuous_snd).subtype_mk _
  continuous_invFun :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)

theorem isClosedEmbedding_canonicalEulerThomInclude :
    IsClosedEmbedding (canonicalEulerThomInclude (d := d) (n := n)) :=
  (isClosed_eq ((canonicalSection d n).continuous.comp continuous_fst) continuous_const).isClosedEmbedding_subtypeVal.comp
    canonicalEulerThomZeroCoordinates.isClosedEmbedding

/-- Proper inclusion of the vertical normal model into the actual total
space. Closedness of the genuine zero locus supplies properness. -/
def canonicalEulerThomIncludeCompact :
    C(OnePoint (VerticalAssociated d n),OnePoint (AssociatedCover (d+1) n)) :=
  ⟨OnePoint.map canonicalEulerThomInclude,
    OnePoint.continuous_map isClosedEmbedding_canonicalEulerThomInclude.continuous (by
      simpa only [coclosedCompact_eq_cocompact] using
        isClosedEmbedding_canonicalEulerThomInclude.tendsto_cocompact)⟩

@[simp] theorem canonicalEulerThomIncludeCompact_infty :
    canonicalEulerThomIncludeCompact (d := d) (n := n) ∞ = ∞ := rfl

@[simp] theorem canonicalEulerThomIncludeCompact_coe (p : VerticalAssociated d n) :
    canonicalEulerThomIncludeCompact (d := d) (n := n) (p : OnePoint (VerticalAssociated d n)) =
      (canonicalEulerThomInclude p : OnePoint (AssociatedCover (d+1) n)) := rfl

theorem canonicalEulerSlide_one_eq_tangent (x : EulerAmbient d n) :
    canonicalEulerSlide (d := d) (n := n) 1 x =
      (canonicalNormalCoordinates d n x).1.val := by
  simp [canonicalEulerSlide,canonicalNormalCoordinates,canonicalNormalLinearEquiv]

/-- The global vertical endpoint is exactly the genuine open collapse
followed by proper inclusion of the full vertical normal model. -/
theorem canonicalEulerVertical_eq_thom_factor :
    canonicalEulerVerticalMap (d := d) (n := n) =
      TopCat.ofHom canonicalEulerThomCollapse ≫ TopCat.ofHom canonicalEulerThomIncludeCompact := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change associatedAmbientSlideMap (d := d) (n := n) (1,x.val) =
      canonicalEulerThomIncludeCompact (canonicalEulerThomCollapse (x : OnePoint (Configuration (d+1) n)))
    by_cases hx : x ∈ canonicalEulerThomOpen d n
    · have hslide : Function.Injective (canonicalEulerSlide (d := d) (n := n) 1 x.val) := by
        rw [canonicalEulerSlide_one_eq_tangent]
        exact hx
      rw [associatedAmbientSlideMap_of_mem 1 x.val hslide,
        canonicalEulerThomCollapse_of_mem x hx,canonicalEulerThomIncludeCompact_coe]
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        exact canonicalEulerSlide_one_eq_tangent x.val
      · rfl
    · have hslide : ¬ Function.Injective (canonicalEulerSlide (d := d) (n := n) 1 x.val) := by
        rwa [canonicalEulerSlide_one_eq_tangent]
      rw [canonicalEulerThomCollapse_of_not_mem x hx,canonicalEulerThomIncludeCompact_infty]
      exact associatedAmbientCollapse_of_not_mem (d := d) (n := n) _ hslide

def canonicalEulerThomComplement (d n : ℕ) [NeZero n] : Set (OnePoint (VerticalAssociated d n)) :=
  canonicalEulerThomIncludeCompact ⁻¹' associatedBMComplement (d+1) n

@[simp] theorem canonicalEulerThomComplement_infty :
    (∞ : OnePoint (VerticalAssociated d n)) ∈ canonicalEulerThomComplement d n :=
  associatedBMComplement_infty (d+1) n

@[simp] theorem canonicalEulerThomComplement_coe_iff (p : VerticalAssociated d n) :
    (p : OnePoint (VerticalAssociated d n)) ∈ canonicalEulerThomComplement d n ↔ p.2 ≠ 0 :=
  associatedBMComplement_coe_iff (canonicalEulerThomInclude p)

def canonicalEulerThomIncl (d n : ℕ) [NeZero n] :
    TopCat.of (canonicalEulerThomComplement d n) ⟶ TopCat.of (OnePoint (VerticalAssociated d n)) :=
  subIncl (Y := TopCat.of (OnePoint (VerticalAssociated d n))) (canonicalEulerThomComplement d n)

instance mono_canonicalEulerThomIncl : Mono (canonicalEulerThomIncl d n) := mono_subIncl _

def canonicalEulerThomComplementInclude :
    TopCat.of (canonicalEulerThomComplement d n) ⟶ TopCat.of (associatedBMComplement (d+1) n) :=
  TopCat.ofHom ⟨fun z => ⟨canonicalEulerThomIncludeCompact z.val,z.property⟩,
    (canonicalEulerThomIncludeCompact.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem canonicalEulerThomInclude_pair_comm :
    canonicalEulerThomIncl d n ≫ TopCat.ofHom canonicalEulerThomIncludeCompact =
      canonicalEulerThomComplementInclude ≫ associatedBMTargetIncl (d+1) n := rfl

def canonicalEulerThomIncludeRelative (R : Type) [Ring R] (k : ℕ) :
    Hrel R k (canonicalEulerThomIncl d n) ⟶ Hrel R k (associatedBMTargetIncl (d+1) n) :=
  HrelMap R k _ _ canonicalEulerThomInclude_pair_comm

def canonicalEulerThomInfinityMap :
    TopCat.of ({∞} : Set (OnePoint (Configuration (d+1) n))) ⟶
      TopCat.of (canonicalEulerThomComplement d n) :=
  TopCat.ofHom (ContinuousMap.const _ ⟨∞,canonicalEulerThomComplement_infty⟩)

theorem canonicalEulerThomCollapse_pair_comm :
    associatedBMSourceIncl (d+1) n ≫ TopCat.ofHom canonicalEulerThomCollapse =
      canonicalEulerThomInfinityMap ≫ canonicalEulerThomIncl d n := by
  ext ⟨z,hz⟩
  have hz' : z = ∞ := hz
  subst z
  rfl

def canonicalEulerThomCollapseRelative (R : Type) [Ring R] (k : ℕ) :
    Hrel R k (associatedBMSourceIncl (d+1) n) ⟶ Hrel R k (canonicalEulerThomIncl d n) :=
  HrelMap R k _ _ canonicalEulerThomCollapse_pair_comm

/-- The genuine global graph map factors, on relative homology, through
the actual full normal neighborhood of the lowest vertical stratum. -/
theorem canonicalEulerGraphRelative_eq_thom_factor (R : Type) [Ring R] (k : ℕ) :
    HrelMap R k _ _ (associatedBMGraph_pair_comm (canonicalSection d n)) =
      canonicalEulerThomCollapseRelative (d := d) (n := n) R k ≫
        canonicalEulerThomIncludeRelative R k := by
  rw [canonicalEulerGraphRelative_eq_vertical]
  unfold canonicalEulerThomCollapseRelative canonicalEulerThomIncludeRelative
  rw [HrelMap_comp]
  congr 1
  exact canonicalEulerVertical_eq_thom_factor

/-- A genuine vertical point admits every radius, so the normal-disk
comparison does not need an assumed sufficiently small neighborhood. -/
theorem canonicalEulerThom_normalFiberDomain (u : VerticalKernelConfiguration d n) :
    canonicalNormalFiberDomain u.val = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  exact canonicalKernel_add_lift_injective u.val u.property v

theorem canonicalEulerThom_closedBall_subset (u : VerticalKernelConfiguration d n) (r : ℝ) :
    Metric.closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u.val := by
  rw [canonicalEulerThom_normalFiberDomain]
  exact Set.subset_univ _

/-- On every actual normal disk the global collapse is literally the
standard vertical fiber disk, before passing to singular chains. -/
theorem canonicalEulerThomCollapse_normalDisk (u : VerticalKernelConfiguration d n)
    (r : ℝ) (v : Metric.closedBall (0 : ReducedValues (d+1) n) r) :
    canonicalEulerThomCollapse (d := d) (n := n)
      (normalDiskConfiguration u.val r (canonicalEulerThom_closedBall_subset u r) v :
        OnePoint (Configuration (d+1) n)) =
      ((u,v.val) : VerticalAssociated d n) := by
  let x := normalDiskConfiguration u.val r (canonicalEulerThom_closedBall_subset u r) v
  have hcoords : canonicalNormalCoordinates d n x.val = (u.val,v.val) :=
    (canonicalNormalCoordinates d n).apply_symm_apply (u.val,v.val)
  have hx : x ∈ canonicalEulerThomOpen d n := by
    change Function.Injective (canonicalNormalCoordinates d n x.val).1.val
    rw [hcoords]
    exact u.property
  rw [canonicalEulerThomCollapse_of_mem x hx]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    change (canonicalNormalCoordinates d n x.val).1 = u.val
    exact congrArg Prod.fst hcoords
  · change canonicalLinear d n x.val = v.val
    exact congrArg Prod.snd hcoords

/-- The local BM Thom normalization already proved in the localization
diagram applies to the whole normal fiber of each genuine vertical point. -/
theorem canonicalEulerThom_normalDisk_eq_standardFiber
    (R : Type) [Ring R] (k : ℕ) (u : VerticalKernelConfiguration d n)
    {r : ℝ} (hr : 0 < r) :
    canonicalBMNormalDiskRelative u.val hr (canonicalEulerThom_closedBall_subset u r) R k ≫
        HrelMap R k _ _ (associatedBMSupportedGraph_square (canonicalSection d n)) =
      standardNormalDiskRelative (d := d) (n := n) R k hr ≫
        associatedCoverFiberRelative R k (⟨u.val.val,u.property⟩ : Configuration (d+1) n) ≫
        associatedBMFiniteRelative R k (d+1) n := by
  rw [canonicalBMNormalDiskRelative_eq_standardFiber]
  have hpoint : normalDiskConfiguration u.val r (canonicalEulerThom_closedBall_subset u r)
      (associatedNormalDiskZero hr) = (⟨u.val.val,u.property⟩ : Configuration (d+1) n) := by
    apply Subtype.ext
    change u.val.val + canonicalLift d n 0 = u.val.val
    rw [map_zero,add_zero]
  rw [hpoint]

def canonicalEulerThomKernelRelabel (σ : ConfigurationGroup n) :
    VerticalKernelConfiguration d n ≃ₜ VerticalKernelConfiguration d n where
  toFun u := ⟨canonicalKernelRelabel σ u.val,u.property.comp σ.symm.injective⟩
  invFun u := ⟨canonicalKernelRelabel σ⁻¹ u.val,u.property.comp σ.injective⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change u.val.val (σ.symm (σ i)) = u.val.val i
    rw [σ.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change u.val.val (σ (σ.symm i)) = u.val.val i
    rw [σ.apply_symm_apply]
  continuous_toFun :=
    (((canonicalKernelRelabel σ).toContinuousLinearEquiv).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (((canonicalKernelRelabel σ⁻¹).toContinuousLinearEquiv).continuous.comp continuous_subtype_val).subtype_mk _

def canonicalEulerThomRelabel (σ : ConfigurationGroup n) :
    OnePoint (VerticalAssociated d n) ≃ₜ OnePoint (VerticalAssociated d n) :=
  ((canonicalEulerThomKernelRelabel (d := d) σ).prodCongr
    (relabelValues (d := d+1) σ).toHomeomorph).onePointCongr

theorem canonicalEulerThomIncludeCompact_equivariant (σ : ConfigurationGroup n)
    (z : OnePoint (VerticalAssociated d n)) :
    canonicalEulerThomIncludeCompact (d := d) (n := n) (canonicalEulerThomRelabel σ z) =
      associatedBMCoverRelabel σ (canonicalEulerThomIncludeCompact z) := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p => rfl

theorem canonicalEulerThomCollapse_equivariant (σ : ConfigurationGroup n)
    (z : OnePoint (Configuration (d+1) n)) :
    canonicalEulerThomCollapse (d := d) (n := n) (compactifiedConfigurationRelabel σ z) =
      canonicalEulerThomRelabel σ (canonicalEulerThomCollapse z) := by
  have hinj : Function.Injective (canonicalEulerThomIncludeCompact (d := d) (n := n)) :=
    Option.map_injective isClosedEmbedding_canonicalEulerThomInclude.injective
  apply hinj
  rw [canonicalEulerThomIncludeCompact_equivariant]
  have factor (w : OnePoint (Configuration (d+1) n)) :
      canonicalEulerThomIncludeCompact (canonicalEulerThomCollapse w) =
        (canonicalEulerVerticalMap (d := d) (n := n)).hom w := by
    exact (congrArg (fun f => f.hom w) canonicalEulerVertical_eq_thom_factor).symm
  rw [factor,factor]
  exact canonicalEulerSlideFamily_equivariant σ 1 z

theorem canonicalEulerThomComplement_relabel_iff (σ : ConfigurationGroup n)
    (z : OnePoint (VerticalAssociated d n)) :
    canonicalEulerThomRelabel σ z ∈ canonicalEulerThomComplement d n ↔
      z ∈ canonicalEulerThomComplement d n := by
  change canonicalEulerThomIncludeCompact (canonicalEulerThomRelabel σ z) ∈
      associatedBMComplement (d+1) n ↔ _
  rw [canonicalEulerThomIncludeCompact_equivariant]
  exact associatedBMComplement_relabel_mem_iff σ _

def canonicalEulerThomRelabelMap (σ : ConfigurationGroup n) :
    TopCat.of (OnePoint (VerticalAssociated d n)) ⟶ TopCat.of (OnePoint (VerticalAssociated d n)) :=
  TopCat.ofHom ⟨canonicalEulerThomRelabel σ,(canonicalEulerThomRelabel σ).continuous⟩

def canonicalEulerThomComplementRelabelMap (σ : ConfigurationGroup n) :
    TopCat.of (canonicalEulerThomComplement d n) ⟶ TopCat.of (canonicalEulerThomComplement d n) :=
  TopCat.ofHom ⟨(canonicalEulerThomRelabel σ).subtype
      (fun z => (canonicalEulerThomComplement_relabel_iff σ z).symm),
    ((canonicalEulerThomRelabel σ).subtype
      (fun z => (canonicalEulerThomComplement_relabel_iff σ z).symm)).continuous⟩

theorem canonicalEulerThomIncl_equivariant (σ : ConfigurationGroup n) :
    canonicalEulerThomIncl d n ≫ canonicalEulerThomRelabelMap σ =
      canonicalEulerThomComplementRelabelMap σ ≫ canonicalEulerThomIncl d n := rfl

theorem canonicalEulerThomCollapseMap_equivariant (σ : ConfigurationGroup n) :
    associatedBMSourceRelabelMap σ ≫ TopCat.ofHom (canonicalEulerThomCollapse (d := d) (n := n)) =
      TopCat.ofHom canonicalEulerThomCollapse ≫ canonicalEulerThomRelabelMap σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact canonicalEulerThomCollapse_equivariant σ z

theorem canonicalEulerThomIncludeMap_equivariant (σ : ConfigurationGroup n) :
    canonicalEulerThomRelabelMap σ ≫ TopCat.ofHom (canonicalEulerThomIncludeCompact (d := d) (n := n)) =
      TopCat.ofHom canonicalEulerThomIncludeCompact ≫ associatedBMCoverRelabelMap σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact canonicalEulerThomIncludeCompact_equivariant σ z

section Twisted
variable (R : Type) [CommRing R] (χ : ConfigurationGroup n →* Rˣ)

def canonicalEulerThomRelativeAction (σ : ConfigurationGroup n) :
    relComplex R (canonicalEulerThomIncl d n) ⟶ relComplex R (canonicalEulerThomIncl d n) :=
  relComplexMap R _ _ (canonicalEulerThomIncl_equivariant σ)

/-- Genuine twisted relative chains of the full lowest-stratum normal
bundle, with the diagonal tangent/normal permutation action. -/
def canonicalEulerThomTwisted : ChainComplex (ModuleCat R) ℕ :=
  twistedChainComplex R χ (relComplex R (canonicalEulerThomIncl d n))
    (canonicalEulerThomRelativeAction R)

def canonicalEulerThomTwistedCollapse :
    associatedBMTwistedSource R (d := d+1) χ ⟶ canonicalEulerThomTwisted (d := d) R χ :=
  twistedChainMap R χ _ (associatedBMSourceRelativeAction R) (canonicalEulerThomRelativeAction R)
    (relComplexMap R _ _ canonicalEulerThomCollapse_pair_comm)
    (relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) associatedBMSourceRelabelMap
      canonicalEulerThomComplementRelabelMap canonicalEulerThomRelabelMap
      associatedBMSourceIncl_equivariant canonicalEulerThomIncl_equivariant
      canonicalEulerThomCollapse_pair_comm canonicalEulerThomCollapseMap_equivariant)

def canonicalEulerThomTwistedInclude :
    canonicalEulerThomTwisted (d := d) R χ ⟶ associatedBMTwistedTarget R (d := d+1) χ :=
  twistedChainMap R χ _ (canonicalEulerThomRelativeAction R) (associatedBMTargetRelativeAction R)
    (relComplexMap R _ _ canonicalEulerThomInclude_pair_comm)
    (relativeSingularChainMap_equivariant R _ _ canonicalEulerThomComplementRelabelMap
      canonicalEulerThomRelabelMap associatedBMComplementRelabelMap associatedBMCoverRelabelMap
      canonicalEulerThomIncl_equivariant associatedBMTargetIncl_equivariant
      canonicalEulerThomInclude_pair_comm canonicalEulerThomIncludeMap_equivariant)

/-- Both the relative quotient and the permutation quotient commute with
the geometric collapse/inclusion factorization. -/
theorem canonicalEulerThomTwistedCollapse_comp_include :
    canonicalEulerThomTwistedCollapse (d := d) R χ ≫ canonicalEulerThomTwistedInclude R χ =
      canonicalEulerTwistedVerticalMap R χ := by
  unfold canonicalEulerThomTwistedCollapse canonicalEulerThomTwistedInclude canonicalEulerTwistedVerticalMap
  have hπ : Epi (twistedChainProj R χ (relComplex R (associatedBMSourceIncl (d+1) n))
      (associatedBMSourceRelativeAction R)) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [twistedChainProj_map_assoc,twistedChainProj_map,twistedChainProj_map,
    ← Category.assoc,relComplexMap_comp]
  congr 2
  exact canonicalEulerVertical_eq_thom_factor.symm

/-- An unconditional global Euler/Thom factorization through the actual
lowest-stratum normal model, valid for arbitrary coefficient character. -/
theorem associatedBMTwistedEulerMap_eq_thom_factor (k : ℕ) :
    associatedBMTwistedEulerMap R (d := d+1) χ k =
      HomologicalComplex.homologyMap (canonicalEulerThomTwistedCollapse (d := d) R χ) k ≫
        HomologicalComplex.homologyMap (canonicalEulerThomTwistedInclude R χ) k := by
  rw [← HomologicalComplex.homologyMap_comp,canonicalEulerThomTwistedCollapse_comp_include,
    associatedBMTwistedEulerMap_eq_vertical]

end Twisted

end NRR.PrimePowerTopology
