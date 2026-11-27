import NRR.PrimePowerTopologyAssociatedBMLocalization
import NRR.PrimePowerTopologyOrientationKernel
import NRR.PrimePowerTopologyMinimalTwistedHomology

/-! A global proper homotopy from the canonical Euler graph to its vertical
normal model. The normal coordinate is retained in the total-space fiber, so
the homotopy remains proper while the base is collapsed onto the vertical
stratum. -/

noncomputable section
open Set Topology Filter Metric CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

abbrev VerticalKernelConfiguration (d n : ℕ) [NeZero n] :=
  {u : CanonicalKernel d n // Function.Injective u.val}

abbrev VerticalAssociated (d n : ℕ) [NeZero n] :=
  VerticalKernelConfiguration d n × ReducedValues (d+1) n

abbrev EulerAmbient (d n : ℕ) := Fin n → Space (d+1)
abbrev EulerAmbientOpen (d n : ℕ) :=
  {p : EulerAmbient d n × ReducedValues (d+1) n // Function.Injective p.1}

/-- The ambient slide leaves the tangent coordinate fixed and scales only
the normal coordinate. -/
def canonicalEulerSlide (t : ℝ) (x : Fin n → Space (d+1)) :
    Fin n → Space (d+1) :=
  x - t • canonicalLift d n (canonicalLinear d n x)

@[simp] theorem canonicalLinear_eulerSlide (t : ℝ) (x : Fin n → Space (d+1)) :
    canonicalLinear d n (canonicalEulerSlide t x) =
      (1-t) • canonicalLinear d n x := by
  rw [canonicalEulerSlide, map_sub, map_smul, canonicalLinear_lift]
  module

@[simp] theorem canonicalNormalCoordinates_eulerSlide (t : ℝ)
    (x : Fin n → Space (d+1)) :
    canonicalNormalCoordinates d n (canonicalEulerSlide t x) =
      ((canonicalNormalCoordinates d n x).1,
        (1-t) • (canonicalNormalCoordinates d n x).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change canonicalEulerSlide t x - canonicalLift d n
        (canonicalLinear d n (canonicalEulerSlide t x)) =
      x - canonicalLift d n (canonicalLinear d n x)
    rw [canonicalLinear_eulerSlide, canonicalEulerSlide, map_smul]
    module
  · exact canonicalLinear_eulerSlide t x

theorem canonicalEulerSlide_equivariant (t : ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → Space (d+1)) :
    canonicalEulerSlide t (ambientRelabel (d+1) σ x) =
      ambientRelabel (d+1) σ (canonicalEulerSlide t x) := by
  unfold canonicalEulerSlide
  rw [canonicalLinear_ambientRelabel, canonicalLift_relabelValues, map_sub, map_smul]

theorem canonicalEulerSlide_collision (t : ℝ) (x : Fin n → Space (d+1))
    (h : ¬ Function.Injective x) : ¬ Function.Injective (canonicalEulerSlide t x) := by
  change ¬ (∀ i j, x i = x j → i = j) at h
  push_neg at h
  obtain ⟨i,j,hx,hij⟩ := h
  intro hout
  have hhor : (horizontalHeight d (x i)).1 = (horizontalHeight d (x j)).1 :=
    congrArg (fun z => (horizontalHeight d z).1) hx
  have hv (k : Fin d) :
      (canonicalLinear d n x).val k i = (canonicalLinear d n x).val k j := by
    change centered (fun l => (horizontalHeight d (x l)).1 k) i =
      centered (fun l => (horizontalHeight d (x l)).1 k) j
    simp [centered, hhor]
  have hlift : canonicalLift d n (canonicalLinear d n x) i =
      canonicalLift d n (canonicalLinear d n x) j := by
    apply (horizontalHeight d).injective
    apply Prod.ext
    · ext k
      simpa [canonicalLift] using hv k
    · simp [canonicalLift]
  have he : canonicalEulerSlide t x i = canonicalEulerSlide t x j := by
    change x i - t • canonicalLift d n (canonicalLinear d n x) i =
      x j - t • canonicalLift d n (canonicalLinear d n x) j
    rw [hx, hlift]
  exact hij (hout he)

theorem canonicalEulerSlide_endpoint_vertical
    (x : EulerAmbient d n) (hx : Function.Injective
      (canonicalEulerSlide (d := d) (n := n) 1 x)) :
    (⟨canonicalEulerSlide (d := d) (n := n) 1 x,hx⟩ : Configuration (d+1) n) ∈
      verticalSet d n := by
  let y : Configuration (d+1) n := ⟨canonicalEulerSlide (d := d) (n := n) 1 x,hx⟩
  apply (canonicalSection_zero_iff (d := d) (n := n) y).mp
  apply Subtype.ext
  simpa using canonicalLinear_eulerSlide 1 x

def associatedAmbientHomeomorph :
    EulerAmbientOpen d n ≃ₜ AssociatedCover (d+1) n where
  toFun p := (⟨p.val.1,p.property⟩,p.val.2)
  invFun p := ⟨(p.1.val,p.2),p.1.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

def associatedAmbientOpenSet (d n : ℕ) :
    Set (EulerAmbient d n × ReducedValues (d+1) n) :=
  {p | Function.Injective p.1}

theorem isOpen_associatedAmbientOpenSet (d n : ℕ) :
    IsOpen (associatedAmbientOpenSet d n) := by
  have heq : associatedAmbientOpenSet d n =
      {x : EulerAmbient d n | Function.Injective x} ×ˢ
        (Set.univ : Set (ReducedValues (d+1) n)) := by
    ext p
    simp [associatedAmbientOpenSet]
  rw [heq]
  exact (isOpen_injectiveSites (d+1) n).prod isOpen_univ

/-- Collapse nonconfigurations in the ambient base coordinate to infinity. -/
def associatedAmbientCollapse :
    C(EulerAmbient d n × ReducedValues (d+1) n,
      OnePoint (AssociatedCover (d+1) n)) :=
  ⟨fun p => (associatedAmbientHomeomorph (d := d) (n := n)).onePointCongr
      (openCollapse (associatedAmbientOpenSet (d := d) (n := n)) p),
    (associatedAmbientHomeomorph (d := d) (n := n)).onePointCongr.continuous.comp
      (continuous_openCollapse _ (isOpen_associatedAmbientOpenSet (d := d) (n := n)))⟩

@[simp] theorem associatedAmbientCollapse_of_mem
    (p : EulerAmbient d n × ReducedValues (d+1) n) (hp : Function.Injective p.1) :
    associatedAmbientCollapse (d := d) (n := n) p =
      (((⟨p.1,hp⟩ : Configuration (d+1) n),p.2) : OnePoint (AssociatedCover (d+1) n)) := by
  change (associatedAmbientHomeomorph (d := d) (n := n)).onePointCongr
    (openCollapse (associatedAmbientOpenSet d n) p) = _
  rw [openCollapse_of_mem (associatedAmbientOpenSet d n) hp]
  simp [associatedAmbientHomeomorph]

@[simp] theorem associatedAmbientCollapse_of_not_mem
    (p : EulerAmbient d n × ReducedValues (d+1) n) (hp : ¬ Function.Injective p.1) :
    associatedAmbientCollapse (d := d) (n := n) p = ∞ := by
  change (associatedAmbientHomeomorph (d := d) (n := n)).onePointCongr
    (openCollapse (associatedAmbientOpenSet d n) p) = ∞
  rw [openCollapse_of_not_mem (associatedAmbientOpenSet d n) hp]
  simp

def canonicalEulerSlideAmbient (t : unitInterval) (x : EulerAmbient d n) :
    EulerAmbient d n × ReducedValues (d+1) n :=
  (canonicalEulerSlide (d := d) (n := n) (t : ℝ) x, canonicalLinear d n x)

theorem continuous_canonicalEulerSlideAmbient :
    Continuous (fun p : unitInterval × EulerAmbient d n =>
      canonicalEulerSlideAmbient (d := d) (n := n) p.1 p.2) := by
  let tv : unitInterval × EulerAmbient d n → ℝ := fun p => (p.1 : ℝ)
  have htv : Continuous tv := continuous_subtype_val.comp continuous_fst
  have hlin : Continuous (fun p : unitInterval × EulerAmbient d n =>
      canonicalLinear d n p.2) := (canonicalLinear d n).continuous.comp continuous_snd
  refine ?_
  change Continuous (fun p : unitInterval × EulerAmbient d n =>
    (p.2 - tv p • canonicalLift d n (canonicalLinear d n p.2),
      canonicalLinear d n p.2))
  exact ((continuous_snd.sub (htv.smul
    ((canonicalLift d n).continuous.comp hlin))).prodMk hlin)

def associatedAmbientSlideMap :
    C(unitInterval × EulerAmbient d n, OnePoint (AssociatedCover (d+1) n)) :=
  associatedAmbientCollapse.comp
    ⟨fun p => canonicalEulerSlideAmbient (d := d) (n := n) p.1 p.2,
      continuous_canonicalEulerSlideAmbient⟩

@[simp] theorem associatedAmbientSlideMap_of_mem
    (t : unitInterval) (x : EulerAmbient d n)
    (hx : Function.Injective (canonicalEulerSlide (d := d) (n := n) (t : ℝ) x)) :
    associatedAmbientSlideMap (d := d) (n := n) (t,x) =
      (((⟨canonicalEulerSlide (d := d) (n := n) (t : ℝ) x,hx⟩ :
        Configuration (d+1) n),canonicalLinear d n x) :
        OnePoint (AssociatedCover (d+1) n)) := by
  exact associatedAmbientCollapse_of_mem
    (d := d) (n := n) (canonicalEulerSlideAmbient (d := d) (n := n) t x) hx

@[simp] theorem associatedAmbientSlideMap_collision
    (t : unitInterval) (x : EulerAmbient d n)
    (hx : ¬ Function.Injective x) :
    associatedAmbientSlideMap (d := d) (n := n) (t,x) = ∞ := by
  exact associatedAmbientCollapse_of_not_mem (d := d) (n := n) _
    (canonicalEulerSlide_collision (d := d) (n := n) (t : ℝ) x hx)

theorem associatedAmbientSlideMap_endpoint_vertical
    (x : EulerAmbient d n)
    (hx : Function.Injective (canonicalEulerSlide (d := d) (n := n) 1 x)) :
    associatedAmbientSlideMap (d := d) (n := n) (1,x) =
      (((⟨canonicalEulerSlide (d := d) (n := n) 1 x,hx⟩ :
        Configuration (d+1) n),canonicalLinear d n x) :
        OnePoint (AssociatedCover (d+1) n)) ∧
      (⟨canonicalEulerSlide (d := d) (n := n) 1 x,hx⟩ :
        Configuration (d+1) n) ∈ verticalSet d n := by
  refine ⟨associatedAmbientSlideMap_of_mem 1 x hx, ?_⟩
  exact canonicalEulerSlide_endpoint_vertical (d := d) (n := n) x hx


def canonicalEulerSlideFiniteFamily :
    unitInterval × Configuration (d+1) n → OnePoint (AssociatedCover (d+1) n) :=
  fun p => associatedAmbientCollapse (d := d) (n := n)
    (canonicalEulerSlideAmbient (d := d) (n := n) p.1 p.2.val)

theorem continuous_canonicalEulerSlideFiniteFamily :
    Continuous (canonicalEulerSlideFiniteFamily (d := d) (n := n)) :=
  associatedAmbientCollapse.continuous.comp
    (continuous_canonicalEulerSlideAmbient.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

private def canonicalEulerSlideRecover :
    unitInterval × (EulerAmbient d n × ReducedValues (d+1) n) → EulerAmbient d n :=
  fun p => p.2.1 + (p.1 : ℝ) • canonicalLift d n p.2.2

private theorem canonicalEulerSlideRecover_continuous :
    Continuous (canonicalEulerSlideRecover (d := d) (n := n)) := by
  exact (continuous_snd.fst.add
    ((continuous_subtype_val.comp continuous_fst).smul
      ((canonicalLift d n).continuous.comp continuous_snd.snd)))

private theorem canonicalEulerSlideRecover_left (t : unitInterval) (x : EulerAmbient d n) :
    canonicalEulerSlideRecover (d := d) (n := n)
      (t,canonicalEulerSlideAmbient (d := d) (n := n) t x) = x := by
  simp [canonicalEulerSlideRecover, canonicalEulerSlideAmbient, canonicalEulerSlide,
    canonicalLinear_lift]

private theorem isCompact_preimage_canonicalEulerSlideAmbient
    (K : Set (EulerAmbient d n × ReducedValues (d+1) n)) (hK : IsCompact K) :
    IsCompact ((fun p : unitInterval × EulerAmbient d n =>
      canonicalEulerSlideAmbient (d := d) (n := n) p.1 p.2) ⁻¹' K) := by
  let recPair : unitInterval × (EulerAmbient d n × ReducedValues (d+1) n) →
      unitInterval × EulerAmbient d n := fun p =>
        (p.1,canonicalEulerSlideRecover (d := d) (n := n) p)
  have hrec : Continuous recPair :=
    continuous_fst.prodMk canonicalEulerSlideRecover_continuous
  have hT : IsCompact (Set.univ : Set unitInterval) := isCompact_univ
  have hK' : IsCompact ((Set.univ : Set unitInterval) ×ˢ K) := hT.prod hK
  have hC : IsCompact (recPair '' (Set.univ ×ˢ K)) := hK'.image hrec
  have hclosed : IsClosed ((fun p : unitInterval × EulerAmbient d n =>
      canonicalEulerSlideAmbient (d := d) (n := n) p.1 p.2) ⁻¹' K) :=
    hK.isClosed.preimage continuous_canonicalEulerSlideAmbient
  apply hC.of_isClosed_subset hclosed
  intro p hp
  refine ⟨(p.1,canonicalEulerSlideAmbient (d := d) (n := n) p.1 p.2),?_,?_⟩
  · exact ⟨Set.mem_univ _,hp⟩
  · apply Prod.ext
    · rfl
    · exact canonicalEulerSlideRecover_left p.1 p.2

section ProperFamily
variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
  [T2Space X] [TopologicalSpace Y]

def compactifiedFamily (F : T × X → OnePoint Y) :
    T × OnePoint X → OnePoint Y := fun p =>
      p.2.elim ∞ (fun x => F (p.1,x))

theorem continuous_compactifiedFamily (F : T × X → OnePoint Y)
    (hF : Continuous F)
    (proper : ∀ K : Set Y, IsCompact K →
      IsCompact (F ⁻¹' (((↑) : Y → OnePoint Y) '' K))) :
    Continuous (compactifiedFamily F) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,z⟩
  induction z using OnePoint.rec with
  | infty =>
    change Filter.map (compactifiedFamily F) (𝓝 (t,(∞ : OnePoint X))) ≤ 𝓝 ∞
    apply OnePoint.le_nhds_infty.mpr
    intro K hKc hKk
    let A : Set X := Prod.snd '' (F ⁻¹' (((↑) : Y → OnePoint Y) '' K))
    have hA : IsCompact A := (proper K hKk).image continuous_snd
    have hAc : IsClosed A := hA.isClosed
    have hV : (((↑) : X → OnePoint X) '' A)ᶜ ∈ 𝓝 (∞ : OnePoint X) := by
      apply OnePoint.isOpen_compl_image_coe.mpr ⟨hAc,hA⟩ |>.mem_nhds
      rintro ⟨x,hx,he⟩
      exact OnePoint.coe_ne_infty x he
    have hW : (Set.univ : Set T) ×ˢ (((↑) : X → OnePoint X) '' A)ᶜ ∈
        𝓝 (t,(∞ : OnePoint X)) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod Filter.univ_mem hV
    apply Filter.mem_of_superset hW
    rintro ⟨s,w⟩ ⟨_,hw⟩
    induction w using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe x =>
      change F (s,x) ∈ (((↑) : Y → OnePoint Y) '' Kᶜ) ∪ {∞}
      generalize hfy : F (s,x) = z
      induction z using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe y =>
        by_cases hy : y ∈ K
        · apply False.elim
          apply hw
          refine ⟨x,⟨(s,x),⟨y,hy,?_⟩,rfl⟩,rfl⟩
          exact hfy.symm
        · exact Or.inl ⟨y,hy,rfl⟩
  | coe x =>
    have he : IsOpenEmbedding
        (Prod.map (id : T → T) ((↑) : X → OnePoint X)) :=
      IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
    apply (he.continuousAt_iff (g := compactifiedFamily F) (x := (t,x))).mp
    change ContinuousAt (fun p : T × X => F (p.1,p.2)) (t,x)
    exact hF.continuousAt
end ProperFamily

private theorem isCompact_preimage_associatedAmbientSlideMap
    (K : Set (AssociatedCover (d+1) n)) (hK : IsCompact K) :
    IsCompact (associatedAmbientSlideMap (d := d) (n := n) ⁻¹'
      (((↑) : AssociatedCover (d+1) n → OnePoint (AssociatedCover (d+1) n)) '' K)) := by
  let j : AssociatedCover (d+1) n → EulerAmbient d n × ReducedValues (d+1) n :=
    fun p => (p.1.val,p.2)
  have hj : Continuous j :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hbound := isCompact_preimage_canonicalEulerSlideAmbient (j '' K) (hK.image hj)
  have hclosed : IsClosed (associatedAmbientSlideMap (d := d) (n := n) ⁻¹'
      (((↑) : AssociatedCover (d+1) n → OnePoint (AssociatedCover (d+1) n)) '' K)) :=
    (hK.image OnePoint.continuous_coe).isClosed.preimage associatedAmbientSlideMap.continuous
  apply hbound.of_isClosed_subset hclosed
  rintro ⟨t,x⟩ ⟨p,hp,he⟩
  by_cases hx : Function.Injective (canonicalEulerSlide (d := d) (n := n) (t : ℝ) x)
  · rw [associatedAmbientSlideMap_of_mem t x hx] at he
    have he' := OnePoint.coe_injective he
    exact ⟨p,hp,congrArg j he'⟩
  · have hz : associatedAmbientSlideMap (d := d) (n := n) (t,x) = ∞ :=
      associatedAmbientCollapse_of_not_mem (d := d) (n := n) _ hx
    exact False.elim (OnePoint.coe_ne_infty p (he.trans hz))

/-- Uniform properness of the genuine configuration slide, including all
parameters at which the base configuration collides. -/
theorem isCompact_preimage_canonicalEulerSlideFiniteFamily
    (K : Set (AssociatedCover (d+1) n)) (hK : IsCompact K) :
    IsCompact (canonicalEulerSlideFiniteFamily (d := d) (n := n) ⁻¹'
      (((↑) : AssociatedCover (d+1) n → OnePoint (AssociatedCover (d+1) n)) '' K)) := by
  let e : unitInterval × Configuration (d+1) n → unitInterval × EulerAmbient d n :=
    Prod.map id Subtype.val
  have he : IsEmbedding e := IsEmbedding.id.prodMap IsEmbedding.subtypeVal
  apply he.isInducing.isCompact_preimage'
    (isCompact_preimage_associatedAmbientSlideMap K hK)
  rintro ⟨t,x⟩ ⟨p,hp,heq⟩
  have hx : Function.Injective x := by
    by_contra hx
    rw [associatedAmbientSlideMap_collision t x hx] at heq
    exact OnePoint.coe_ne_infty p heq
  exact ⟨(t,⟨x,hx⟩),rfl⟩

/-- The actual proper Euler slide on one-point compactifications. -/
def canonicalEulerSlideFamily :
    C(unitInterval × OnePoint (Configuration (d+1) n),
      OnePoint (AssociatedCover (d+1) n)) :=
  ⟨compactifiedFamily (canonicalEulerSlideFiniteFamily (d := d) (n := n)),
    continuous_compactifiedFamily _ continuous_canonicalEulerSlideFiniteFamily
      isCompact_preimage_canonicalEulerSlideFiniteFamily⟩

@[simp] theorem canonicalEulerSlideFamily_infty (t : unitInterval) :
    canonicalEulerSlideFamily (d := d) (n := n) (t,∞) = ∞ := rfl

@[simp] theorem canonicalEulerSlideFamily_coe (t : unitInterval)
    (x : Configuration (d+1) n) :
    canonicalEulerSlideFamily (d := d) (n := n) (t,(x : OnePoint (Configuration (d+1) n))) =
      associatedAmbientSlideMap (d := d) (n := n) (t,x.val) := rfl

@[simp] theorem canonicalEulerSlideFamily_zero (z : OnePoint (Configuration (d+1) n)) :
    canonicalEulerSlideFamily (d := d) (n := n) (0,z) =
      (associatedBMGraph (canonicalSection d n)).hom z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    have hx : Function.Injective (canonicalEulerSlide (d := d) (n := n) 0 x.val) := by
      simpa [canonicalEulerSlide] using x.property
    rw [canonicalEulerSlideFamily_coe,associatedAmbientSlideMap_of_mem 0 x.val hx]
    change (((⟨canonicalEulerSlide (d := d) (n := n) 0 x.val,hx⟩,
      canonicalLinear d n x.val) : AssociatedCover (d+1) n) :
      OnePoint (AssociatedCover (d+1) n)) =
      (((x,canonicalLinear d n x.val) : AssociatedCover (d+1) n) :
        OnePoint (AssociatedCover (d+1) n))
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      simp [canonicalEulerSlide]
    · rfl

/-- The endpoint is supported on the actual vertical stratum and retains
the full original normal vector in the associated fiber. -/
def canonicalEulerVerticalMap :
    TopCat.of (OnePoint (Configuration (d+1) n)) ⟶
      TopCat.of (OnePoint (AssociatedCover (d+1) n)) :=
  TopCat.ofHom ⟨fun z => canonicalEulerSlideFamily (d := d) (n := n) (1,z),
    canonicalEulerSlideFamily.continuous.comp (continuous_const.prodMk continuous_id)⟩

theorem canonicalEulerVertical_pair_comm :
    associatedBMSourceIncl (d+1) n ≫ canonicalEulerVerticalMap (d := d) (n := n) =
      associatedBMInfinityMap (d+1) n ≫ associatedBMTargetIncl (d+1) n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨z,hz⟩
  have hz' : z = ∞ := hz
  subst z
  rfl

/-- A global geometric comparison, before taking either relative chains
or permutation coinvariants. -/
def canonicalEulerVerticalPairHomotopy :
    ContinuousPairHomotopy (associatedBMSourceIncl (d+1) n)
      (associatedBMTargetIncl (d+1) n)
      (associatedBMGraph_pair_comm (canonicalSection d n))
      (canonicalEulerVertical_pair_comm (d := d) (n := n)) where
  sub := ContinuousMap.Homotopy.refl (associatedBMInfinityMap (d+1) n).hom
  amb :=
    { toFun := canonicalEulerSlideFamily (d := d) (n := n)
      continuous_toFun := canonicalEulerSlideFamily.continuous
      map_zero_left := canonicalEulerSlideFamily_zero
      map_one_left := fun _ => rfl }
  compat := by
    rintro t ⟨z,hz⟩
    have hz' : z = ∞ := hz
    subst z
    rfl

theorem canonicalEulerGraphRelative_eq_vertical
    (R : Type) [Ring R] (k : ℕ) :
    HrelMap R k _ _ (associatedBMGraph_pair_comm (canonicalSection d n)) =
      HrelMap R k _ _ (canonicalEulerVertical_pair_comm (d := d) (n := n)) :=
  HrelMap_eq_of_continuousPairHomotopy R _ _ _ _ canonicalEulerVerticalPairHomotopy k

theorem associatedAmbientCollapse_equivariant (σ : ConfigurationGroup n)
    (p : EulerAmbient d n × ReducedValues (d+1) n) :
    associatedAmbientCollapse (d := d) (n := n)
      (ambientRelabel (d+1) σ p.1,relabelValues σ p.2) =
      associatedBMCoverRelabel σ (associatedAmbientCollapse (d := d) (n := n) p) := by
  by_cases hp : Function.Injective p.1
  · have hp' : Function.Injective (ambientRelabel (d+1) σ p.1) :=
      hp.comp σ.symm.injective
    rw [associatedAmbientCollapse_of_mem _ hp',associatedAmbientCollapse_of_mem _ hp]
    rfl
  · have hp' : ¬ Function.Injective (ambientRelabel (d+1) σ p.1) := by
      intro h
      apply hp
      intro i j hij
      have h' := h (show ambientRelabel (d+1) σ p.1 (σ i) =
          ambientRelabel (d+1) σ p.1 (σ j) by simpa [ambientRelabel] using hij)
      exact σ.injective h'
    rw [associatedAmbientCollapse_of_not_mem _ hp',associatedAmbientCollapse_of_not_mem _ hp]
    rfl

theorem canonicalEulerSlideFamily_equivariant (σ : ConfigurationGroup n)
    (t : unitInterval) (z : OnePoint (Configuration (d+1) n)) :
    canonicalEulerSlideFamily (d := d) (n := n)
        (t,compactifiedConfigurationRelabel σ z) =
      associatedBMCoverRelabel σ (canonicalEulerSlideFamily (d := d) (n := n) (t,z)) := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change associatedAmbientCollapse (d := d) (n := n)
      (canonicalEulerSlide (t : ℝ) (ambientRelabel (d+1) σ x.val),
        canonicalLinear d n (ambientRelabel (d+1) σ x.val)) = _
    rw [canonicalEulerSlide_equivariant,canonicalLinear_ambientRelabel]
    exact associatedAmbientCollapse_equivariant (d := d) σ
      (canonicalEulerSlide (t : ℝ) x.val,canonicalLinear d n x.val)

theorem canonicalEulerVertical_equivariant (σ : ConfigurationGroup n) :
    associatedBMSourceRelabelMap σ ≫ canonicalEulerVerticalMap (d := d) (n := n) =
      canonicalEulerVerticalMap (d := d) (n := n) ≫ associatedBMCoverRelabelMap σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact canonicalEulerSlideFamily_equivariant σ 1 z

/-- The global vertical comparison descends to genuine twisted relative
chains, without division by the permutation-group order. -/
def canonicalEulerTwistedVerticalMap (R : Type) [CommRing R]
    (χ : ConfigurationGroup n →* Rˣ) :
    associatedBMTwistedSource R (d := d+1) χ ⟶
      associatedBMTwistedTarget R (d := d+1) χ :=
  twistedChainMap R χ _ (associatedBMSourceRelativeAction R)
    (associatedBMTargetRelativeAction R)
    (relComplexMap R _ _ (canonicalEulerVertical_pair_comm (d := d) (n := n)))
    (relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) associatedBMSourceRelabelMap
      associatedBMComplementRelabelMap associatedBMCoverRelabelMap
      associatedBMSourceIncl_equivariant associatedBMTargetIncl_equivariant
      canonicalEulerVertical_pair_comm canonicalEulerVertical_equivariant)

def canonicalEulerTwistedVerticalHomotopy (R : Type) [CommRing R]
    (χ : ConfigurationGroup n →* Rˣ) :
    Homotopy
      (associatedBMTwistedGraphMap R χ (canonicalSection d n) canonicalSection_equivariant)
      (canonicalEulerTwistedVerticalMap (d := d) R χ) :=
  twistedRelativeSingularChainHomotopy R χ _ _
    (fun _ => 𝟙 _) associatedBMSourceRelabelMap
    associatedBMComplementRelabelMap associatedBMCoverRelabelMap
    associatedBMSourceIncl_equivariant associatedBMTargetIncl_equivariant
    (associatedBMGraph_pair_comm (canonicalSection d n)) canonicalEulerVertical_pair_comm
    canonicalEulerVerticalPairHomotopy
    (associatedBMGraph_equivariant (canonicalSection d n) canonicalSection_equivariant)
    canonicalEulerVertical_equivariant canonicalEulerSlideFamily_equivariant

/-- The actual global twisted Euler morphism equals the homology map of
the explicit vertical normal endpoint, in every degree and character. -/
theorem associatedBMTwistedEulerMap_eq_vertical (R : Type) [CommRing R]
    (χ : ConfigurationGroup n →* Rˣ) (k : ℕ) :
    associatedBMTwistedEulerMap R (d := d+1) χ k =
      HomologicalComplex.homologyMap (canonicalEulerTwistedVerticalMap (d := d) R χ) k := by
  calc
    _ = HomologicalComplex.homologyMap
        (associatedBMTwistedGraphMap R χ (canonicalSection d n) canonicalSection_equivariant) k :=
      ((associatedBMTwistedGraphZeroHomotopy R χ (canonicalSection d n)
        canonicalSection_equivariant).homologyMap_eq k).symm
    _ = _ := (canonicalEulerTwistedVerticalHomotopy R χ).homologyMap_eq k

end NRR.PrimePowerTopology
