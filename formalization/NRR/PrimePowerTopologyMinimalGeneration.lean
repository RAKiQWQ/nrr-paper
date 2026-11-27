import NRR.SingularHomologyFiniteWedge
import NRR.PrimePowerTopologyMinimalRelative
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Basis.Basic

/-! Exhaustion of actual lowest-stratum singular homology by the genuine
minimal-cell fundamental classes. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

def univSetHomeomorph (X : Type) [TopologicalSpace X] : (Set.univ : Set X) ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x,Set.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

def puncturedHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (c : X) : {x : X // x ≠ c} ≃ₜ {y : Y // y ≠ e c} where
  toFun x := ⟨e x.val,fun h => x.property (e.injective h)⟩
  invFun y := ⟨e.symm y.val,fun h => y.property
    ((e.apply_symm_apply y.val).symm.trans (congrArg e h))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

def puncturedSphereChart (m : ℕ) (b : Sph m) :
    {x : Sph m // x ≠ -b} ≃ₜ EuclideanSpace ℝ (Fin m) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) = m+1) := ⟨by simp⟩
  have hs : {x : Sph m | x ≠ -b} = (stereographic' m (-b)).source := by ext x; simp
  have ht : (stereographic' m (-b)).target = Set.univ := by simp
  exact (Homeomorph.setCongr hs).trans
    ((stereographic' m (-b)).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr ht).trans (univSetHomeomorph _)))

/-- A global vector chart gives a contraction fixing any specified basepoint. -/
def contractionOfVectorChart {X E : Type} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : X ≃ₜ E) (b : X) :
    ContractionData X b where
  path x := {
    toFun := fun t => e.symm ((1-(t : ℝ)) • e b + (t : ℝ) • e x)
    continuous_toFun := e.symm.continuous.comp
      (((continuous_const.sub continuous_subtype_val).smul continuous_const).add
        (continuous_subtype_val.smul continuous_const))
    source' := by simp
    target' := by simp }
  continuous_uncurry := e.symm.continuous.comp
    (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul continuous_const).add
      ((continuous_subtype_val.comp continuous_snd).smul
        (e.continuous.comp continuous_fst)))
  path_base := by
    ext t
    change e.symm ((1-(t : ℝ)) • e b + (t : ℝ) • e b) = b
    rw [← add_smul,sub_add_cancel,one_smul,e.symm_apply_apply]

abbrev MinimalCommonCell (d n : ℕ) := OnePoint (Space d × (Fin n → ℝ))

def minimalCellCommonChart (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    OnePoint (Space d × heightChamber n σ) ≃ₜ MinimalCommonCell d n :=
  ((Homeomorph.refl (Space d)).prodCongr (heightChamberEuclidean n σ)).onePointCongr

def minimalCommonSumHomeomorph (d n : ℕ) :
    (Σ _ : Equiv.Perm (Fin n),MinimalCommonCell d n) ≃ₜ MinimalSphereSum d n where
  toEquiv := Equiv.sigmaCongrRight fun σ => (minimalCellCommonChart d n σ).symm.toEquiv
  continuous_toFun := by
    apply continuous_sigma
    intro σ
    exact continuous_sigmaMk.comp (minimalCellCommonChart d n σ).symm.continuous
  continuous_invFun := by
    apply continuous_sigma
    intro σ
    exact continuous_sigmaMk.comp (minimalCellCommonChart d n σ).continuous

/-- The proved minimal-cell quotient, with all branches expressed in the
same one-point compactified vector-space coordinates. -/
def minimalCommonWedgePresentation {d n : ℕ} (i₀ : Fin n) :
    FiniteWedgePresentation (Equiv.Perm (Fin n)) (MinimalCommonCell d n)
      (minimalSkeleton d n) where
  projection := (minimalWedgeProjection i₀).comp ⟨minimalCommonSumHomeomorph d n,
    (minimalCommonSumHomeomorph d n).continuous⟩
  base := ∞
  point := minimalCellInclusion i₀ (1 : Equiv.Perm (Fin n)) ∞
  at_base σ := by apply Subtype.ext; rfl
  quotient := (isQuotientMap_minimalWedgeProjection i₀).comp
    (minimalCommonSumHomeomorph d n).isQuotientMap
  fiber p q := by
    change minimalWedgeProjection i₀ (minimalCommonSumHomeomorph d n p) =
      minimalWedgeProjection i₀ (minimalCommonSumHomeomorph d n q) ↔ _
    rw [minimalWedgeProjection_fiber]
    constructor
    · rintro (he | ⟨hp,hq⟩)
      · exact Or.inl ((minimalCommonSumHomeomorph d n).injective he)
      · right
        constructor
        · exact (minimalCellCommonChart d n p.1).symm.injective hp
        · exact (minimalCellCommonChart d n q.1).symm.injective hq
    · rintro (rfl | ⟨hp,hq⟩)
      · exact Or.inl rfl
      · right
        constructor
        · change (minimalCellCommonChart d n p.1).symm p.2 = ∞
          rw [hp]
          rfl
        · change (minimalCellCommonChart d n q.1).symm q.2 = ∞
          rw [hq]
          rfl

def minimalCommonSphere (d n : ℕ) : MinimalCommonCell d n ≃ₜ Sph (d+n) :=
  onePointEquivSphereOfFinrankEq (by simp [Module.finrank_prod])

def minimalCommonMark (d n : ℕ) : MinimalCommonCell d n :=
  (minimalCommonSphere d n).symm (-(minimalCommonSphere d n) ∞)

theorem minimalCommonMark_ne_infty (d n : ℕ) : minimalCommonMark d n ≠ ∞ := by
  intro h
  have hh := congrArg (minimalCommonSphere d n) h
  simp only [minimalCommonMark,Homeomorph.apply_symm_apply] at hh
  exact (ne_neg_of_mem_unit_sphere ℝ ((minimalCommonSphere d n) ∞)) hh.symm

def minimalCommonPuncturedChart (d n : ℕ) :
    {x : MinimalCommonCell d n // x ≠ minimalCommonMark d n} ≃ₜ
      EuclideanSpace ℝ (Fin (d+n)) :=
  (puncturedHomeomorph (minimalCommonSphere d n) (minimalCommonMark d n)).trans
    ((Homeomorph.setCongr (by simp [minimalCommonMark])).trans
      (puncturedSphereChart (d+n) ((minimalCommonSphere d n) ∞)))

def minimalCommonPuncturedContraction (d n : ℕ) :
    ContractionData {x : MinimalCommonCell d n // x ≠ minimalCommonMark d n}
      ⟨∞,Ne.symm (minimalCommonMark_ne_infty d n)⟩ :=
  contractionOfVectorChart (minimalCommonPuncturedChart d n) _

section RingCoefficients
variable (R : Type) [Ring R]

/-- Actual positive homology of the lowest skeleton is generated by the
homology images of its actual compactified cells. -/
theorem iSup_range_minimalCellInclusionMap_eq_top {d n : ℕ}
    (i₀ : Fin n) (k : ℕ) (hk : k ≠ 0) :
    (⨆ σ : Equiv.Perm (Fin n), LinearMap.range
      (HabsMap R k (minimalCellInclusionMap (d := d) i₀ σ)).hom) = ⊤ := by
  cases k with
  | zero => contradiction
  | succ k =>
    let P := minimalCommonWedgePresentation (d := d) i₀
    have hg := P.iSup_range_homologyInclusion_eq_top R (minimalCommonMark d n)
      (minimalCommonMark_ne_infty d n) (minimalCommonPuncturedContraction d n) k
    apply top_unique
    rw [← hg]
    apply iSup_le
    intro σ z hz
    obtain ⟨x,hx⟩ := hz
    apply (le_iSup (fun τ : Equiv.Perm (Fin n) => LinearMap.range
      (HabsMap R (k+1) (minimalCellInclusionMap (d := d) i₀ τ)).hom) σ)
    have he : TopCat.ofHom (P.inclusion σ) =
        TopCat.ofHom ⟨(minimalCellCommonChart d n σ).symm,
          (minimalCellCommonChart d n σ).symm.continuous⟩ ≫
          minimalCellInclusionMap (d := d) i₀ σ := rfl
    rw [he,HabsMap_comp] at hx
    exact ⟨HabsMap R (k+1) (TopCat.ofHom ⟨(minimalCellCommonChart d n σ).symm,
      (minimalCellCommonChart d n σ).symm.continuous⟩) x,hx⟩

/-- The previously constructed genuine cell fundamental classes exhaust
all actual top singular homology classes of the lowest skeleton. -/
theorem span_minimalFundamentalClass_eq_top {d n : ℕ}
    (i₀ : Fin n) (hdim : 0 < d+n) :
    Submodule.span R (Set.range (fun σ : Equiv.Perm (Fin n) =>
      minimalFundamentalClass R i₀ σ hdim)) = ⊤ := by
  apply top_unique
  rw [← iSup_range_minimalCellInclusionMap_eq_top R (d := d) i₀ (d+n) hdim.ne']
  apply iSup_le
  intro σ z hz
  obtain ⟨x,rfl⟩ := hz
  let e := minimalCellTopHomologyIso R d n σ hdim
  have hex : e.inv (e.hom x) = x :=
    congrArg (fun f : Habs R (d+n) (TopCat.of (OnePoint (Space d × heightChamber n σ))) ⟶
      Habs R (d+n) (TopCat.of (OnePoint (Space d × heightChamber n σ))) => f x) e.hom_inv_id
  have hgen : minimalCellGenerator R i₀ σ hdim (e.hom x) =
      HabsMap R (d+n) (minimalCellInclusionMap (d := d) i₀ σ) x := by
    change HabsMap R (d+n) (minimalCellInclusionMap (d := d) i₀ σ)
      (e.inv (e.hom x)) = _
    rw [hex]
  rw [← hgen]
  have hs : minimalCellGenerator R i₀ σ hdim (e.hom x) =
      (e.hom x) • minimalFundamentalClass R i₀ σ hdim := by
    simpa only [smul_eq_mul,mul_one,minimalFundamentalClass] using
      (minimalCellGenerator R i₀ σ hdim).hom.map_smul (e.hom x) (1 : R)
  rw [hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ,rfl⟩)

/-- The genuine geometric fundamental classes form a basis, not merely
a linearly independent family. -/
def minimalFundamentalBasis {d n : ℕ} (i₀ : Fin n) (hdim : 0 < d+n) :
    Module.Basis (Equiv.Perm (Fin n)) R (Habs R (d+n) (TopCat.of (minimalSkeleton d n))) :=
  Module.Basis.mk (linearIndependent_minimalFundamentalClass R i₀ hdim)
    (by rw [span_minimalFundamentalClass_eq_top R i₀ hdim])

@[simp] theorem minimalFundamentalBasis_apply {d n : ℕ} (i₀ : Fin n)
    (hdim : 0 < d+n) (σ : Equiv.Perm (Fin n)) :
    minimalFundamentalBasis R i₀ hdim σ = minimalFundamentalClass R i₀ σ hdim :=
  Module.Basis.mk_apply _ _ _

def minimalTopHomologyLinearEquiv {d n : ℕ} (i₀ : Fin n) (hdim : 0 < d+n) :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ≃ₗ[R] (Equiv.Perm (Fin n) → R) :=
  (minimalFundamentalBasis R i₀ hdim).equivFun

theorem minimalFundamentalBasis_coord {d n : ℕ} (i₀ : Fin n) (hdim : 0 < d+n)
    (σ : Equiv.Perm (Fin n)) :
    (minimalFundamentalBasis R i₀ hdim).coord σ =
      (minimalCellCoefficient R i₀ σ hdim).hom := by
  classical
  apply (minimalFundamentalBasis R i₀ hdim).ext
  intro τ
  change (minimalFundamentalBasis R i₀ hdim).repr
    (minimalFundamentalBasis R i₀ hdim τ) σ = _
  rw [Module.Basis.repr_self_apply,minimalFundamentalBasis_apply,
    minimalFundamentalClass_coefficient]

/-- The basis coordinates are exactly the previously constructed genuine
cell-retraction coefficients. -/
@[simp] theorem minimalTopHomologyLinearEquiv_apply {d n : ℕ} (i₀ : Fin n)
    (hdim : 0 < d+n) (z : Habs R (d+n) (TopCat.of (minimalSkeleton d n)))
    (σ : Equiv.Perm (Fin n)) :
    minimalTopHomologyLinearEquiv R i₀ hdim z σ = minimalCellCoefficient R i₀ σ hdim z := by
  exact congrArg (fun f : Habs R (d+n) (TopCat.of (minimalSkeleton d n)) →ₗ[R] R => f z)
    (minimalFundamentalBasis_coord R i₀ hdim σ)

theorem minimalFundamentalClass_sum_coeff {d n : ℕ} (i₀ : Fin n) (hdim : 0 < d+n)
    (z : Habs R (d+n) (TopCat.of (minimalSkeleton d n))) :
    ∑ σ : Equiv.Perm (Fin n),
      minimalCellCoefficient R i₀ σ hdim z • minimalFundamentalClass R i₀ σ hdim = z := by
  have h := (minimalFundamentalBasis R i₀ hdim).sum_repr z
  change (∑ σ : Equiv.Perm (Fin n),
    (minimalFundamentalBasis R i₀ hdim).coord σ z •
      minimalFundamentalBasis R i₀ hdim σ) = z at h
  simpa only [minimalFundamentalBasis_coord,minimalFundamentalBasis_apply] using h

/-- Every positive homological degree away from the genuine cell dimension
vanishes on the actual minimal skeleton. -/
theorem isZero_Habs_minimalSkeleton_off_top {d n : ℕ} (i₀ : Fin n)
    (k : ℕ) (hk : k ≠ 0) (hkn : k ≠ d+n) :
    IsZero (Habs R k (TopCat.of (minimalSkeleton d n))) := by
  have hr := iSup_range_minimalCellInclusionMap_eq_top R (d := d) i₀ k hk
  have hz (σ : Equiv.Perm (Fin n)) :
      HabsMap R k (minimalCellInclusionMap (d := d) i₀ σ) = 0 := by
    have hs := IsZero.of_iso (isZero_Habs_sphere_off_top R k (d+n) hk hkn)
      (HabsIsoOfHomotopyEquiv R k (verticalCellSphere d n σ).toHomotopyEquiv)
    exact hs.eq_zero_of_src _
  have ht : (⊤ : Submodule R (Habs R k (TopCat.of (minimalSkeleton d n)))) = ⊥ := by
    rw [← hr]
    simp [hz]
  apply (IsZero.iff_id_eq_zero _).mpr
  ext x
  change x = 0
  have hx : x ∈ (⊥ : Submodule R (Habs R k (TopCat.of (minimalSkeleton d n)))) := by
    rw [← ht]
    exact Submodule.mem_top
  simpa only [Submodule.mem_bot] using hx

/-- The canonical pair quotient is a homology isomorphism in every
positive degree for a nonempty contractible subspace, including degree one. -/
def relativeOfContractiblePositiveIso (q : ℕ) {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] :
    Habs R (q+1) X ≅ Hrel R (q+1) i := by
  have hi : relIota R (q+1) i = 0 :=
    (isZero_Habs_of_contractible R (q+1) (by omega) A).eq_zero_of_src _
  have hd : relδ R q i = 0 := by
    cases q with
    | zero =>
      let cX := homologyPointCollapse X
      have he : HabsMap R 0 i ≫ HabsMap R 0 cX = HabsMap R 0 (homologyPointCollapse A) := by
        rw [← HabsMap_comp]
        rfl
      letI : IsIso (HabsMap R 0 i ≫ HabsMap R 0 cX) := by
        rw [he]
        exact isIso_HabsMap_zero_of_pathConnected R _
      letI : Mono (HabsMap R 0 i) := mono_of_mono (HabsMap R 0 i) (HabsMap R 0 cX)
      exact (pair_exact_δ_iota R 0 i).mono_g_iff.mp inferInstance
    | succ q =>
      exact (isZero_Habs_of_contractible R (q+1) (by omega) A).eq_zero_of_tgt _
  letI : Mono (relJ R (q+1) i) := (pair_exact_iota_j R (q+1) i).mono_g hi
  letI : Epi (relJ R (q+1) i) := (pair_exact_j_δ R q i).epi_f hd
  letI : IsIso (relJ R (q+1) i) := isIso_of_mono_of_epi _
  exact asIso (relJ R (q+1) i)

end RingCoefficients

section Relative
variable (R : Type) [CommRing R]

/-- The actual lowest relative group is exhausted by the images of the
actual minimal-cell fundamental classes under the canonical pair quotient. -/
theorem span_minimalRelativeFundamentalClass_eq_top {d n : ℕ} [NeZero n]
    (hd : 0 < d) (i₀ : Fin n) :
    Submodule.span R (Set.range (fun σ : Equiv.Perm (Fin n) =>
      minimalRelativeFundamentalClass R hd i₀ σ)) = ⊤ := by
  let e := minimalFuksRelativeIso R d n hd
  have he : Set.range (fun σ : Equiv.Perm (Fin n) =>
      minimalRelativeFundamentalClass R hd i₀ σ) =
      e.hom '' Set.range (fun σ : Equiv.Perm (Fin n) =>
        minimalFundamentalClass R (d := d) i₀ σ (by omega)) := by
    ext z
    constructor
    · rintro ⟨σ,rfl⟩
      exact ⟨minimalFundamentalClass R (d := d) i₀ σ (by omega),⟨σ,rfl⟩,rfl⟩
    · rintro ⟨x,⟨σ,rfl⟩,rfl⟩
      exact ⟨σ,rfl⟩
  rw [he,← Submodule.map_span,span_minimalFundamentalClass_eq_top R i₀ (by omega),
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

def minimalRelativeFundamentalBasis {d n : ℕ} [NeZero n] (hd : 0 < d) (i₀ : Fin n) :
    Module.Basis (Equiv.Perm (Fin n)) R
      ((fuksRelativeComplex R (d := d) (n := n)
        (show d-1 ≤ d by omega)).homology (d+n)) :=
  (minimalFundamentalBasis R (d := d) i₀ (by omega)).map
    (minimalFuksRelativeIso R d n hd).toLinearEquiv

@[simp] theorem minimalRelativeFundamentalBasis_apply {d n : ℕ} [NeZero n]
    (hd : 0 < d) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    minimalRelativeFundamentalBasis R hd i₀ σ = minimalRelativeFundamentalClass R hd i₀ σ := by
  rw [minimalRelativeFundamentalBasis,Module.Basis.map_apply,minimalFundamentalBasis_apply]
  rfl

def minimalRelativeTopHomologyLinearEquiv {d n : ℕ} [NeZero n] (hd : 0 < d) (i₀ : Fin n) :
    ((fuksRelativeComplex R (d := d) (n := n)
      (show d-1 ≤ d by omega)).homology (d+n)) ≃ₗ[R] (Equiv.Perm (Fin n) → R) :=
  (minimalRelativeFundamentalBasis R hd i₀).equivFun

/-- The absolute-to-relative comparison on the actual lowest Fuks level
in every positive degree. -/
def minimalFuksRelativePositiveIso (q d n : ℕ) [NeZero n] (hd : 0 < d) :
    Habs R (q+1) (TopCat.of (minimalSkeleton d n)) ≅
      (fuksRelativeComplex R (d := d) (n := n)
        (show d-1 ≤ d by omega)).homology (q+1) := by
  letI := contractible_lowerFuksLevel d n hd
  exact HabsIsoOfHomotopyEquiv R (q+1) (minimalLevelHomeomorph d n).toHomotopyEquiv ≪≫
    relativeOfContractiblePositiveIso R q
      (compactifiedFuksInclusion (d := d) (n := n) (show d-1 ≤ d by omega))

theorem isZero_minimalFuksRelative_off_top {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (k : ℕ) (hk : k ≠ 0) (hkn : k ≠ d+n) :
    IsZero ((fuksRelativeComplex R (d := d) (n := n)
      (show d-1 ≤ d by omega)).homology k) := by
  cases k with
  | zero => contradiction
  | succ q =>
    exact IsZero.of_iso (isZero_Habs_minimalSkeleton_off_top R (d := d) i₀ (q+1) hk hkn)
      (minimalFuksRelativePositiveIso R q d n hd).symm

end Relative

end NRR.PrimePowerTopology
