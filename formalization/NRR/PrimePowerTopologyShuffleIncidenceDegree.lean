import NRR.PrimePowerTopologyTwoColumnBoundaryCharts
import NRR.SingularHomologyLocalComparison

/-! The actual attaching map followed by the geometric minimal-cell pinch
has unit local homological degree at every valid shuffle. No orientation
or choice of the sign of that degree is asserted here. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Metric Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

/-- A finite point of a selected minimal cell has just one preimage under
the genuine geometric pinch of the minimal skeleton. -/
theorem minimalCellRetraction_fiber_coe {d n : ℕ} (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (p : Space d × heightChamber n σ)
    (z : minimalSkeleton d n) :
    minimalCellRetraction i₀ σ z = (p : OnePoint (Space d × heightChamber n σ)) ↔
      z = minimalCellInclusion i₀ σ (p : OnePoint (Space d × heightChamber n σ)) := by
  classical
  constructor
  · intro hz
    obtain ⟨⟨τ,q⟩,rfl⟩ := minimalWedgeProjection_surjective i₀ z
    change minimalCellRetraction i₀ σ (minimalCellInclusion i₀ τ q) = _ at hz
    by_cases h : τ = σ
    · subst τ
      rw [minimalCellRetraction_same] at hz
      exact congrArg (minimalCellInclusion i₀ σ) hz
    · rw [minimalCellRetraction_other i₀ σ τ h] at hz
      exact False.elim ((OnePoint.infty_ne_coe p) hz)
  · rintro rfl
    exact minimalCellRetraction_same i₀ σ (p : OnePoint (Space d × heightChamber n σ))

/-- The actual characteristic boundary map, with its genuine lowest
filtration level expressed as the minimal skeleton. -/
def twoColumnBoundaryMinimalMap {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    C(twoColumnCharacteristicBoundary (d := d) S, minimalSkeleton (d+1) n) where
  toFun z := ⟨(twoColumnCharacteristicBoundaryMap S iL iR hL hR z).val, by
    simpa only [compactifiedFuksLevel_minimal] using
      (twoColumnCharacteristicBoundaryMap S iL iR hL hR z).property⟩
  continuous_toFun := (continuous_subtype_val.comp
    (twoColumnCharacteristicBoundaryMap S iL iR hL hR).continuous).subtype_mk _

/-- Attach the actual boundary, then pinch all the other minimal cells to
their common point at infinity. -/
def twoColumnShuffleIncidenceMap {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    C(twoColumnCharacteristicBoundary (d := d) S,
      OnePoint (Space (d+1) × heightChamber n σ)) :=
  (minimalCellRetraction i₀ σ).comp (twoColumnBoundaryMinimalMap S iL iR hL hR)

theorem twoColumnBoundaryMinimalMap_shuffleChart {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ)
    (p : Space (d+1) × heightChamber n σ) :
    twoColumnBoundaryMinimalMap S iL iR hL hR
        (twoColumnShuffleBoundaryChart S σ hs p) =
      minimalCellInclusion i₀ σ (p : OnePoint (Space (d+1) × heightChamber n σ)) := by
  apply Subtype.ext
  exact twoColumnShuffleBoundaryChart_attaching S σ hs iL iR hL hR i₀ p

@[simp] theorem twoColumnShuffleIncidenceMap_chart {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ)
    (p : Space (d+1) × heightChamber n σ) :
    twoColumnShuffleIncidenceMap S iL iR hL hR i₀ σ
        (twoColumnShuffleBoundaryChart S σ hs p) =
      (p : OnePoint (Space (d+1) × heightChamber n σ)) := by
  change minimalCellRetraction i₀ σ
    (twoColumnBoundaryMinimalMap S iL iR hL hR
      (twoColumnShuffleBoundaryChart S σ hs p)) = _
  rw [twoColumnBoundaryMinimalMap_shuffleChart S iL iR hL hR i₀ σ hs,
    minimalCellRetraction_same]

/-- All boundary points, including collision faces and infinity, are
accounted for in this singleton-fiber computation. -/
theorem twoColumnShuffleIncidenceMap_fiber_coe {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ)
    (p : Space (d+1) × heightChamber n σ)
    (z : twoColumnCharacteristicBoundary (d := d) S) :
    twoColumnShuffleIncidenceMap S iL iR hL hR i₀ σ z =
        (p : OnePoint (Space (d+1) × heightChamber n σ)) ↔
      z = twoColumnShuffleBoundaryChart S σ hs p := by
  constructor
  · intro hz
    have hm := (minimalCellRetraction_fiber_coe i₀ σ p
      (twoColumnBoundaryMinimalMap S iL iR hL hR z)).mp hz
    apply Subtype.ext
    exact (compactTwoColumnAttaching_fiber_minimalCell S iL iR hL hR
      σ hs i₀ p z.val).mp (congrArg Subtype.val hm)
  · rintro rfl
    exact twoColumnShuffleIncidenceMap_chart S iL iR hL hR i₀ σ hs p

private def linearUnitSphereHomeomorph {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 where
  toFun x := ⟨‖e x.val‖⁻¹ • e x.val, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr
      (fun h => (ne_of_mem_sphere x.property one_ne_zero) (e.injective (h.trans (map_zero e).symm))))⟩
  invFun y := ⟨‖e.symm y.val‖⁻¹ • e.symm y.val, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr
      (fun h => (ne_of_mem_sphere y.property one_ne_zero)
        (e.symm.injective (h.trans (map_zero e.symm).symm))))⟩
  left_inv x := by
    apply Subtype.ext
    have hx : ‖e x.val‖ ≠ 0 := norm_ne_zero_iff.mpr
      (fun h => (ne_of_mem_sphere x.property one_ne_zero) (e.injective (h.trans (map_zero e).symm)))
    simp only [map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_smul,
      norm_inv, norm_norm, norm_eq_of_mem_sphere x, mul_one, inv_inv,
      smul_smul, mul_inv_cancel₀ hx, one_smul]
  right_inv y := by
    apply Subtype.ext
    have hy : ‖e.symm y.val‖ ≠ 0 := norm_ne_zero_iff.mpr
      (fun h => (ne_of_mem_sphere y.property one_ne_zero)
        (e.symm.injective (h.trans (map_zero e.symm).symm)))
    simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply, norm_smul,
      norm_inv, norm_norm, norm_eq_of_mem_sphere y, mul_one, inv_inv,
      smul_smul, mul_inv_cancel₀ hy, one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · exact (e.continuous.comp continuous_subtype_val).norm.inv₀ (fun x =>
        norm_ne_zero_iff.mpr (fun h => (ne_of_mem_sphere x.property one_ne_zero)
          (e.injective (h.trans (map_zero e).symm))))
    · exact e.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · exact (e.symm.continuous.comp continuous_subtype_val).norm.inv₀ (fun y =>
        norm_ne_zero_iff.mpr (fun h => (ne_of_mem_sphere y.property one_ne_zero)
          (e.symm.injective (h.trans (map_zero e.symm).symm))))
    · exact e.symm.continuous.comp continuous_subtype_val

private def sphereInClosedBallHomeomorph (E : Type) [NormedAddCommGroup E] :
    {q : closedBall (0 : E) 1 // ‖q.val‖ = 1} ≃ₜ sphere (0 : E) 1 where
  toFun q := ⟨q.val.val, by simpa only [mem_sphere_zero_iff_norm] using q.property⟩
  invFun y := ⟨⟨y.val, by
    rw [mem_closedBall_zero_iff]
    exact (norm_eq_of_mem_sphere y).le⟩, norm_eq_of_mem_sphere y⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The real characteristic boundary is a Euclidean metric sphere of the
dimension of a minimal cell. The product norm in its disk presentation
is handled by radial normalization of a continuous linear equivalence. -/
def twoColumnCharacteristicBoundarySphere {d n : ℕ} (S : Finset (Fin n)) :
    twoColumnCharacteristicBoundary (d := d) S ≃ₜ Sph (d+n+1) := by
  let e : TwoColumnAmbientParameters d n ≃L[ℝ] Space (d+n+2) :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
      rw [finrank_twoColumnAmbientParameters]
      simp)).some
  exact ((twoColumnDiskHomeomorph S).subtype (fun x =>
    (twoColumnDiskHomeomorph_boundary_iff S x).symm)).trans
    ((sphereInClosedBallHomeomorph _).trans (linearUnitSphereHomeomorph e))

theorem contractibleSpace_compl_point_of_sphere_homeomorph
    {X : Type} [TopologicalSpace X] (m : ℕ) (e : X ≃ₜ Sph m) (x : X) :
    ContractibleSpace ({x}ᶜ : Set X) := by
  have hn : -(-(e x)) = e x := by
    apply Subtype.ext
    simp
  let h : {y : Sph m // y ≠ e x} ≃ₜ {y : Sph m // y ≠ -(-(e x))} :=
    Homeomorph.setCongr (by rw [hn])
  exact ((puncturedHomeomorph e x).trans
    (h.trans (puncturedSphereChart m (-(e x))))).contractibleSpace

theorem contractibleSpace_twoColumnCharacteristicBoundary_punctured {d n : ℕ}
    (S : Finset (Fin n)) (x : twoColumnCharacteristicBoundary (d := d) S) :
    ContractibleSpace ({x}ᶜ : Set (twoColumnCharacteristicBoundary (d := d) S)) :=
  contractibleSpace_compl_point_of_sphere_homeomorph (d+n+1)
    (twoColumnCharacteristicBoundarySphere S) x

theorem contractibleSpace_minimalCell_punctured (d n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : OnePoint (Space d × heightChamber n σ)) :
    ContractibleSpace ({x}ᶜ : Set (OnePoint (Space d × heightChamber n σ))) :=
  contractibleSpace_compl_point_of_sphere_homeomorph (d+n) (verticalCellSphere d n σ) x

/-- For every valid shuffle, the actual attaching boundary followed by
the geometric pinch induces an isomorphism in every positive ordinary
singular homology degree, with arbitrary ring coefficients. -/
theorem isIso_HabsMap_twoColumnShuffleIncidence (R : Type) [Ring R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) (q : ℕ) :
    IsIso (HabsMap R (q+1)
      (TopCat.ofHom (twoColumnShuffleIncidenceMap (d := d) S iL iR hL hR i₀ σ))) := by
  obtain ⟨t,ht⟩ := heightChamber_nonempty n σ
  let p : Space (d+1) × heightChamber n σ := (0,⟨t,ht⟩)
  let u := twoColumnShuffleBoundaryChart (d := d) S σ hs
  let v : C(Space (d+1) × heightChamber n σ,
      OnePoint (Space (d+1) × heightChamber n σ)) :=
    ⟨OnePoint.some, OnePoint.continuous_coe⟩
  letI := contractibleSpace_twoColumnCharacteristicBoundary_punctured S (u p)
  letI := contractibleSpace_minimalCell_punctured (d+1) n σ (v p)
  exact isIso_HabsMap_of_open_chart R
    (twoColumnShuffleIncidenceMap S iL iR hL hR i₀ σ) u v
    (isOpenEmbedding_twoColumnShuffleBoundaryChart S σ hs)
    OnePoint.isOpenEmbedding_coe
    (twoColumnShuffleIncidenceMap_chart S iL iR hL hR i₀ σ hs) p
    (fun z hz => (twoColumnShuffleIncidenceMap_fiber_coe S iL iR hL hR i₀ σ hs p z).mp hz) q

/-- A choice of fundamental class for the actual attaching boundary. -/
def twoColumnBoundaryTopHomologyIso (R : Type) [Ring R]
    {d n : ℕ} (S : Finset (Fin n)) :
    Habs R (d+n+1) (TopCat.of (twoColumnCharacteristicBoundary (d := d) S)) ≅
      ModuleCat.of R R :=
  HabsIsoOfHomotopyEquiv R (d+n+1)
    (twoColumnCharacteristicBoundarySphere S).toHomotopyEquiv ≪≫
      sphereTopHomologyIso R (d+n)

private def shuffleTargetTopHomologyIso (R : Type) [Ring R]
    (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Habs R (d+n+1) (TopCat.of (OnePoint (Space (d+1) × heightChamber n σ))) ≅
      ModuleCat.of R R := by
  simpa only [Nat.add_right_comm d 1 n] using
    minimalCellTopHomologyIso R (d+1) n σ (by omega)

/-- The coefficient of the actual attaching-then-pinch map in the chosen
fundamental classes of its source and target spheres. -/
def twoColumnShuffleIncidenceCoefficient (R : Type) [Ring R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  (twoColumnBoundaryTopHomologyIso R S).inv ≫
    HabsMap R (d+n+1)
      (TopCat.ofHom (twoColumnShuffleIncidenceMap S iL iR hL hR i₀ σ)) ≫
        (shuffleTargetTopHomologyIso R d n σ).hom

def twoColumnShuffleLocalDegree (R : Type) [Ring R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) : R :=
  twoColumnShuffleIncidenceCoefficient R (d := d) S iL iR hL hR i₀ σ 1

private theorem isUnit_iso_apply_one (R : Type) [Ring R]
    (e : ModuleCat.of R R ≅ ModuleCat.of R R) : IsUnit (e.hom 1) := by
  have h₁ : e.hom 1 * e.inv 1 = 1 := by
    have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
      e.hom_inv_id
    change e.inv (e.hom 1) = 1 at h
    have hm : e.inv (e.hom 1) = e.hom 1 * e.inv 1 := by
      simpa only [smul_eq_mul, mul_one] using e.inv.hom.map_smul (e.hom 1) (1 : R)
    exact hm.symm.trans h
  have h₂ : e.inv 1 * e.hom 1 = 1 := by
    have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
      e.inv_hom_id
    change e.hom (e.inv 1) = 1 at h
    have hm : e.hom (e.inv 1) = e.inv 1 * e.hom 1 := by
      simpa only [smul_eq_mul, mul_one] using e.hom.hom.map_smul (e.inv 1) (1 : R)
    exact hm.symm.trans h
  exact ⟨⟨e.hom 1, e.inv 1, h₁, h₂⟩, rfl⟩

/-- A valid shuffle has unit local degree. In particular its integral
degree is a unit; this statement does not choose an orientation sign. -/
theorem isUnit_twoColumnShuffleLocalDegree (R : Type) [Ring R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    IsUnit (twoColumnShuffleLocalDegree R (d := d) S iL iR hL hR i₀ σ) := by
  letI := isIso_HabsMap_twoColumnShuffleIncidence R (d := d) S iL iR hL hR i₀ σ hs (d+n)
  letI : IsIso (twoColumnShuffleIncidenceCoefficient R (d := d) S iL iR hL hR i₀ σ) := by
    unfold twoColumnShuffleIncidenceCoefficient
    infer_instance
  exact isUnit_iso_apply_one R
    (asIso (twoColumnShuffleIncidenceCoefficient R (d := d) S iL iR hL hR i₀ σ))

end NRR.PrimePowerTopology
