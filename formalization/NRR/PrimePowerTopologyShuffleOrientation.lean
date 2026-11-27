import NRR.PrimePowerTopologyTwoColumnModTwo
import NRR.PrimePowerTopologyOrientationRows
import NRR.PrimePowerTopologyTwoColumnBoundaryGraph
import NRR.PrimePowerTopologyChamberCollapseOrientation

/-! Coordinate orientation of the local boundary-face charts used by the
actual two-column shuffle incidences. -/

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory
open NRR.SingularHomology NRR.SingularHomology.FiniteCellAttachment
open NRR.PrimePower

namespace NRR.PrimePowerTopology

/-- The local boundary-face coordinates consist of all common coordinates
and all labelled heights, in their original label order. -/
def shuffleFaceCoordinatesRelabel {d n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    (Space (d+1) × (Fin n → ℝ)) →ₗ[ℝ] (Space (d+1) × (Fin n → ℝ)) :=
  LinearMap.prodMap LinearMap.id (labelPermutationLinear ρ).toLinearMap

/-- Reordering the full height-coordinate block has determinant exactly the
permutation sign; the column inequalities play no role in this calculation. -/
theorem det_shuffleFaceCoordinatesRelabel {d n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    LinearMap.det (shuffleFaceCoordinatesRelabel (d := d) ρ) =
      (Equiv.Perm.sign ρ : ℝ) := by
  rw [shuffleFaceCoordinatesRelabel, LinearMap.det_prodMap,
    LinearMap.det_id, one_mul, det_labelPermutationLinear]

/-- Exact orientation character for comparing shuffle charts: the full
height block contributes `sign ρ`; the source/target orientation-row ratio
is the same character, so their product is positive. -/
theorem shuffleFace_coordinate_orientation_cancellation {d n : ℕ} [NeZero n]
    (ρ : Equiv.Perm (Fin n)) :
    LinearMap.det (shuffleFaceCoordinatesRelabel (d := d) ρ) *
      (LinearMap.det (ambientRelabel (d+1) ρ).toLinearMap /
        LinearMap.det (relabelValues (d := d+1) ρ).toLinearEquiv.toLinearMap) = 1 := by
  rw [det_shuffleFaceCoordinatesRelabel, source_target_orientation_ratio]
  rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> simp [h]

/-- On the actual chamber charts, the source coordinate permutation is the
height relabeling that carries the σ-chamber to the ρ*σ-chamber. -/
theorem shuffleFaceCoordinatesRelabel_apply {d n : ℕ}
    (ρ σ : Equiv.Perm (Fin n)) (u : Space (d+1))
    (t : heightChamber n σ) :
    shuffleFaceCoordinatesRelabel (d := d) ρ (u, t.val) =
      (u, (heightChamberRelabel ρ σ t).val) := rfl

/-- The coordinate permutation restricted to ordered-height chambers. It is
defined for any two chamber labels; shuffle hypotheses are needed only when
the chambers are used as actual boundary charts. -/
def shuffleFaceChartRelabel {d n : ℕ} (ρ σ : Equiv.Perm (Fin n)) :
    (Space (d+1) × heightChamber n σ) ≃ₜ
      (Space (d+1) × heightChamber n (ρ*σ)) :=
  (Homeomorph.refl (Space (d+1))).prodCongr (heightChamberRelabel ρ σ)

/-- The actual boundary chart and the target cell chart are compatible with
the same local height-coordinate permutation. -/
theorem twoColumnBoundaryMinimalMap_chart_relabel
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (ρ σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ)
    (hs' : IsColumnShuffle S (ρ*σ))
    (p : Space (d+1) × heightChamber n σ) :
    minimalSkeletonRelabelMap ρ
        (twoColumnBoundaryMinimalMap S iL iR hL hR
          (twoColumnShuffleBoundaryChart S σ hs p)) =
      twoColumnBoundaryMinimalMap S iL iR hL hR
        (twoColumnShuffleBoundaryChart S (ρ*σ) hs'
          (shuffleFaceChartRelabel ρ σ p)) := by
  rw [twoColumnBoundaryMinimalMap_shuffleChart,
    twoColumnBoundaryMinimalMap_shuffleChart]
  have h := congrArg (fun f => f (p : OnePoint (Space (d+1) × heightChamber n σ)))
    (minimalCellInclusionMap_relabel i₀ ρ σ)
  change minimalSkeletonRelabelMap ρ
      (minimalCellInclusion i₀ σ (p : OnePoint (Space (d+1) × heightChamber n σ))) =
    minimalCellInclusion i₀ (ρ*σ)
      (compactifiedCellRelabel ρ σ (p : OnePoint (Space (d+1) × heightChamber n σ))) at h
  simpa [shuffleFaceChartRelabel, compactifiedCellRelabel] using h

/-- The restriction of the genuine attaching-then-pinch map to one chamber
chart is the standard finite-point route into that compactified cell. -/
def twoColumnShuffleChartRoute {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    C(Space (d+1) × heightChamber n σ,
      OnePoint (Space (d+1) × heightChamber n σ)) :=
  ⟨OnePoint.some, OnePoint.continuous_coe⟩

def twoColumnDiskShuffleFaceChart {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    C(Space (d+1) × heightChamber n σ,
      diskBoundary (TwoColumnAmbientParameters d n)) :=
  (⟨twoColumnBoundaryDiskHomeomorph (canonicalColumnLabels split),
    (twoColumnBoundaryDiskHomeomorph (canonicalColumnLabels split)).continuous⟩ :
      C(twoColumnCharacteristicBoundary (canonicalColumnLabels split),
        diskBoundary (TwoColumnAmbientParameters d n))).comp
    (twoColumnShuffleBoundaryChart (canonicalColumnLabels split) σ hs)

theorem twoColumnDiskAttachingSphereMinimalPinch_chart_route
    {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1)).comp
        (twoColumnDiskShuffleFaceChart split σ hs) =
      twoColumnShuffleChartRoute σ := by
  have h := twoColumnDiskAttachingSphereMinimalPinch_boundaryChart
    (d := d) split i₀ σ
  ext p
  change (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1))
      ((twoColumnBoundaryDiskHomeomorph (canonicalColumnLabels split))
        (twoColumnShuffleBoundaryChart (canonicalColumnLabels split) σ hs p)) = _
  calc
    _ = twoColumnShuffleIncidenceMap (d := d) (canonicalColumnLabels split)
        0 split.val (zero_mem_canonicalColumnLabels split)
        (split_not_mem_canonicalColumnLabels split) i₀ σ
        (twoColumnShuffleBoundaryChart (canonicalColumnLabels split) σ hs p) := by
          simpa only [ContinuousMap.comp_apply] using
            congrArg (fun f => f
              (twoColumnShuffleBoundaryChart (canonicalColumnLabels split) σ hs p)) h
    _ = (p : OnePoint (Space (d+1) × heightChamber n σ)) :=
      twoColumnShuffleIncidenceMap_chart (canonicalColumnLabels split)
        0 split.val (zero_mem_canonicalColumnLabels split)
        (split_not_mem_canonicalColumnLabels split) i₀ σ hs p

/-- The homology map of the actual attaching sphere factors through each
regular-value chamber chart as the standard chart route. -/
theorem HabsMap_twoColumnDiskAttachingSphereMinimalPinch_chart_route
    (R : Type) [Ring R] {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) (q : ℕ) :
    HabsMap R q (TopCat.ofHom (twoColumnDiskShuffleFaceChart split σ hs)) ≫
        HabsMap R q (TopCat.ofHom
          (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1))) =
      HabsMap R q (TopCat.ofHom (twoColumnShuffleChartRoute (d := d) σ)) := by
  have h : TopCat.ofHom (twoColumnDiskShuffleFaceChart split σ hs) ≫
      TopCat.ofHom (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1)) =
      TopCat.ofHom (twoColumnShuffleChartRoute (d := d) σ) := by
    exact congrArg TopCat.ofHom
      (twoColumnDiskAttachingSphereMinimalPinch_chart_route split i₀ σ hs)
  rw [← HabsMap_comp, h]

/-- The chart route commutes with the actual relabeling of the target cell. -/
def shuffleFaceChartRelabelMap {d n : ℕ} (ρ σ : Equiv.Perm (Fin n)) :
    TopCat.of (Space (d+1) × heightChamber n σ) ⟶
      TopCat.of (Space (d+1) × heightChamber n (ρ*σ)) :=
  TopCat.ofHom ⟨shuffleFaceChartRelabel ρ σ,
    (shuffleFaceChartRelabel ρ σ).continuous⟩

theorem twoColumnShuffleChartRoute_relabel {d n : ℕ}
    (ρ σ : Equiv.Perm (Fin n)) :
    TopCat.ofHom (twoColumnShuffleChartRoute (d := d) σ) ≫
        compactifiedCellRelabelMap ρ σ =
      shuffleFaceChartRelabelMap ρ σ ≫
        TopCat.ofHom (twoColumnShuffleChartRoute (d := d) (ρ*σ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-- The chart-route square remains a commuting square after applying actual
singular homology, providing the local homology factorization used for a
comparison of incidence amplitudes. -/
theorem HabsMap_twoColumnShuffleChartRoute_relabel (R : Type) [Ring R]
    {d n : ℕ} (ρ σ : Equiv.Perm (Fin n)) (q : ℕ) :
    HabsMap R q (TopCat.ofHom (twoColumnShuffleChartRoute (d := d) σ)) ≫
        HabsMap R q (compactifiedCellRelabelMap ρ σ) =
      HabsMap R q (shuffleFaceChartRelabelMap ρ σ) ≫
        HabsMap R q (TopCat.ofHom (twoColumnShuffleChartRoute (d := d) (ρ*σ))) := by
  rw [← HabsMap_comp, ← HabsMap_comp, twoColumnShuffleChartRoute_relabel]

/-- The source and target local charts use the same full height block, so
their coordinate-permutation orientation characters cancel in the ratio. -/
theorem shuffleFace_source_target_chart_orientation_ratio {d n : ℕ}
    (ρ : Equiv.Perm (Fin n)) :
    LinearMap.det (shuffleFaceCoordinatesRelabel (d := d) ρ) /
      LinearMap.det (shuffleFaceCoordinatesRelabel (d := d) ρ) = 1 := by
  rw [det_shuffleFaceCoordinatesRelabel]
  have hsign : (Equiv.Perm.sign ρ : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> simp [h]
  exact div_self hsign

private theorem isUnit_iso_apply_one (R : Type) [CommRing R]
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

/-- The actual integral incidence of every valid shuffle is a signed unit.
This establishes its two possible integral values without choosing which
orientation sign occurs. -/
theorem twoColumnDiskIncidenceCoefficient_int_eq_one_or_neg_one
    {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    (twoColumnDiskIncidenceCoefficient ℤ (d := d) split i₀ σ).hom 1 = 1 ∨
      (twoColumnDiskIncidenceCoefficient ℤ (d := d) split i₀ σ).hom 1 = -1 := by
  letI := isIso_twoColumnDiskIncidenceCoefficient ℤ (d := d) split i₀ σ hs
  let e := asIso (twoColumnDiskIncidenceCoefficient ℤ (d := d) split i₀ σ)
  have hu : IsUnit (e.hom 1) := isUnit_iso_apply_one ℤ e
  change e.hom 1 = 1 ∨ e.hom 1 = -1
  rcases hu with ⟨u, hu⟩
  rcases Int.units_eq_one_or u with h | h
  · left
    calc
      e.hom 1 = ↑u := hu.symm
      _ = 1 := by rw [h]; norm_num
  · right
    calc
      e.hom 1 = ↑u := hu.symm
      _ = -1 := by rw [h]; norm_num

private theorem onePoint_eq_of_coe_fibers {X : Type} (x y : OnePoint X)
    (h : ∀ p : X, x = (p : OnePoint X) ↔ y = (p : OnePoint X)) : x = y := by
  induction x using OnePoint.rec with
  | infty =>
      induction y using OnePoint.rec with
      | infty => rfl
      | coe p => exact False.elim (OnePoint.infty_ne_coe p ((h p).mpr rfl))
  | coe p => exact ((h p).mp rfl).symm

/-- In the common graph coordinates on the entire characteristic boundary,
the actual attaching-then-pinch map is exactly the ordinary chamber collapse. -/
theorem twoColumnShuffleIncidenceMap_graph_factor {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    TopCat.ofHom (twoColumnBoundaryGraphHomeomorph (d := d) S).toHomotopyEquiv.toFun ≫
      TopCat.ofHom (twoColumnShuffleIncidenceMap S iL iR hL hR i₀ σ) =
        TopCat.ofHom (minimalChamberOnePointCollapse (d := d+1) σ) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply onePoint_eq_of_coe_fibers
  intro p
  change twoColumnShuffleIncidenceMap S iL iR hL hR i₀ σ
      (twoColumnBoundaryGraphHomeomorph S x) = (p : OnePoint _) ↔
    minimalChamberOnePointCollapse σ x = (p : OnePoint _)
  rw [twoColumnShuffleIncidenceMap_fiber_coe S iL iR hL hR i₀ σ hs,
    minimalChamberOnePointCollapse_fiber_coe]
  rw [← twoColumnBoundaryGraphHomeomorph_shuffle S σ hs p]
  exact ⟨fun h => (twoColumnBoundaryGraphHomeomorph S).injective h,
    congrArg (twoColumnBoundaryGraphHomeomorph S)⟩

/-- After coherent transport of the target-cell orientation, the sign of
every genuine shuffle incidence is the integral permutation sign times
the same common-face amplitude. -/
theorem twoColumnShuffleIncidenceMap_coherent_sign (R : Type) [CommRing R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    HabsMap R ((d+1)+n) (TopCat.ofHom
      (twoColumnShuffleIncidenceMap (d := d) S iL iR hL hR i₀ σ)) ≫
        (coherentCellTopHomologyIso R σ (by omega)).hom =
      (Equiv.Perm.sign σ : ℤ) •
        ((HabsIsoOfHomotopyEquiv R ((d+1)+n)
          (twoColumnBoundaryGraphHomeomorph (d := d) S).toHomotopyEquiv).inv ≫
          HabsMap R ((d+1)+n) (TopCat.ofHom
            (minimalChamberOnePointCollapse (d := d+1) 1)) ≫
              (minimalCellTopHomologyIso R (d+1) n 1 (by omega)).hom) := by
  let e := HabsIsoOfHomotopyEquiv R ((d+1)+n)
    (twoColumnBoundaryGraphHomeomorph (d := d) S).toHomotopyEquiv
  apply (cancel_epi e.hom).mp
  have h := congrArg (HabsMap R ((d+1)+n))
    (twoColumnShuffleIncidenceMap_graph_factor (d := d) S iL iR hL hR i₀ σ hs)
  rw [HabsMap_comp] at h
  change e.hom ≫ HabsMap R ((d+1)+n) (TopCat.ofHom
      (twoColumnShuffleIncidenceMap (d := d) S iL iR hL hR i₀ σ)) =
    HabsMap R ((d+1)+n) (TopCat.ofHom
      (minimalChamberOnePointCollapse (d := d+1) σ)) at h
  change e.hom ≫ (HabsMap R ((d+1)+n) _ ≫ _) = _
  rw [← Category.assoc, h, minimalChamberCollapse_coherent_sign]
  simp only [e, Preadditive.comp_zsmul, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

end NRR.PrimePowerTopology
