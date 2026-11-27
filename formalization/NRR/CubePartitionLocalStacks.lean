import NRR.CubePartitionSpace
import NRR.CubeChartBounds
import NRR.CubeInternalMargins
import NRR.CubeClippedStack
import NRR.CubePolynomialTests

/-! Genuine equal-volume cube partitions admit the small affine-stack charts
needed for global rational four-moment polynomial exclusion. -/

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NRR.CubePartitionSpace

open Coordinates InterfaceChart CubeFourMomentReadout CubeMomentCorrection

/-- Forget full dimensionality but retain each actual compact cell. -/
def compactConfiguration {n : ℕ} (S : X n) :
    Fin n → NonemptyCompacts Ambient := fun i => (S.val i).val

theorem continuous_compactConfiguration (n : ℕ) :
    Continuous (compactConfiguration (n := n)) :=
  continuous_pi fun i => continuous_subtype_val.comp
    ((continuous_apply i).comp (continuous_subtype_val :
      Continuous (fun S : X n => S.val)))

theorem convex_partition {n : ℕ} (S : X n) :
    ConvexPartition cube (compactConfiguration S) :=
  ⟨cubeBody.property.1, fun i => (S.val i).property.1,
    fun i => (S.val i).property.2, (partition S).covers, (partition S).disjoint⟩

/-- Every zero-horizontal-moment reference has a genuine neighborhood of
small-slope stacks. No chart or moment identity is assumed in this theorem. -/
theorem local_stacks {r : ℕ} (δ : ℝ) (hδ : 0 < δ) (S : X (r+2))
    (zero : ∀ i, horizontal (cellMoment (r+2) i S) = 0) :
    ∀ᶠ T in 𝓝 S, ∃ (A : EqualVolumeStack (r+2))
      (σ : Equiv.Perm (Fin (r+2))),
      (∀ j, ‖A.slope j‖ ≤ δ) ∧
        ∀ i, cellMoment (r+2) (σ i) T = A.moments i := by
  classical
  choose a b positive repr using partition_is_slabs S zero
  have clips (i : Fin (r+2)) :
      (compactConfiguration S i : Set Ambient) ∩
        (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1) =
      CubeHorizontalRigidity.square ×ˢ Icc (a i) (b i) := by
    change bodyPoints (S.val i) ∩ cube = _
    rw [inter_eq_left.mpr (cell_subset S i), repr i]
  obtain ⟨h, hh, margin⟩ := CubeInternalMargins.exists_internal_margin
    (compactConfiguration S) (convex_partition S) a b positive clips
  let η : ℝ := (3 * (2 / (r+2 : ℕ) : ℝ)) * δ
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨σ, U, hU, memU, _, chart⟩ :=
    CubeChartBounds.exists_bounded_cube_graph_chart
      (compactConfiguration S) (convex_partition S) a b positive clips h hh margin η hη
  have nearby : ∀ᶠ T in 𝓝 S, compactConfiguration T ∈ U :=
    (hU.preimage (continuous_compactConfiguration (r+2))).mem_nhds memU
  filter_upwards [nearby] with T hT
  obtain ⟨P, chain, _, pcaps, scaps, bounds⟩ :=
    chart (compactConfiguration T) hT (convex_partition T)
  have zeroSquare : (0 : Space 2) ∈ CubeHorizontalRigidity.square := by
    intro j
    simp
  have small (i : Fin (r+1)) :
      ‖(P i).1‖ ≤ (3 * (2 / (r+2 : ℕ) : ℝ)) * δ :=
    (bounds i 0 zeroSquare).1
  have transported_volume (i : Fin (r+2)) :
      volume.real (CubePlaneCoordinates.E ''
        (compactConfiguration T (σ i) : Set Ambient)) =
      volume.real (bodyPoints (T.val (σ i))) := by
    simpa only [setIntegral_one_eq_measureReal] using
      CubePlaneCoordinates.setIntegral_image_E
        (bodyPoints (T.val (σ i))) (fun _ => (1 : ℝ))
  obtain ⟨A, slopes, cells⟩ := exists_stack_of_cube_caps
    (fun i => compactConfiguration T (σ i)) chain P
    (fun i => ⟨pcaps i, scaps i⟩)
    (fun i u hu => ⟨(bounds i u hu).2.1, (bounds i u hu).2.2⟩)
    hδ.le small (fun i j =>
      (transported_volume i).trans
        ((congrArg ENNReal.toReal (equal_volume T (σ i) (σ j))).trans
          (transported_volume j).symm))
  refine ⟨A, σ, slopes, ?_⟩
  intro i
  rw [cellMoment_apply]
  change volumeFourMoments (2 / (r+2 : ℕ))
    (CubePlaneCoordinates.E '' (compactConfiguration T (σ i) : Set Ambient)) = _
  rw [cells i]
  rfl

/-- A fixed pair of rational four-variable polynomials and a positive gap
exclude every actual three-dimensional equal-volume convex partition.
The quantifiers range over the full compact partition space. -/
theorem exists_rational_polynomials (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ S : X (r+2), ∃ i j k,
        γ < |RationalMomentApproximation.eval (P k)
          (fourCoordinates (cellMoment (r+2) i S)) -
          RationalMomentApproximation.eval (P k)
          (fourCoordinates (cellMoment (r+2) j S))| :=
  rational_cube_tests_of_local_stacks r hn (cellMoment (r+2))
    sum_horizontal (fun δ hδ S zero => local_stacks δ hδ S zero)


/-- For every non-prime-power n >= 2, one pair works on all genuine
three-dimensional cube partitions, with the explicit n/8 volume moments. -/
theorem exists_rational_polynomials_for_partitions (n : ℕ) (hn : 2 ≤ n)
    (hpow : ¬ IsPrimePow n) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ S : X n, ∃ i j k,
        γ < |RationalMomentApproximation.eval (P k)
          (CubeProductMoments.moments3 n
            (CubePlaneCoordinates.E '' bodyPoints (S.val i))) -
          RationalMomentApproximation.eval (P k)
          (CubeProductMoments.moments3 n
            (CubePlaneCoordinates.E '' bodyPoints (S.val j)))| := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+2 := ⟨n-2, (Nat.sub_add_cancel hn).symm⟩
  obtain ⟨P, γ, hγ, gap⟩ := exists_rational_polynomials r hpow
  refine ⟨P, γ, hγ, fun S => ?_⟩
  simpa only [cellMoment_apply,
    fourCoordinates_volumeFourMoments (by omega : 0 < r+2)] using gap S

end NRR.CubePartitionSpace
