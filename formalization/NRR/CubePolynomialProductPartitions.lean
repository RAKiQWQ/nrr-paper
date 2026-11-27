import NRR.CubePartitionLocalStacks
import NRR.CubeProductMoments

/-! The fixed rational polynomial pair on every actual three-dimensional
cube partition, expressed directly on closed sets and then on their genuine
products in all passive dimensions. -/

noncomputable section
open Set Topology MeasureTheory
open NRR.Coordinates

namespace NRR.CubePolynomialProductPartitions
open CubeProductMoments RationalMomentApproximation

theorem coordinate_image_cube :
    CubePlaneCoordinates.E '' CubePartitionSpace.cube = CubePlaneCoordinates.coordinateCube := by
  have eq : CubePartitionSpace.cube = CubePlaneCoordinates.cube := by
    ext p
    rw [CubePlaneCoordinates.mem_cube]
    change ((∀ j : Fin 2, p.1 j ∈ Icc (-1 : ℝ) 1) ∧ p.2 ∈ Icc (-1 : ℝ) 1) ↔ _
    constructor
    · rintro ⟨h,hz⟩
      exact ⟨h 0,h 1,hz⟩
    · rintro ⟨h0,h1,hz⟩
      refine ⟨?_,hz⟩
      intro j
      fin_cases j <;> assumption
  rw [eq, CubePlaneCoordinates.image_cube]

/-- The pair is selected before every actual set partition; the formulation
does not require a caller to construct a point of the Hausdorff subtype. -/
theorem exists_polynomials_for_actual_sets (n : ℕ) (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ B : Fin n → Set Active,
        (∀ i, IsCompact (B i)) → (∀ i, Convex ℝ (B i)) →
        (∀ i, (interior (B i)).Nonempty) →
        (⋃ i, B i) = CubePlaneCoordinates.coordinateCube →
        Pairwise (fun i j => Disjoint (interior (B i)) (interior (B j))) →
        (∀ i j, volume.real (B i) = volume.real (B j)) →
        ∃ i j a, γ < |eval (P a) (moments3 n (B i)) - eval (P a) (moments3 n (B j))| := by
  obtain ⟨P,γ,hγ,gap⟩ :=
    CubePartitionSpace.exists_rational_polynomials_for_partitions n hn hpow
  refine ⟨P,γ,hγ,?_⟩
  intro B compact convex full cover disjoint equal
  let C : Fin n → ConvexBody Active := fun i =>
    ⟨{ carrier := B i, isCompact' := compact i,
        nonempty' := (full i).mono interior_subset }, convex i, full i⟩
  let K : ConvexBody Active := bodiesHomeomorph CubePlaneCoordinates.E CubePartitionSpace.cubeBody
  have hK : bodyPoints K = CubePlaneCoordinates.coordinateCube := coordinate_image_cube
  have part : Partition K C := by
    refine ⟨?_,disjoint⟩
    change (⋃ i, B i) = bodyPoints K
    rw [hK]
    exact cover
  let Q : Fin n → ConvexBody CubePartitionSpace.Ambient := fun i =>
    bodiesHomeomorph CubePlaneCoordinates.E.symm (C i)
  have parent : bodiesHomeomorph CubePlaneCoordinates.E.symm K =
      CubePartitionSpace.cubeBody := by
    change (bodiesHomeomorph CubePlaneCoordinates.E).symm
      ((bodiesHomeomorph CubePlaneCoordinates.E) CubePartitionSpace.cubeBody) = _
    exact Homeomorph.symm_apply_apply _ _
  have partQ : Partition CubePartitionSpace.cubeBody Q :=
    parent ▸ part.map CubePlaneCoordinates.E.symm
  have transport (i : Fin n) :
      CubePlaneCoordinates.E '' bodyPoints (Q i) = B i := by
    change CubePlaneCoordinates.E '' (CubePlaneCoordinates.E.symm '' B i) = B i
    simp only [image_image, ContinuousLinearEquiv.apply_symm_apply, image_id']
  have vol (i : Fin n) : volume.real (bodyPoints (Q i)) = volume.real (B i) := by
    have h := CubePlaneCoordinates.setIntegral_image_E (bodyPoints (Q i)) (fun _ => (1 : ℝ))
    rw [transport i] at h
    simpa only [setIntegral_one_eq_measureReal] using h.symm
  have sub (i : Fin n) : bodyPoints (Q i) ⊆ CubePartitionSpace.cube := by
    rw [← show bodyPoints CubePartitionSpace.cubeBody = CubePartitionSpace.cube from rfl,
      ← partQ.covers]
    exact subset_iUnion (fun j => bodyPoints (Q j)) i
  have restrict (i : Fin n) :
      CubePartitionSpace.cubeMeasure (bodyPoints (Q i)) = volume (bodyPoints (Q i)) := by
    rw [CubePartitionSpace.cubeMeasure,
      Measure.restrict_apply (Q i).val.isCompact.isClosed.measurableSet,
      inter_eq_left.mpr (sub i)]
  have equalQ (i j : Fin n) :
      CubePartitionSpace.cubeMeasure (bodyPoints (Q i)) =
        CubePartitionSpace.cubeMeasure (bodyPoints (Q j)) := by
    rw [restrict i, restrict j]
    apply (ENNReal.toReal_eq_toReal_iff'
      (Q i).val.isCompact.measure_lt_top.ne (Q j).val.isCompact.measure_lt_top.ne).mp
    exact (vol i).trans ((equal i j).trans (vol j).symm)
  let S : CubePartitionSpace.X n := ⟨Q,partQ,equalQ⟩
  obtain ⟨i,j,a,h⟩ := gap S
  change γ < |eval (P a) (moments3 n (CubePlaneCoordinates.E '' bodyPoints (Q i))) -
    eval (P a) (moments3 n (CubePlaneCoordinates.E '' bodyPoints (Q j)))| at h
  rw [transport i, transport j] at h
  exact ⟨i,j,a,h⟩

/-- One preselected pair and the same positive gap apply in every product
dimension to every actual active partition, without an affine-stack premise. -/
theorem exists_polynomials_for_product_partitions (n : ℕ)
    (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ (k : ℕ) (B : Fin n → Set Active),
        (∀ i, IsCompact (B i)) → (∀ i, Convex ℝ (B i)) →
        (∀ i, (interior (B i)).Nonempty) →
        (⋃ i, B i) = CubePlaneCoordinates.coordinateCube →
        Pairwise (fun i j => Disjoint (interior (B i)) (interior (B j))) →
        (∀ i j, volume.real (B i) = volume.real (B j)) →
        ∃ i j a, γ < |eval (P a) (productMoments k n (B i)) -
          eval (P a) (productMoments k n (B j))| := by
  obtain ⟨P,γ,hγ,gap⟩ := exists_polynomials_for_actual_sets n hn hpow
  exact ⟨P,γ,hγ,fun k B hc hv hf hp hd he => by
    simpa only [productMoments_eq] using gap B hc hv hf hp hd he⟩

end NRR.CubePolynomialProductPartitions
