import NRR.ProductPartitions
import NRR.CubePlaneCoordinates
import NRR.CubeHorizontalRigidity
import NRR.CubeVolumeMoments
import NRR.CubeMomentCorrection
import NRR.PartitionMoments

/-! The compact space of actual equal-volume convex partitions of the cube,
with its continuous four-moment readout. -/

noncomputable section
open Set Topology MeasureTheory
open scoped ENNReal

namespace NRR.CubePartitionSpace

open Coordinates CubeMomentCorrection

abbrev Ambient := Space 2 × ℝ

def cube : Set Ambient := CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1

theorem cube_compact : IsCompact cube :=
  CubeHorizontalRigidity.square_compact.prod isCompact_Icc

theorem cube_interior_nonempty : (interior cube).Nonempty := by
  rw [cube, interior_prod_eq, interior_Icc]
  exact CubeHorizontalRigidity.square_interior_nonempty.prod ⟨0, by norm_num, by norm_num⟩

def cubeBody : ConvexBody Ambient :=
  ⟨{ carrier := cube, isCompact' := cube_compact,
      nonempty' := cube_interior_nonempty.mono interior_subset },
    CubeHorizontalRigidity.square_convex.prod (convex_Icc _ _), cube_interior_nonempty⟩

@[simp] theorem cubeBody_points : bodyPoints cubeBody = cube := rfl

def cubeMeasure : Measure Ambient := volume.restrict cube

instance : IsFiniteMeasure cubeMeasure :=
  ⟨by simpa [cubeMeasure] using cube_compact.measure_lt_top⟩

instance ambientHaar : Measure.IsAddHaarMeasure (volume : Measure Ambient) := by
  rw [Measure.volume_eq_prod]
  infer_instance

theorem cubeMeasure_ac : cubeMeasure ≪ volume := Measure.absolutelyContinuous_restrict

theorem cubeMeasure_pos : 0 < cubeMeasure (bodyPoints cubeBody) := by
  simpa [cubeMeasure] using
    Measure.measure_pos_of_nonempty_interior volume cube_interior_nonempty

/-- The ambient function space is the actual space of Euclidean convex bodies. -/
def partitions (n : ℕ) : Set (Fin n → ConvexBody Ambient) :=
  equalMassPartitions cubeBody cubeMeasure

abbrev X (n : ℕ) := ↥(partitions n)

instance (n : ℕ) : CompactSpace (X n) :=
  isCompact_iff_compactSpace.mp
    (Coordinates.compact_equalMassPartitions (horizontalHeight 2) cubeBody cubeMeasure
      cubeMeasure_ac cubeMeasure_pos)

theorem partition {n : ℕ} (S : X n) : Partition cubeBody S.val := S.property.1

theorem equal_mass {n : ℕ} (S : X n) (i j : Fin n) :
    cubeMeasure (bodyPoints (S.val i)) = cubeMeasure (bodyPoints (S.val j)) :=
  S.property.2 i j

theorem cell_subset {n : ℕ} (S : X n) (i : Fin n) : bodyPoints (S.val i) ⊆ cube := by
  have h := subset_iUnion (fun j => bodyPoints (S.val j)) i
  rwa [(partition S).covers] at h

@[simp] theorem cubeMeasure_cell {n : ℕ} (S : X n) (i : Fin n) :
    cubeMeasure (bodyPoints (S.val i)) = volume (bodyPoints (S.val i)) := by
  rw [cubeMeasure, Measure.restrict_apply (S.val i).val.isCompact.isClosed.measurableSet,
    inter_eq_left.mpr (cell_subset S i)]

theorem equal_volume {n : ℕ} (S : X n) (i j : Fin n) :
    volume (bodyPoints (S.val i)) = volume (bodyPoints (S.val j)) := by
  simpa only [cubeMeasure_cell] using equal_mass S i j

theorem cell_volume {n : ℕ} (S : X n) (i : Fin n) :
    volume (bodyPoints (S.val i)) = volume cube / n := by
  calc
    _ = cubeMeasure (bodyPoints (S.val i)) := (cubeMeasure_cell S i).symm
    _ = cubeMeasure (bodyPoints cubeBody) / n :=
      (partition S).mass_eq_div cubeMeasure cubeMeasure_ac (equal_mass S) i
    _ = _ := by simp [cubeMeasure]

/-- The genuine four volume moments, transported by the Hausdorff homeomorphism. -/
def cellMoment (n : ℕ) (i : Fin n) : C(X n, Input) :=
  let select : C(X n, ConvexLimits.ConvexCompact Ambient) :=
    ⟨fun S => bodyToConvexCompact (S.val i),
      continuous_bodyToConvexCompact.comp
        ((continuous_apply i).comp continuous_subtype_val)⟩
  let transport : C(ConvexLimits.ConvexCompact Ambient,
      ConvexLimits.ConvexCompact ((ℝ × ℝ) × ℝ)) :=
    ⟨convexCompactsHomeomorph CubePlaneCoordinates.E,
      (convexCompactsHomeomorph CubePlaneCoordinates.E).continuous⟩
  let readout : C(ConvexLimits.ConvexCompact ((ℝ × ℝ) × ℝ), Input) :=
    ⟨fun C => CubeFourMomentReadout.volumeFourMoments (2 / n) (ConvexLimits.points C),
      CubeFourMomentReadout.continuous_volumeFourMoments (2 / n)⟩
  readout.comp (transport.comp select)

@[simp] theorem cellMoment_apply {n : ℕ} (i : Fin n) (S : X n) :
    cellMoment n i S = CubeFourMomentReadout.volumeFourMoments (2 / n)
      (CubePlaneCoordinates.E '' bodyPoints (S.val i)) := rfl

def horizontalCoordinate (j : Fin 2) : Ambient →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.fst ℝ (Space 2) ℝ)

theorem integral_cube_coordinate (j : Fin 2) :
    (∫ p in cube, p.1 j ∂volume) = 0 := by
  have symmetric : Neg.neg ⁻¹' cube = cube := by
    ext p
    simp only [cube, mem_preimage, mem_prod, CubeHorizontalRigidity.square,
      mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, PiLp.neg_apply, mem_Icc]
    constructor <;> rintro ⟨h, hz⟩ <;> constructor
    · intro j; have := h j; constructor <;> linarith
    · constructor <;> linarith [hz.1, hz.2]
    · intro j; have := h j; constructor <;> linarith
    · constructor <;> linarith [hz.1, hz.2]
  have hz := ConvexLimits.integral_id_zero_of_neg_invariant volume
    cube_compact.isClosed.measurableSet symmetric
  have hi : IntegrableOn id cube volume :=
    continuous_id.continuousOn.integrableOn_compact cube_compact
  have h := (horizontalCoordinate j).integral_comp_comm hi
  change (∫ p in cube, p.1 j) = horizontalCoordinate j (∫ p in cube, p) at h
  rw [h, hz, map_zero]

theorem sum_integral_coordinate {n : ℕ} (S : X n) (j : Fin 2) :
    (∑ i, ∫ p in bodyPoints (S.val i), p.1 j ∂volume) = 0 := by
  rw [← ConvexLimits.integral_partition volume volume Measure.AbsolutelyContinuous.rfl
    (fun i => bodyPoints (S.val i)) (fun i => (S.val i).val.isCompact.isClosed)
    (fun i => (S.val i).property.1) (partition S).disjoint (partition S).covers
    (fun p => p.1 j) ((horizontalCoordinate j).continuous.continuousOn.integrableOn_compact
      cube_compact)]
  exact integral_cube_coordinate j

theorem horizontal_cellMoment {n : ℕ} (S : X n) (i : Fin n) :
    horizontal (cellMoment n i S) = toComplex
      ((1 / (4 * (2 / n))) * (∫ p in bodyPoints (S.val i), p.1 0),
       (1 / (4 * (2 / n))) * (∫ p in bodyPoints (S.val i), p.1 1)) := by
  simp only [cellMoment_apply, horizontal, ContinuousMap.coe_mk,
    CubeFourMomentReadout.volumeFourMoments, CubePlaneCoordinates.setIntegral_image_E]
  simp [CubePlaneCoordinates.E, CubePlaneCoordinates.e_apply]

/-- The horizontal readouts balance on every genuine partition. -/
theorem sum_horizontal {n : ℕ} (S : X n) :
    ∑ i, horizontal (cellMoment n i S) = 0 := by
  simp_rw [horizontal_cellMoment]
  apply Complex.ext
  · simp [toComplex, ← Finset.mul_sum, sum_integral_coordinate S 0]
  · simp [toComplex, ← Finset.mul_sum, sum_integral_coordinate S 1]

/-- Zero horizontal readouts force the original Euclidean cells to be slabs. -/
theorem partition_is_slabs {n : ℕ} (S : X n)
    (zero : ∀ i, horizontal (cellMoment n i S) = 0) :
    ∀ i, ∃ a b : ℝ, a < b ∧
      bodyPoints (S.val i) = CubeHorizontalRigidity.square ×ˢ Icc a b := by
  apply CubeHorizontalRigidity.partition_is_slabs (fun i => bodyPoints (S.val i))
    (fun i => (S.val i).val.isCompact) (fun i => (S.val i).property.1)
    (partition S).covers (partition S).disjoint
  · intro i
    exact ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior volume (S.val i).property.2).ne'
      (S.val i).val.isCompact.measure_lt_top.ne
  · intro i j
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_le i.val |>.trans_lt i.isLt))
    have hc : (1 / (4 * (2 / (n : ℝ)))) ≠ 0 := by positivity
    have h := zero i
    rw [horizontal_cellMoment] at h
    fin_cases j
    · have hr := congrArg Complex.re h
      simp only [toComplex, Complex.zero_re] at hr
      exact (mul_eq_zero.mp hr).resolve_left hc
    · have hr := congrArg Complex.im h
      simp only [toComplex, Complex.zero_im] at hr
      exact (mul_eq_zero.mp hr).resolve_left hc

end NRR.CubePartitionSpace
