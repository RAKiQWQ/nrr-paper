import NRR.PrimePowerTopologyTwoColumnIncidence
import NRR.PrimePowerTopologyTwoColumnBoundaryCharts
import NRR.PrimePowerTopologyMinimalRelative
import NRR.PrimePowerTopologyMinimalEquivariance

/-! Finite-point support of a two-column boundary and the resulting actual
minimal-cell pinch on the attaching sphere. -/

noncomputable section
set_option maxHeartbeats 400000
open Set Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology
open NRR.SingularHomology.FiniteCellAttachment

namespace NRR.PrimePowerTopology

/-- A finite point in a minimal chamber can only be hit by the canonical
two-column attaching map when the chamber order is a shuffle of its columns. -/
theorem compactTwoColumnAttaching_ne_minimalCellInclusion_of_not_shuffle
    {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (σ : Equiv.Perm (Fin n)) (hnoshuffle : ¬ IsColumnShuffle S σ)
    (i₀ : Fin n) (x : Space (d+1) × heightChamber n σ)
    (z : twoColumnCharacteristicBoundary (d := d) S) :
    compactTwoColumnAttaching S iL iR hL hR z.val ≠
      (minimalCellInclusion (d := d+1) i₀ σ
        (x : OnePoint (Space (d+1) × heightChamber n σ))).val := by
  intro h
  rcases z with ⟨z,hz⟩
  induction z using OnePoint.rec with
  | infty =>
      simp [compactTwoColumnAttaching_infty, minimalCellInclusion,
        compactifiedVerticalCell] at h
  | coe p =>
      have hcollapse : configurationCollapse (d+2) n
          (twoColumnAmbient S p.val) =
          ((verticalCellEmbedding i₀ σ x : Configuration (d+2) n) :
            OnePoint (Configuration (d+2) n)) := by
        simpa [compactTwoColumnAttaching_coe, twoColumnAttaching,
          ContinuousMap.comp_apply, compactifiedConfigurationCollapse_coe,
          compactifiedVerticalCell, minimalCellInclusion] using h
      by_cases hinj : Function.Injective (twoColumnAmbient S p.val)
      · have hconfig :
            (⟨twoColumnAmbient S p.val,hinj⟩ : Configuration (d+2) n) =
              verticalCellEmbedding i₀ σ x := by
          rw [configurationCollapse_injective (d := d+2) (n := n)
            (twoColumnAmbient S p.val) hinj] at hcollapse
          exact Option.some.inj hcollapse
        have hambient : twoColumnAmbient S p.val =
            fun i => (horizontalHeight (d+1)).symm (x.1,x.2.val i) := by
          funext i
          have hi := congrArg (fun q : Configuration (d+2) n => q.val i) hconfig
          simpa only [verticalCellEmbedding, ContinuousMap.coe_mk,
            verticalCellCoordinates] using hi
        have hheight : p.val.1.2 = x.2.val := by
          funext i
          have hi := congrArg (fun f : Fin n → Space (d+2) =>
            (horizontalHeight (d+1) (f i)).2) hambient
          simpa only [twoColumnAmbient, ContinuousMap.coe_mk,
            ContinuousLinearEquiv.apply_symm_apply] using hi
        have htwoColumnHeights : p.val.1.2 ∈ twoColumnHeights S :=
          twoColumnHeights_of_closed_injective S p hinj
        have hshuffle : IsColumnShuffle S σ :=
          (twoColumnHeights_iff_shuffle S σ x.2.property).mp
            (hheight ▸ htwoColumnHeights)
        exact hnoshuffle hshuffle
      · have hbad : (∞ : OnePoint (Configuration (d+2) n)) =
            ((verticalCellEmbedding i₀ σ x : Configuration (d+2) n) :
              OnePoint (Configuration (d+2) n)) := by
          rw [configurationCollapse_collision _ hinj] at hcollapse
          exact hcollapse
        exact False.elim (OnePoint.infty_ne_coe _ hbad)

/-- The finite-point exclusion is preserved by the actual relabelled ordered
characteristic map; relabeling transports the target chamber by left action. -/
theorem orderedTwoColumnCharacteristic_ne_minimalCellInclusion_of_not_shuffle
    {d n : ℕ} [NeZero n] (c : TwoColumnCellIndex n)
    (σ : Equiv.Perm (Fin n))
    (hnoshuffle : ¬ IsColumnShuffle (canonicalColumnLabels c.1) (c.2.symm * σ))
    (i₀ : Fin n) (x : Space (d+1) × heightChamber n σ)
    (z : twoColumnCharacteristicBoundary (d := d) (canonicalColumnLabels c.1)) :
    (orderedTwoColumnCharacteristic (d := d) c z.val).val ≠
      (minimalCellInclusion (d := d+1) i₀ σ
        (x : OnePoint (Space (d+1) × heightChamber n σ))).val := by
  intro h
  let τ := c.2.symm * σ
  let x' : Space (d+1) × heightChamber n τ :=
    (x.1,heightChamberRelabel c.2.symm σ x.2)
  have hrel : compactifiedConfigurationRelabel c.2.symm
      ((minimalCellInclusion (d := d+1) i₀ σ
        (x : OnePoint (Space (d+1) × heightChamber n σ))).val) =
      (minimalCellInclusion (d := d+1) i₀ τ
        (x' : OnePoint (Space (d+1) × heightChamber n τ))).val := by
    have hmap := congrArg
      (fun f : TopCat.of (OnePoint (Space (d+1) × heightChamber n σ)) ⟶
          TopCat.of (minimalSkeleton (d+1) n) =>
        f x)
      (minimalCellInclusionMap_relabel (d := d+1) i₀ c.2.symm σ)
    change minimalSkeletonRelabel (d := d+1) c.2.symm
        (minimalCellInclusion i₀ σ (x : OnePoint _)) =
      minimalCellInclusion i₀ τ (compactifiedCellRelabel c.2.symm σ
        (x : OnePoint _)) at hmap
    have hval := congrArg Subtype.val hmap
    simpa [τ, x', compactifiedCellRelabel] using hval
  have hcanonical : compactTwoColumnAttaching (canonicalColumnLabels c.1)
      0 c.1.val (zero_mem_canonicalColumnLabels c.1)
      (split_not_mem_canonicalColumnLabels c.1) z.val =
      (minimalCellInclusion (d := d+1) i₀ τ
        (x' : OnePoint (Space (d+1) × heightChamber n τ))).val := by
    have hraw : compactifiedConfigurationRelabel c.2
        (compactTwoColumnAttaching (canonicalColumnLabels c.1)
          0 c.1.val (zero_mem_canonicalColumnLabels c.1)
          (split_not_mem_canonicalColumnLabels c.1) z.val) =
        (minimalCellInclusion (d := d+1) i₀ σ
          (x : OnePoint (Space (d+1) × heightChamber n σ))).val := by
      simpa [orderedTwoColumnCharacteristic, canonicalTwoColumnCharacteristic,
        compactTwoColumnCharacteristic, ContinuousMap.comp_apply,
        compactifiedFuksRelabel] using h
    have hinv := congrArg (compactifiedConfigurationRelabel c.2.symm) hraw
    have hcancel : c.2.symm * c.2 = (1 : Equiv.Perm (Fin n)) := by
      ext i
      simp
    rw [← compactifiedConfigurationRelabel_mul_apply,
      hcancel, compactifiedConfigurationRelabel_one_apply] at hinv
    exact hinv.trans hrel
  exact compactTwoColumnAttaching_ne_minimalCellInclusion_of_not_shuffle
    (canonicalColumnLabels c.1) 0 c.1.val
    (zero_mem_canonicalColumnLabels c.1) (split_not_mem_canonicalColumnLabels c.1)
    τ hnoshuffle i₀ x' z hcanonical

/-- View the genuine attaching sphere as a map to the actual minimal
skeleton using the canonical homeomorphism of minimal-level presentations. -/
def twoColumnDiskAttachingSphereToMinimalSkeleton
    {d n : ℕ} [NeZero n] (c : TwoColumnCellIndex n) :
    C(diskBoundary (TwoColumnAmbientParameters d n),minimalSkeleton (d+1) n) :=
  (⟨fun x => (minimalLevelHomeomorph (d+1) n).symm x,
    (minimalLevelHomeomorph (d+1) n).symm.continuous⟩ :
      C(compactifiedFuksLevel (d+1) n (d+1),minimalSkeleton (d+1) n)).comp
    (twoColumnDiskAttachingSphere (d := d) c)

/-- The composite of the genuine attaching sphere, the minimal-skeleton
inclusion, and the pinch onto a non-shuffle minimal cell. -/
def twoColumnDiskAttachingSphereMinimalPinch
    {d n : ℕ} [NeZero n] (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (c : TwoColumnCellIndex n) :
    C(diskBoundary (TwoColumnAmbientParameters d n),
      OnePoint (Space (d+1) × heightChamber n σ)) :=
  (minimalCellRetraction (d := d+1) i₀ σ).comp
    (twoColumnDiskAttachingSphereToMinimalSkeleton (d := d) c)

@[simp] theorem twoColumnDiskAttachingSphere_val
    {d n : ℕ} [NeZero n] (c : TwoColumnCellIndex n)
    (q : diskBoundary (TwoColumnAmbientParameters d n)) :
    (twoColumnDiskAttachingSphere (d := d) c q).val =
      (orderedTwoColumnDiskCharacteristic c q.val).val := rfl

/-- On the actual sphere boundary, the attaching map has no finite point in
a minimal cell whose order fails the relabelled column-shuffle condition.
Consequently its genuine minimal-cell retraction is the constant infinity map. -/
theorem twoColumnDiskAttachingSphereMinimalPinch_eq_const
    {d n : ℕ} [NeZero n] (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (c : TwoColumnCellIndex n)
    (hnoshuffle : ¬ IsColumnShuffle (canonicalColumnLabels c.1) (c.2.symm * σ)) :
    twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ c =
      ContinuousMap.const _ (∞ : OnePoint (Space (d+1) × heightChamber n σ)) := by
  classical
  ext q
  let S := canonicalColumnLabels c.1
  let disk := twoColumnDiskHomeomorph (d := d) S
  let zval := disk.symm q.val
  have hzval : zval ∈ twoColumnCharacteristicBoundary S := by
    apply (twoColumnDiskHomeomorph_boundary_iff S zval).mp
    change ‖(disk (disk.symm q.val)).val‖ = 1
    rw [Homeomorph.apply_symm_apply]
    exact q.property
  let z : twoColumnCharacteristicBoundary S := ⟨zval,hzval⟩
  let y := twoColumnDiskAttachingSphereToMinimalSkeleton (d := d) c q
  obtain ⟨a,ha⟩ := minimalWedgeProjection_surjective (d := d+1) i₀ y
  rcases a with ⟨τ,p⟩
  have hy : y = minimalCellInclusion (d := d+1) i₀ τ p := by
    change minimalCellInclusion (d := d+1) i₀ τ p = y at ha
    exact ha.symm
  change minimalCellRetraction (d := d+1) i₀ σ y = ∞
  by_cases hτσ : τ = σ
  · subst τ
    rw [hy, minimalCellRetraction_same]
    induction p using OnePoint.rec with
    | infty => rfl
    | coe x =>
        have hhit : (orderedTwoColumnCharacteristic (d := d) c z.val).val =
            (minimalCellInclusion (d := d+1) i₀ σ
              (x : OnePoint (Space (d+1) × heightChamber n σ))).val := by
          have hval := congrArg Subtype.val hy
          simpa [y, twoColumnDiskAttachingSphereToMinimalSkeleton,
            minimalLevelHomeomorph, twoColumnDiskAttachingSphere_val, z, zval, disk, S] using hval
        exact False.elim
          (orderedTwoColumnCharacteristic_ne_minimalCellInclusion_of_not_shuffle
            (d := d) c σ hnoshuffle i₀ x z hhit)
  · rw [hy]
    exact minimalCellRetraction_other (d := d+1) i₀ σ τ hτσ p

section Homology

variable (R : Type) [Ring R]

/-- The induced positive-degree ordinary homology map of the actual
attaching-sphere composite with a non-shuffle cell pinch is zero. -/
theorem HabsMap_twoColumnDiskAttachingSphereMinimalPinch_eq_zero
    {d n : ℕ} [NeZero n] (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (c : TwoColumnCellIndex n)
    (hnoshuffle : ¬ IsColumnShuffle (canonicalColumnLabels c.1) (c.2.symm * σ))
    (k : ℕ) (hk : k ≠ 0) :
    HabsMap R k (TopCat.ofHom
      (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ c)) = 0 := by
  rw [twoColumnDiskAttachingSphereMinimalPinch_eq_const (d := d)
    i₀ σ c hnoshuffle]
  exact HabsMap_const_eq_zero R k hk
    (X := TopCat.of (diskBoundary (TwoColumnAmbientParameters d n)))
    (Y := TopCat.of (OnePoint (Space (d+1) × heightChamber n σ))) ∞

end Homology

end NRR.PrimePowerTopology
