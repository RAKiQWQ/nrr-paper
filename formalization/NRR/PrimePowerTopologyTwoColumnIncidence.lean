import NRR.PrimePowerTopologyTwoColumnRelative
import NRR.SingularHomologyCellCharacteristic
import NRR.PrimePowerTopologyTwistedBoundaryTransfer

/-! The columns of the first ordinary Fuks differential are computed by
applying the actual attaching sphere maps to the boundary of a single
oriented relative disk class. -/

noncomputable section

open CategoryTheory Limits Set
open NRR.SingularHomology NRR.SingularHomology.FiniteCellAttachment

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]

def twoColumnDiskAttachingSphere (c : TwoColumnCellIndex n) :
    C(diskBoundary (TwoColumnAmbientParameters d n), compactifiedFuksLevel (d+1) n (d+1)) :=
  (⟨(twoColumnLowerHomeomorph d n).symm, (twoColumnLowerHomeomorph d n).symm.continuous⟩ :
    C(twoColumnLowerSubset d n, compactifiedFuksLevel (d+1) n (d+1))).comp
    ((twoColumnFiniteAttachment d n).attachingSphere c)

theorem twoColumnDiskCharacteristic_pair_comm (c : TwoColumnCellIndex n) :
    subIncl (Y := TopCat.of (TwoColumnDisk d n)) (diskBoundary (TwoColumnAmbientParameters d n)) ≫
      TopCat.ofHom (orderedTwoColumnDiskCharacteristic c) =
    TopCat.ofHom (twoColumnDiskAttachingSphere c) ≫
      compactifiedFuksInclusion (d := d+1) (n := n) (show d+1 ≤ d+2 by omega) := rfl

def twoColumnDiskRelativeMap (c : TwoColumnCellIndex n) (k : ℕ) :
    Hrel R k (subIncl (Y := TopCat.of (TwoColumnDisk d n)) (diskBoundary (TwoColumnAmbientParameters d n))) ⟶
      (fuksRelativeComplex R (d := d+1) (n := n) (show d+1 ≤ d+2 by omega)).homology k :=
  HrelMap R k _ _ (twoColumnDiskCharacteristic_pair_comm c)

theorem twoColumnDiskRelativeMap_comp_pairIso (c : TwoColumnCellIndex n) (k : ℕ) :
    twoColumnDiskRelativeMap R (d := d) c k ≫ (twoColumnFuksPairIso R d n k).hom =
      (twoColumnFiniteAttachment d n).characteristicRelativeMap R c k := by
  change HrelMap _ _ _ _ _ ≫ HrelMap _ _ _ _ _ = _
  rw [HrelMap_comp]
  rfl

/-- A common disk orientation in the actual space of two-column parameters. -/
def twoColumnOrientedDiskClass (d n : ℕ) :
    Hrel R (d+n+2) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
      (diskBoundary (TwoColumnAmbientParameters d n))) :=
  diskChartTopClass R diskBoundary_nonempty (d+n+1) (finrank_twoColumnAmbientParameters d n)

/-- Each coordinate basis vector is the pushforward of the same oriented
relative disk class by the actual ordered characteristic map. -/
theorem twoColumnFuksBasis_eq_disk_image (hn : 2 ≤ n) (c : TwoColumnCellIndex n) :
    twoColumnFuksBasis R d n hn c =
      twoColumnDiskRelativeMap R c (d+n+2) (twoColumnOrientedDiskClass R d n) := by
  classical
  letI : Nonempty (TwoColumnCellIndex n) := ⟨c⟩
  apply (twoColumnFuksTopEquiv R d n hn).injective
  rw [twoColumnFuksBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  symm
  let x := twoColumnOrientedDiskClass R d n
  change (twoColumnFiniteAttachment d n).relativeTopEquiv R _ _ _
    ((twoColumnFuksPairIso R d n (d+n+2)).hom (twoColumnDiskRelativeMap R c (d+n+2) x)) = _
  have h := congrArg (fun f : Hrel R (d+n+2) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
    (diskBoundary (TwoColumnAmbientParameters d n))) ⟶
    Hrel R (d+n+2) (subIncl (Y := TopCat.of (compactifiedFuksLevel (d+1) n (d+2)))
      (twoColumnLowerSubset d n)) => f x) (twoColumnDiskRelativeMap_comp_pairIso R c (d+n+2))
  rw [show (twoColumnFuksPairIso R d n (d+n+2)).hom (twoColumnDiskRelativeMap R c (d+n+2) x) =
      (twoColumnFiniteAttachment d n).characteristicRelativeMap R c (d+n+2) x from h]
  exact (twoColumnFiniteAttachment d n).relativeTopEquiv_characteristic R
    (nonempty_twoColumnLowerSubset d n) diskBoundary_nonempty c (d+n+1)
    (finrank_twoColumnAmbientParameters d n)

/-- A column of the true three-level differential, before evaluating its
shuffle degrees. The last map is the quotient by the level below the minimum. -/
theorem fuksDifferential_twoColumnFuksBasis (hn : 2 ≤ n) (c : TwoColumnCellIndex n) :
    fuksDifferential R (d := d+1) (n := n) (show d ≤ d+1 by omega)
      (show d+1 ≤ d+2 by omega) (d+n+1) (twoColumnFuksBasis R d n hn c) =
    relJ R (d+n+1) (compactifiedFuksInclusion (d := d+1) (n := n) (show d ≤ d+1 by omega))
      (HabsMap R (d+n+1) (TopCat.ofHom (twoColumnDiskAttachingSphere c))
        (relδ R (d+n+1) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
          (diskBoundary (TwoColumnAmbientParameters d n))) (twoColumnOrientedDiskClass R d n))) := by
  rw [twoColumnFuksBasis_eq_disk_image R hn c]
  have h := congrArg (fun f : Hrel R (d+n+2) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
    (diskBoundary (TwoColumnAmbientParameters d n))) ⟶
    Habs R (d+n+1) (TopCat.of (compactifiedFuksLevel (d+1) n (d+1))) =>
      f (twoColumnOrientedDiskClass R d n))
    (relδ_naturality R (d+n+1) _ _ (twoColumnDiskCharacteristic_pair_comm c))
  exact congrArg (relJ R (d+n+1) (compactifiedFuksInclusion (d := d+1) (n := n)
    (show d ≤ d+1 by omega))) h.symm

end NRR.PrimePowerTopology
