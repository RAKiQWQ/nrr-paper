import NRR.PrimePowerTopologyTwoColumnIncidence

/-! Relabelling acts on the actual two-column disk basis by permuting the
label order. The same parameter disk is used throughout each orbit. -/

noncomputable section
open CategoryTheory
open NRR.SingularHomology NRR.SingularHomology.FiniteCellAttachment

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]

/-- Relabelling a disk class is the class of the relabelled characteristic
map, with the original oriented disk as source. -/
theorem twoColumnDiskRelativeMap_relabel (c : TwoColumnCellIndex n)
    (σ : Equiv.Perm (Fin n)) (q : ℕ) :
    twoColumnDiskRelativeMap R (d := d) c q ≫
        HomologicalComplex.homologyMap (fuksRelativeRelabel R (d := d+1)
          (show d+1 ≤ d+2 by omega) σ) q =
      twoColumnDiskRelativeMap R (d := d) (c.1, σ*c.2) q := by
  change HrelMap R q _ _ _ ≫ HrelMap R q _ _ _ = HrelMap R q _ _ _
  rw [HrelMap_comp]
  congr 1
  · ext x
    exact (compactifiedConfigurationRelabel_mul_apply σ c.2 _).symm
  · ext x
    exact (compactifiedConfigurationRelabel_mul_apply σ c.2 _).symm

theorem twoColumnFuksBasis_relabel (hn : 2 ≤ n)
    (c : TwoColumnCellIndex n) (σ : Equiv.Perm (Fin n)) :
    HomologicalComplex.homologyMap (fuksRelativeRelabel R (d := d+1)
      (show d+1 ≤ d+2 by omega) σ) (d+n+2) (twoColumnFuksBasis R d n hn c) =
      twoColumnFuksBasis R d n hn (c.1, σ*c.2) := by
  rw [twoColumnFuksBasis_eq_disk_image R hn, twoColumnFuksBasis_eq_disk_image R hn]
  exact congrArg (fun f : Hrel R (d+n+2) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
    (diskBoundary (TwoColumnAmbientParameters d n))) ⟶
      (fuksRelativeComplex R (d := d+1) (n := n) (show d+1 ≤ d+2 by omega)).homology (d+n+2) =>
      f (twoColumnOrientedDiskClass R d n)) (twoColumnDiskRelativeMap_relabel R (d := d) c σ (d+n+2))

end NRR.PrimePowerTopology
