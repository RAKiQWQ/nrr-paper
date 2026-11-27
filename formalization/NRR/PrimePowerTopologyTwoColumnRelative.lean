import NRR.SingularHomologyFiniteCellGroups
import NRR.PrimePowerTopologyTwoColumnDisks
import NRR.PrimePowerTopologyFuksSubpair

/-! The actual first nonminimal Fuks pair is a good finite disk
attachment. All cells, boundaries and neighborhood deformations below
refer to the genuine compactified configuration spaces. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology Metric CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

theorem isClosed_twoColumnLowerSubset (d n : ℕ) : IsClosed (twoColumnLowerSubset d n) :=
  (isClosed_compactifiedFuksLevel (d+1) n (d+1)).preimage continuous_subtype_val

instance compactSpace_twoColumnLowerSubset (d n : ℕ) :
    CompactSpace (twoColumnLowerSubset d n) :=
  isCompact_iff_compactSpace.mp (isClosed_twoColumnLowerSubset d n).isCompact

theorem nonempty_twoColumnLowerSubset (d n : ℕ) : (twoColumnLowerSubset d n).Nonempty :=
  ⟨⟨∞,Or.inl rfl⟩,Or.inl rfl⟩

def twoColumnFiniteAttachment (d n : ℕ) [NeZero n] :
    FiniteCellAttachment (TwoColumnCellIndex n) (TwoColumnAmbientParameters d n)
      (compactifiedFuksLevel (d+1) n (d+2)) (twoColumnLowerSubset d n) where
  characteristic := orderedTwoColumnDiskCharacteristic
  boundary := orderedTwoColumnDiskCharacteristic_mem_lower_iff
  interior_unique := orderedTwoColumnDiskCharacteristic_interior_unique
  cover := orderedTwoColumnDiskCharacteristic_cover

/-- A genuine open neighborhood of the entire compactified lower level. -/
def twoColumnGoodNeighborhood (d n : ℕ) [NeZero n] :
    Set (compactifiedFuksLevel (d+1) n (d+2)) :=
  (twoColumnFiniteAttachment d n).neighborhood

theorem isOpen_twoColumnGoodNeighborhood (d n : ℕ) [NeZero n] :
    IsOpen (twoColumnGoodNeighborhood d n) :=
  (twoColumnFiniteAttachment d n).isOpen_neighborhood

/-- The lower level is a deformation retract of this actual neighborhood,
including at the original point at infinity and all collision faces. -/
def twoColumnNeighborhoodDeformation (d n : ℕ) [NeZero n] :
    NeighborhoodDeformation (twoColumnLowerSubset d n) (twoColumnGoodNeighborhood d n) :=
  (twoColumnFiniteAttachment d n).neighborhoodDeformation

def twoColumnLowerHomeomorph (d n : ℕ) :
    compactifiedFuksLevel (d+1) n (d+1) ≃ₜ twoColumnLowerSubset d n :=
  fuksLowerSubsetHomeomorph (show d+1 ≤ d+2 by omega)

section Homology

variable (R : Type) [CommRing R]

/-- Identify the two descriptions of the same relative pair by the identity
on the upper level and the canonical homeomorphism onto its lower subset. -/
def twoColumnFuksPairIso (d n q : ℕ) :
    (fuksRelativeComplex R (d := d+1) (n := n) (show d+1 ≤ d+2 by omega)).homology q ≅
      Hrel R q (subIncl (Y := TopCat.of (compactifiedFuksLevel (d+1) n (d+2)))
        (twoColumnLowerSubset d n)) :=
  fuksSubsetPairIso R (show d+1 ≤ d+2 by omega) q

private theorem nonempty_twoColumnCellIndex {n : ℕ} (hn : 2 ≤ n) :
    Nonempty (TwoColumnCellIndex n) :=
  ⟨⟨⟨⟨1, by omega⟩, Nat.zero_lt_one⟩, 1⟩⟩

/-- The genuine first nonminimal relative singular group has one free
coordinate for every ordered two-column disk. -/
def twoColumnFuksTopEquiv (d n : ℕ) (hn : 2 ≤ n) :
    (fuksRelativeComplex R (d := d+1) (n := n)
      (show d+1 ≤ d+2 by omega)).homology (d+n+2) ≃ₗ[R] (TwoColumnCellIndex n → R) := by
  letI : NeZero n := ⟨by omega⟩
  letI := nonempty_twoColumnCellIndex hn
  exact (twoColumnFuksPairIso R d n (d+n+2)).toLinearEquiv.trans
    ((twoColumnFiniteAttachment d n).relativeTopEquiv R
      (nonempty_twoColumnLowerSubset d n) (d+n+1) (finrank_twoColumnAmbientParameters d n))

def twoColumnFuksBasis (d n : ℕ) (hn : 2 ≤ n) :
    Module.Basis (TwoColumnCellIndex n) R ((fuksRelativeComplex R (d := d+1) (n := n)
      (show d+1 ≤ d+2 by omega)).homology (d+n+2)) :=
  (Pi.basisFun R (TwoColumnCellIndex n)).map (twoColumnFuksTopEquiv R d n hn).symm

theorem isZero_twoColumnFuksRelative_positive_off_top (d n k : ℕ)
    (hn : 2 ≤ n) (hoff : k+1 ≠ d+n+2) :
    IsZero ((fuksRelativeComplex R (d := d+1) (n := n)
      (show d+1 ≤ d+2 by omega)).homology (k+1)) := by
  letI : NeZero n := ⟨by omega⟩
  letI := nonempty_twoColumnCellIndex hn
  exact IsZero.of_iso ((twoColumnFiniteAttachment d n).isZero_relative_off_top R
    (nonempty_twoColumnLowerSubset d n) k (by rwa [finrank_twoColumnAmbientParameters]))
    (twoColumnFuksPairIso R d n (k+1))

theorem isZero_twoColumnFuksRelative_off_top (d n k : ℕ)
    (hn : 2 ≤ n) (hoff : k ≠ d+n+2) :
    IsZero ((fuksRelativeComplex R (d := d+1) (n := n)
      (show d+1 ≤ d+2 by omega)).homology k) := by
  cases k with
  | succ k => exact isZero_twoColumnFuksRelative_positive_off_top R d n k hn hoff
  | zero =>
    letI : NeZero n := ⟨by omega⟩
    letI := nonempty_twoColumnCellIndex hn
    exact IsZero.of_iso ((twoColumnFiniteAttachment d n).isZero_relative_zero R
      (nonempty_twoColumnLowerSubset d n) (d+n+1) (finrank_twoColumnAmbientParameters d n))
      (twoColumnFuksPairIso R d n 0)

end Homology

end NRR.PrimePowerTopology
