import NRR.PrimePowerTopologyGeneralCellAttachment
import NRR.PrimePowerTopologyFuksSubpair
import NRR.SingularHomologyFiniteCellGroups
import NRR.PrimePowerTopologyTwistedBoundaryTransfer

/-! The ordinary singular relative homology of every successive pair of
compactified Fuks levels. In degrees below the next cell dimension minus
one, the actual inclusion of relative chains induces an isomorphism. -/

noncomputable section
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] (d m k : ℕ) [NeZero m]

/-- For `m+1` labels, the relative group of levels `k ⊆ k+1` is free in
degree `k+1+(m+1)`, on the labelled words of that degree. This includes a
vacuous layer, whose index type is empty. -/
def generalFuksRelativeTopEquiv :
    (fuksRelativeComplex R (d := d) (n := m+1)
      (show k ≤ k+1 by omega)).homology (k+1+(m+1)) ≃ₗ[R] (GeneralFuksCellIndex d m k → R) :=
  (fuksSubsetPairIso R (Nat.le_succ k) (k+1+(m+1))).toLinearEquiv.trans
    ((generalFuksFiniteAttachment d m k).relativeTopCoordinates R
      (nonempty_generalFuksLowerSubset d m k) (k+1+m) (finrank_generalFuksParameters m k))

theorem isZero_generalFuksRelative_off_dimension (q : ℕ) (hoff : q ≠ k+1+(m+1)) :
    IsZero ((fuksRelativeComplex R (d := d) (n := m+1) (Nat.le_succ k)).homology q) :=
  IsZero.of_iso ((generalFuksFiniteAttachment d m k).isZero_relative_off_dimension R
    (nonempty_generalFuksLowerSubset d m k) (k+1+m) q (finrank_generalFuksParameters m k) hoff)
    (fuksSubsetPairIso R (Nat.le_succ k) q)

/-- Above the possible incoming boundary, a later layer preserves every
ordinary class in degree `q`, with surjectivity as well as injectivity. -/
theorem isIso_generalFuksRelative_step {a : ℕ} (ha : a ≤ k) (q : ℕ)
    (h : q+1 < k+1+(m+1)) :
    IsIso (HomologicalComplex.homologyMap (fuksRelativeMap R (d := d) (n := m+1)
      ha (ha.trans (Nat.le_succ k)) (le_refl a) (Nat.le_succ k)) q) := by
  let T := fuksTriple R (d := d) (n := m+1) ha (Nat.le_succ k)
  have ht := fuksTriple_shortExact R (d := d) (n := m+1) ha (Nat.le_succ k)
  have hi : ht.δ (q+1) q rfl = 0 :=
    (isZero_generalFuksRelative_off_dimension R d m k (q+1) h.ne).eq_zero_of_src _
  have hj : HomologicalComplex.homologyMap T.g q = 0 :=
    (isZero_generalFuksRelative_off_dimension R d m k q (by omega)).eq_zero_of_tgt _
  letI : Mono (HomologicalComplex.homologyMap T.f q) := (ht.homology_exact₁ (q+1) q rfl).mono_g hi
  letI : Epi (HomologicalComplex.homologyMap T.f q) := (ht.homology_exact₂ q).epi_f hj
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap T.f q)

end NRR.PrimePowerTopology
