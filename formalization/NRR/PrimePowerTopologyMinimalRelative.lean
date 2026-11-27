import NRR.PrimePowerTopologyMinimalHomology
import NRR.PrimePowerTopologyFilteredChains

/-! Genuine nonzero fundamental classes in the lowest Fuks relative pair.
The lower level is the actual point at infinity, and the positive-degree
comparison is the canonical quotient map in the singular pair sequence.
No orientation-twisted or cellular comparison is assumed here. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

/-- Quotienting by an actual contractible subspace preserves homology in
degrees at least two, by the canonical pair quotient. -/
def relativeOfContractibleSubspaceIso (q : ℕ) {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] :
    Habs R (q+2) X ≅ Hrel R (q+2) i := by
  have hi : HabsMap R (q+2) i = 0 :=
    (isZero_Habs_of_contractible R (q+2) (by omega) A).eq_zero_of_src _
  have hd : relδ R (q+1) i = 0 :=
    (isZero_Habs_of_contractible R (q+1) (by omega) A).eq_zero_of_tgt _
  letI : Mono (relJ R (q+2) i) := (pair_exact_iota_j R (q+2) i).mono_g hi
  letI : Epi (relJ R (q+2) i) := (pair_exact_j_δ R (q+1) i).epi_f hd
  letI : IsIso (relJ R (q+2) i) := isIso_of_mono_of_epi _
  exact asIso (relJ R (q+2) i)

def minimalLevelHomeomorph (d n : ℕ) [NeZero n] :
    minimalSkeleton d n ≃ₜ compactifiedFuksLevel d n d :=
  Homeomorph.setCongr (compactifiedFuksLevel_minimal (d := d) (n := n)).symm

theorem contractible_lowerFuksLevel (d n : ℕ) [NeZero n] (hd : 0 < d) :
    ContractibleSpace (compactifiedFuksLevel d n (d-1)) := by
  have he := compactifiedFuksLevel_eq_infty_of_lt (d := d) (n := n)
    (by omega : d-1 < d)
  letI : Subsingleton (compactifiedFuksLevel d n (d-1)) := ⟨fun x y => by
    apply Subtype.ext
    have hx : x.val = ∞ := by simpa only [he, mem_singleton_iff] using x.property
    have hy : y.val = ∞ := by simpa only [he, mem_singleton_iff] using y.property
    exact hx.trans hy.symm⟩
  letI : Nonempty (compactifiedFuksLevel d n (d-1)) :=
    ⟨⟨∞, Or.inl rfl⟩⟩
  infer_instance

/-- The actual lowest Fuks relative pair receives the minimal skeleton
homology by a genuine isomorphism in the precise top degree d+n. -/
def minimalFuksRelativeIso (d n : ℕ) [NeZero n] (hd : 0 < d) :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ≅
      (fuksRelativeComplex R (d := d) (n := n)
        (show d-1 ≤ d by omega)).homology (d+n) := by
  letI := contractible_lowerFuksLevel d n hd
  have hdim : 2 ≤ d+n := by have hn := NeZero.pos n; omega
  have e := relativeOfContractibleSubspaceIso R (d+n-2)
    (compactifiedFuksInclusion (d := d) (n := n) (show d-1 ≤ d by omega))
  have eqdim : d+n-2+2 = d+n := Nat.sub_add_cancel hdim
  rw [eqdim] at e
  exact HabsIsoOfHomotopyEquiv R (d+n)
    (minimalLevelHomeomorph d n).toHomotopyEquiv ≪≫ e

def minimalRelativeFundamentalClass {d n : ℕ} [NeZero n]
    (hd : 0 < d) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (fuksRelativeComplex R (d := d) (n := n)
      (show d-1 ≤ d by omega)).homology (d+n) :=
  (minimalFuksRelativeIso R d n hd).hom
    (minimalFundamentalClass R i₀ σ (by omega))

theorem minimalRelativeFundamentalClass_ne_zero [Nontrivial R]
    {d n : ℕ} [NeZero n] (hd : 0 < d) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    minimalRelativeFundamentalClass R hd i₀ σ ≠ 0 := by
  have hdim : 0 < d+n := by omega
  have injective := (ModuleCat.mono_iff_injective
    (minimalFuksRelativeIso R d n hd).hom).mp inferInstance
  intro hz
  apply minimalFundamentalClass_ne_zero R i₀ σ hdim
  apply injective
  simpa only [map_zero] using hz

end NRR.PrimePowerTopology
