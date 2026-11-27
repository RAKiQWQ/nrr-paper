import NRR.SingularHomologySmallQuasiIso

/-! Excision for actual relative singular homology under a cover by
interiors. The comparison is the canonical previously constructed map. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

namespace NRR.SingularHomology
variable (R : Type) [Ring R]
variable {X : TopCat.{0}} (A B : Set X)

theorem quasiIso_mvSmallIncl (cover : interior A ∪ interior B = Set.univ) :
    QuasiIso (mvSmallIncl (R := R) A B) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_mvSmallIncl_homologyMap R A B cover n

/-- Passing from small relative chains to all relative chains is a genuine
quasi-isomorphism. It follows from the morphism of actual short exact
sequences, with identity on the subspace chain complex. -/
theorem quasiIso_mvSmallRelMap (cover : interior A ∪ interior B = Set.univ) :
    QuasiIso (mvSmallRelMap (R := R) A B) := by
  have h₁ : QuasiIso
      (mvSmallRelShortComplexMap (R := R) A B).τ₁ := by
    change QuasiIso (𝟙 (Csing R (TopCat.of B)))
    infer_instance
  have h₂ : QuasiIso
      (mvSmallRelShortComplexMap (R := R) A B).τ₂ :=
    quasiIso_mvSmallIncl R A B cover
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (mvSmallRelShortComplexMap (R := R) A B)
    (mvSmallRelShortComplex_shortExact (R := R) A B)
    (relShortComplex_shortExact R (subIncl B)) h₁ h₂

theorem isIso_mvSmallRelMap_homologyMap
    (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (mvSmallRelMap (R := R) A B) n) := by
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp
    ((quasiIso_iff _).mp (quasiIso_mvSmallRelMap R A B cover) n)

/-- The canonical excision map H_n(A,A∩B;R) -> H_n(X,B;R) is an
isomorphism whenever the interiors of A and B cover X. -/
theorem isIso_mvExcisionHrelMap
    (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (mvExcisionHrelMap R A B n) := by
  change IsIso (HomologicalComplex.homologyMap
    (relComplexMap R (mvInclLeft A B) (subIncl B)
      (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B from rfl)) n)
  rw [← mvExcisionChainMap_comp (R := R) A B,
    HomologicalComplex.homologyMap_comp]
  letI : IsIso (mvExcisionToSmallChainMap (R := R) A B) :=
    isIso_mvExcisionToSmallChainMap (R := R) A B
  letI : IsIso (HomologicalComplex.homologyMap (mvSmallRelMap (R := R) A B) n) :=
    isIso_mvSmallRelMap_homologyMap R A B cover n
  infer_instance

def mvExcisionHrelIso (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    Hrel R n (mvInclLeft A B) ≅ Hrel R n (subIncl B) := by
  letI := isIso_mvExcisionHrelMap R A B cover n
  exact asIso (mvExcisionHrelMap R A B n)

end NRR.SingularHomology
