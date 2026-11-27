import NRR.PrimePowerTopologyAssociatedBM
import NRR.PrimePowerTopologyRelativePairOrbitBasis

/-! Regular orbit bases for the actual compactified associated Borel--Moore
pair, with the diagonal label action used by `associatedBMTargetRelativeAction`.
-/

noncomputable section
open CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

private theorem associatedBMCoverRelabel_one {d n : ℕ}
    (z : OnePoint (AssociatedCover d n)) :
    associatedBMCoverRelabel (1 : ConfigurationGroup n) z = z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p =>
      simp [associatedBMCoverRelabel, Homeomorph.onePointCongr,
        Homeomorph.smul]

private theorem associatedBMCoverRelabel_mul {d n : ℕ}
    (σ τ : ConfigurationGroup n) (z : OnePoint (AssociatedCover d n)) :
    associatedBMCoverRelabel (σ * τ) z =
      associatedBMCoverRelabel σ (associatedBMCoverRelabel τ z) := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p =>
      simp [associatedBMCoverRelabel, Homeomorph.onePointCongr,
        Homeomorph.smul, mul_smul]

private theorem associatedBMTarget_pointwise_free {d n : ℕ}
    (σ : ConfigurationGroup n) (z : OnePoint (AssociatedCover d n))
    (hz : z ∉ associatedBMComplement d n)
    (fixed : associatedBMCoverRelabel σ z = z) : σ = 1 := by
  induction z using OnePoint.rec with
  | infty => exact (hz (associatedBMComplement_infty d n)).elim
  | coe p =>
      have hzero : p.2 = 0 := by
        by_contra hzero
        apply hz
        exact (associatedBMComplement_coe_iff p).2 hzero
      have hfix : σ • p = p := Option.some.inj fixed
      apply configuration_action_free σ p.1
      exact congrArg Prod.fst hfix

def associatedBMTargetRelativeSimplexAction {d n q : ℕ} :
    MulAction (ConfigurationGroup n)
      (relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
        (associatedBMComplement d n) q) :=
  relativePairSimplexOutsideMulAction
    associatedBMCoverRelabel
    associatedBMComplement_relabel_mem_iff
    associatedBMCoverRelabel_one
    associatedBMCoverRelabel_mul q

instance associatedBMTargetRelativeSimplexMulAction {d n q : ℕ} :
    MulAction (ConfigurationGroup n)
      (relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
        (associatedBMComplement d n) q) :=
  associatedBMTargetRelativeSimplexAction

theorem associatedBMTargetRelativeSimplex_action_free {d n q : ℕ}
    (σ : ConfigurationGroup n)
    (s : relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
      (associatedBMComplement d n) q)
    (fixed : σ • s = s) : σ = 1 :=
  relativePairSimplex_action_free associatedBMCoverRelabel
    (associatedBMTarget_pointwise_free) (associatedBMTargetRelativeSimplexAction)
    (fun _ _ => rfl) σ s fixed

def associatedBMTargetRelativeOrbitIndex (d n q : ℕ) :=
  freeOrbitIndex (G := ConfigurationGroup n)
    (S := relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
      (associatedBMComplement d n) q)

def associatedBMTargetRelativeOrbitBasis (R : Type) [CommRing R] {d n : ℕ} (q : ℕ) :
    Module.Basis (ConfigurationGroup n × associatedBMTargetRelativeOrbitIndex d n q) R
      ((relComplex R (associatedBMTargetIncl d n)).X q) := by
  let B := relativePairSimplexBasis R
    (X := TopCat.of (OnePoint (AssociatedCover d n)))
    (A := associatedBMComplement d n) (q := q)
  exact freeOrbitBasis R B associatedBMTargetRelativeSimplex_action_free

theorem associatedBMTargetRelativeSimplexGenerator_relabel
    (R : Type) [CommRing R] {d n : ℕ} (q : ℕ)
    (σ : ConfigurationGroup n)
    (s : relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
      (associatedBMComplement d n) q) :
    (associatedBMTargetRelativeAction R (d := d) (n := n) σ).f q
        (relativePairSimplexGenerator R s) =
      relativePairSimplexGenerator R (σ • s) := by
  have h : simplexι R s.val ≫ (relProj R (associatedBMTargetIncl d n)).f q ≫
      (associatedBMTargetRelativeAction R σ).f q =
      simplexι R (σ • s).val ≫ (relProj R (associatedBMTargetIncl d n)).f q := by
    rw [← HomologicalComplex.comp_f, associatedBMTargetRelativeAction,
      relProj_comp_relComplexMap,
      HomologicalComplex.comp_f]
    change simplexι R s.val ≫ (simplicialChainMap R
      (TopCat.toSSet.map (associatedBMCoverRelabelMap σ))).f q ≫ _ = _
    rw [simplexι_chainMap_f_assoc]
    rfl
  exact congrArg (fun f => f 1) h

theorem associatedBMTargetRelativeOrbitBasis_relabel
    (R : Type) [CommRing R] {d n : ℕ} (q : ℕ)
    (σ τ : ConfigurationGroup n)
    (i : associatedBMTargetRelativeOrbitIndex d n q) :
    (associatedBMTargetRelativeAction R (d := d) (n := n) σ).f q
      (associatedBMTargetRelativeOrbitBasis R q (τ, i)) =
      associatedBMTargetRelativeOrbitBasis R q (σ * τ, i) := by
  exact freeOrbitBasis_relabel R
    (relativePairSimplexBasis R
      (X := TopCat.of (OnePoint (AssociatedCover d n)))
      (A := associatedBMComplement d n) (q := q))
    associatedBMTargetRelativeSimplex_action_free
    (fun σ => ((associatedBMTargetRelativeAction R σ).f q).hom)
    (fun σ s => by
      rw [relativePairSimplexBasis_apply, relativePairSimplexBasis_apply]
      exact associatedBMTargetRelativeSimplexGenerator_relabel R q σ s)
    σ τ i

/-! The same construction for the one-point relative pair of the total
associated space `E = Configuration × ReducedValues`. This gives the literal
relative chain module `C(OnePoint E, {∞})` a regular labelled orbit basis.
-/

def associatedBMCoverInfinityIncl (d n : ℕ) :
    TopCat.of ({∞} : Set (OnePoint (AssociatedCover d n))) ⟶
      TopCat.of (OnePoint (AssociatedCover d n)) :=
  subIncl (Y := TopCat.of (OnePoint (AssociatedCover d n))) {∞}

instance mono_associatedBMCoverInfinityIncl (d n : ℕ) :
    Mono (associatedBMCoverInfinityIncl d n) :=
  mono_subIncl (Y := TopCat.of (OnePoint (AssociatedCover d n))) {∞}

theorem associatedBMCoverInfinityIncl_equivariant {d n : ℕ}
    (σ : ConfigurationGroup n) :
    associatedBMCoverInfinityIncl d n ≫ associatedBMCoverRelabelMap σ =
      𝟙 _ ≫ associatedBMCoverInfinityIncl d n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨z,hz⟩
  have hz' : z = ∞ := hz
  subst z
  change associatedBMCoverRelabel σ ∞ = ∞
  simp [associatedBMCoverRelabel]

def associatedBMCoverInfinityRelativeAction (R : Type) [CommRing R] {d n : ℕ}
    (σ : ConfigurationGroup n) :
    relComplex R (associatedBMCoverInfinityIncl d n) ⟶
      relComplex R (associatedBMCoverInfinityIncl d n) :=
  relComplexMap R (associatedBMCoverInfinityIncl d n) (associatedBMCoverInfinityIncl d n)
    (associatedBMCoverInfinityIncl_equivariant σ)

private theorem associatedBMCoverInfinity_mem_relabel_iff {d n : ℕ}
    (σ : ConfigurationGroup n) (z : OnePoint (AssociatedCover d n)) :
    associatedBMCoverRelabel σ z ∈ ({∞} : Set (OnePoint (AssociatedCover d n))) ↔ z = ∞ := by
  induction z using OnePoint.rec with
  | infty => simp [associatedBMCoverRelabel]
  | coe p => simp [associatedBMCoverRelabel]

private theorem associatedBMTotalPointwiseFree {d n : ℕ}
    (σ : ConfigurationGroup n) (z : OnePoint (AssociatedCover d n))
    (hz : z ∉ ({∞} : Set (OnePoint (AssociatedCover d n))))
    (fixed : associatedBMCoverRelabel σ z = z) : σ = 1 := by
  induction z using OnePoint.rec with
  | infty => exact (hz rfl).elim
  | coe p =>
      have hfix : σ • p = p := Option.some.inj fixed
      apply configuration_action_free σ p.1
      exact congrArg Prod.fst hfix

def associatedBMCoverInfinityRelativeSimplexAction {d n q : ℕ} :
    MulAction (ConfigurationGroup n)
      (relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
        ({∞} : Set (OnePoint (AssociatedCover d n))) q) :=
  relativePairSimplexOutsideMulAction
    associatedBMCoverRelabel
    (associatedBMCoverInfinity_mem_relabel_iff)
    associatedBMCoverRelabel_one
    associatedBMCoverRelabel_mul q

instance associatedBMCoverInfinityRelativeSimplexMulAction {d n q : ℕ} :
    MulAction (ConfigurationGroup n)
      (relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
        ({∞} : Set (OnePoint (AssociatedCover d n))) q) :=
  associatedBMCoverInfinityRelativeSimplexAction

theorem associatedBMCoverInfinityRelativeSimplex_action_free {d n q : ℕ}
    (σ : ConfigurationGroup n)
    (s : relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
      ({∞} : Set (OnePoint (AssociatedCover d n))) q)
    (fixed : σ • s = s) : σ = 1 :=
  relativePairSimplex_action_free associatedBMCoverRelabel
    associatedBMTotalPointwiseFree associatedBMCoverInfinityRelativeSimplexAction
    (fun _ _ => rfl) σ s fixed

def associatedBMCoverInfinityRelativeOrbitIndex (d n q : ℕ) :=
  freeOrbitIndex (G := ConfigurationGroup n)
    (S := relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
      ({∞} : Set (OnePoint (AssociatedCover d n))) q)

def associatedBMCoverInfinityRelativeOrbitBasis (R : Type) [CommRing R]
    {d n : ℕ} (q : ℕ) :
    Module.Basis
      (ConfigurationGroup n × associatedBMCoverInfinityRelativeOrbitIndex d n q) R
      ((relComplex R (associatedBMCoverInfinityIncl d n)).X q) := by
  let B := relativePairSimplexBasis R
    (X := TopCat.of (OnePoint (AssociatedCover d n)))
    (A := ({∞} : Set (OnePoint (AssociatedCover d n)))) (q := q)
  exact freeOrbitBasis R B associatedBMCoverInfinityRelativeSimplex_action_free

theorem associatedBMCoverInfinityRelativeSimplexGenerator_relabel
    (R : Type) [CommRing R] {d n : ℕ} (q : ℕ)
    (σ : ConfigurationGroup n)
    (s : relativePairSimplexOutside (TopCat.of (OnePoint (AssociatedCover d n)))
      ({∞} : Set (OnePoint (AssociatedCover d n))) q) :
    (associatedBMCoverInfinityRelativeAction R (d := d) (n := n) σ).f q
        (relativePairSimplexGenerator R s) =
      relativePairSimplexGenerator R (σ • s) := by
  have h : simplexι R s.val ≫ (relProj R (associatedBMCoverInfinityIncl d n)).f q ≫
      (associatedBMCoverInfinityRelativeAction R σ).f q =
      simplexι R (σ • s).val ≫ (relProj R (associatedBMCoverInfinityIncl d n)).f q := by
    rw [← HomologicalComplex.comp_f, associatedBMCoverInfinityRelativeAction,
      relProj_comp_relComplexMap, HomologicalComplex.comp_f]
    change simplexι R s.val ≫ (simplicialChainMap R
      (TopCat.toSSet.map (associatedBMCoverRelabelMap σ))).f q ≫ _ = _
    rw [simplexι_chainMap_f_assoc]
    rfl
  exact congrArg (fun f => f 1) h

theorem associatedBMCoverInfinityRelativeOrbitBasis_relabel
    (R : Type) [CommRing R] {d n : ℕ} (q : ℕ)
    (σ τ : ConfigurationGroup n)
    (i : associatedBMCoverInfinityRelativeOrbitIndex d n q) :
    (associatedBMCoverInfinityRelativeAction R (d := d) (n := n) σ).f q
      (associatedBMCoverInfinityRelativeOrbitBasis R q (τ, i)) =
      associatedBMCoverInfinityRelativeOrbitBasis R q (σ * τ, i) := by
  exact freeOrbitBasis_relabel R
    (relativePairSimplexBasis R
      (X := TopCat.of (OnePoint (AssociatedCover d n)))
      (A := ({∞} : Set (OnePoint (AssociatedCover d n)))) (q := q))
    associatedBMCoverInfinityRelativeSimplex_action_free
    (fun σ => ((associatedBMCoverInfinityRelativeAction R σ).f q).hom)
    (fun σ s => by
      rw [relativePairSimplexBasis_apply, relativePairSimplexBasis_apply]
      exact associatedBMCoverInfinityRelativeSimplexGenerator_relabel R q σ s)
    σ τ i

end NRR.PrimePowerTopology
