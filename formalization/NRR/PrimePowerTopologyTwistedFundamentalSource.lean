import NRR.PrimePowerTopologyTwistedFundamental
import NRR.PrimePowerTopologyTwistedFundamentalTransfer

/-! Actual free orbit bases and injective signed transfer for the
infinity-relative configuration-space source complex. -/

noncomputable section
open Set Topology CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

private theorem fundamentalSourceRelabel_one {d n : ℕ}
    (z : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel (1 : ConfigurationGroup n) z = z := by
  induction z using OnePoint.rec <;> rfl

private theorem fundamentalSourceRelabel_mul {d n : ℕ} (g h : ConfigurationGroup n)
    (z : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel (g*h) z =
      compactifiedConfigurationRelabel g (compactifiedConfigurationRelabel h z) := by
  induction z using OnePoint.rec <;> rfl

private theorem fundamentalSourceInfinity_relabel {d n : ℕ}
    (g : ConfigurationGroup n) (z : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel g z ∈ ({∞} : Set (OnePoint (Configuration d n))) ↔
      z ∈ ({∞} : Set (OnePoint (Configuration d n))) := by
  induction z using OnePoint.rec <;> simp [compactifiedConfigurationRelabel]

def twistedFundamentalSourceSimplexAction {d n q : ℕ} :
    MulAction (ConfigurationGroup n)
      (relativePairSimplexOutside (TopCat.of (OnePoint (Configuration d n))) {∞} q) :=
  relativePairSimplexOutsideMulAction compactifiedConfigurationRelabel
    fundamentalSourceInfinity_relabel fundamentalSourceRelabel_one
    fundamentalSourceRelabel_mul q

instance twistedFundamentalSourceSimplexMulAction {d n q : ℕ} :
    MulAction (ConfigurationGroup n)
      (relativePairSimplexOutside (TopCat.of (OnePoint (Configuration d n))) {∞} q) :=
  twistedFundamentalSourceSimplexAction

theorem twistedFundamentalSourceSimplex_action_free {d n q : ℕ}
    (g : ConfigurationGroup n)
    (s : relativePairSimplexOutside (TopCat.of (OnePoint (Configuration d n))) {∞} q)
    (hs : g • s = s) : g = 1 := by
  apply relativePairSimplex_action_free compactifiedConfigurationRelabel
    (fun g z hz hfix => (compactifiedConfigurationRelabel_fix g z hfix).resolve_right
      (fun he => hz (by simp [he])))
    twistedFundamentalSourceSimplexAction (fun _ _ => rfl) g s hs

def twistedFundamentalSourceOrbitIndex (d n q : ℕ) :=
  freeOrbitIndex (G := ConfigurationGroup n)
    (S := relativePairSimplexOutside (TopCat.of (OnePoint (Configuration d n))) {∞} q)

def twistedFundamentalSourceOrbitBasis (R : Type) [CommRing R] {d n : ℕ} (q : ℕ) :
    Module.Basis (ConfigurationGroup n × twistedFundamentalSourceOrbitIndex d n q) R
      ((relComplex R (associatedBMSourceIncl d n)).X q) :=
  freeOrbitBasis R (relativePairSimplexBasis R)
    twistedFundamentalSourceSimplex_action_free

theorem twistedFundamentalSourceSimplexGenerator_relabel
    (R : Type) [CommRing R] {d n : ℕ} (q : ℕ) (g : ConfigurationGroup n)
    (s : relativePairSimplexOutside (TopCat.of (OnePoint (Configuration d n))) {∞} q) :
    (associatedBMSourceRelativeAction R (d := d) (n := n) g).f q
      (relativePairSimplexGenerator R s) = relativePairSimplexGenerator R (g • s) := by
  have h : simplexι R s.val ≫ (relProj R (associatedBMSourceIncl d n)).f q ≫
      (associatedBMSourceRelativeAction R g).f q =
      simplexι R (g • s).val ≫ (relProj R (associatedBMSourceIncl d n)).f q := by
    rw [← HomologicalComplex.comp_f, associatedBMSourceRelativeAction,
      relProj_comp_relComplexMap, HomologicalComplex.comp_f]
    change simplexι R s.val ≫ (simplicialChainMap R
      (TopCat.toSSet.map (associatedBMSourceRelabelMap g))).f q ≫ _ = _
    rw [simplexι_chainMap_f_assoc]
    rfl
  exact congrArg (fun f => f 1) h

theorem twistedFundamentalSourceOrbitBasis_relabel
    (R : Type) [CommRing R] {d n : ℕ} (q : ℕ) (g h : ConfigurationGroup n)
    (i : twistedFundamentalSourceOrbitIndex d n q) :
    (associatedBMSourceRelativeAction R (d := d) (n := n) g).f q
      (twistedFundamentalSourceOrbitBasis R q (h,i)) =
      twistedFundamentalSourceOrbitBasis R q (g*h,i) := by
  exact freeOrbitBasis_relabel R (relativePairSimplexBasis R)
    twistedFundamentalSourceSimplex_action_free
    (fun g => ((associatedBMSourceRelativeAction R g).f q).hom)
    (fun g s => by
      rw [relativePairSimplexBasis_apply, relativePairSimplexBasis_apply]
      exact twistedFundamentalSourceSimplexGenerator_relabel R q g s) g h i

theorem twistedFundamentalSourceAction_mul (R : Type) [CommRing R] {d n : ℕ}
    (g h : ConfigurationGroup n) :
    associatedBMSourceRelativeAction R (d := d) (g*h) =
      associatedBMSourceRelativeAction R h ≫ associatedBMSourceRelativeAction R g := by
  have hp : Epi (relProj R (associatedBMSourceIncl d n)) := coequalizer.π_epi
  apply hp.left_cancellation
  simp only [associatedBMSourceRelativeAction, relProj_comp_relComplexMap_assoc,
    relProj_comp_relComplexMap]
  rw [← Category.assoc, ← CsingMap_comp]
  congr 2
  ext z
  exact fundamentalSourceRelabel_mul g h z

/-- The genuine signed transfer for the infinity-relative BM source. -/
def twistedFundamentalSourceTransfer (R : Type) [CommRing R] {d n : ℕ}
    (χ : ConfigurationGroup n →* Rˣ) :
    associatedBMTwistedSource R (d := d) χ ⟶ relComplex R (associatedBMSourceIncl d n) :=
  twistedChainTransferDesc R χ _ (associatedBMSourceRelativeAction R)
    (twistedFundamentalSourceAction_mul R)

theorem twistedFundamentalSourceTransfer_injective
    (R : Type) [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ) (q : ℕ) :
    Function.Injective ((twistedFundamentalSourceTransfer R (d := d) χ).f q) :=
  twistedFundamentalTransfer_injective R χ _ (associatedBMSourceRelativeAction R)
    (twistedFundamentalSourceAction_mul R) (twistedFundamentalSourceOrbitBasis R)
    (twistedFundamentalSourceOrbitBasis_relabel R) q

end NRR.PrimePowerTopology
