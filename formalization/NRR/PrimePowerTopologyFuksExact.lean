import NRR.PrimePowerTopologyTwistedRelativeExact

/-! The long exact sequences of the compactified Fuks filtration with twisted
coefficients. In particular the coefficient ring may have prime characteristic. -/

noncomputable section
open CategoryTheory Limits Opposite Simplicial
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

section Pair

variable {G : Type} [Group G] (χ : G →* Rˣ) {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] (α : G → (A ⟶ A)) (β : G → (X ⟶ X))
    (comm : ∀ a, i ≫ β a = α a ≫ i)

/-- Singular chains of an invariant pair, taking the twisted coinvariants
of its absolute and relative chain complexes. -/
def twistedSingularPair : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  twistedShortComplex R χ (relShortComplex R i)
    (fun a => CsingMap R (α a)) (fun a => CsingMap R (β a))
    (fun a => relComplexMap R i i (comm a))
    (CsingMap_equivariant R α β i (fun a => (comm a).symm))
    (fun a => (relProj_comp_relComplexMap R i i (comm a)).symm)

theorem twistedSingularPair_shortExact [∀ a, IsIso (α a)] [∀ a, IsIso (β a)] :
    (twistedSingularPair R χ i α β comm).ShortExact := by
  let S := relShortComplex R i
  have hS := relShortComplex_shortExact R i
  letI : Epi S.g := hS.epi_g
  have ⟨he, hq⟩ := twistedShortComplex_exact R χ S _ _ _
    (CsingMap_equivariant R α β i (fun a => (comm a).symm))
    (fun a => (relProj_comp_relComplexMap R i i (comm a)).symm) hS.exact
  refine { exact := he, mono_f := ?_, epi_g := hq }
  have inj (n : ℕ) : Function.Injective ((TopCat.toSSet.map i).app (op ⦋n⦌)) := by
    intro s t h
    apply (TopCat.toSSetObjEquiv A _).injective
    ext x
    exact (TopCat.mono_iff_injective i).mp inferInstance
      (congrArg (fun z => TopCat.toSSetObjEquiv X _ z x) h)
  apply mono_twistedChainMap_of_retraction R χ _ _ (CsingMap R i)
    (CsingMap_equivariant R α β i (fun a => (comm a).symm))
    (fun n => mvRetr R (TopCat.toSSet.map i) n)
  · intro a n
    apply simplicialRetraction_equivariant R (TopCat.toSSet.map i)
      (TopCat.toSSet.map (α a)) (TopCat.toSSet.map (β a)) _ n (inj n)
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  · exact fun n => simplicialChainMap_f_comp_mvRetr R _ (inj n)

end Pair

variable {d n : ℕ} [NeZero n] (χ : Equiv.Perm (Fin n) →* Rˣ)

def fuksLevelAction (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    Csing R (TopCat.of (compactifiedFuksLevel d n k)) ⟶
      Csing R (TopCat.of (compactifiedFuksLevel d n k)) :=
  CsingMap R (compactifiedFuksRelabelMap σ)

def twistedFuksLevelComplex (k : ℕ) : ChainComplex (ModuleCat R) ℕ :=
  twistedChainComplex R χ _ (fuksLevelAction R (d := d) k)

def twistedFuksInclusion {a b : ℕ} (hab : a ≤ b) :
    twistedFuksLevelComplex R (d := d) χ a ⟶ twistedFuksLevelComplex R (d := d) χ b :=
  twistedChainMap R χ _ (fuksLevelAction R a) (fuksLevelAction R b)
    (CsingMap R (compactifiedFuksInclusion hab))
    (CsingMap_equivariant R _ _ _ (fun σ => (compactifiedFuksInclusion_equivariant hab σ).symm))

def twistedFuksQuotient {a b : ℕ} (hab : a ≤ b) :
    twistedFuksLevelComplex R (d := d) χ b ⟶ twistedFuksRelativeComplex R (d := d) χ hab :=
  twistedChainMap R χ _ (fuksLevelAction R b) (fuksRelativeRelabel R hab)
    (relProj R (compactifiedFuksInclusion hab))
    (fun σ => (relProj_comp_relComplexMap R _ _ (compactifiedFuksInclusion_equivariant hab σ)).symm)

/-- The absolute chains of each compactified level and the actual relative
chains of the pair, with the same character on all three terms. -/
def twistedFuksPair {k l : ℕ} (h : k ≤ l) : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (twistedFuksInclusion R (d := d) χ h) (twistedFuksQuotient R (d := d) χ h)
    (twistedSingularPair R χ (compactifiedFuksInclusion (d := d) h)
      _ _ (compactifiedFuksInclusion_equivariant h)).zero

instance isIso_compactifiedFuksRelabelMap {k : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsIso (compactifiedFuksRelabelMap (d := d) (k := k) σ) :=
  (TopCat.isoOfHomeo (X := TopCat.of (compactifiedFuksLevel d n k))
    (Y := TopCat.of (compactifiedFuksLevel d n k)) (compactifiedFuksRelabel σ)).isIso_hom

theorem twistedFuksPair_shortExact {k l : ℕ} (h : k ≤ l) :
    (twistedFuksPair R (d := d) χ h).ShortExact :=
  twistedSingularPair_shortExact R χ _ _ _ _

/-- The six consecutive terms across the connecting morphism of a level pair. -/
theorem twistedFuksPair_LES_exact {k l : ℕ} (h : k ≤ l) (q : ℕ) :
    (HomologicalComplex.HomologySequence.composableArrows₅
      (twistedFuksPair_shortExact R (d := d) χ h) (q+1) q rfl).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact _ _ _ _

/-- The boundary between two successive relative groups. It is induced by
the connecting morphism of the upper pair followed by the lower quotient. -/
def twistedFuksDifferential {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    (twistedFuksRelativeComplex R (d := d) χ hbc).homology (q+1) ⟶
      (twistedFuksRelativeComplex R (d := d) χ hab).homology q :=
  (twistedFuksPair_shortExact R (d := d) χ hbc).δ (q+1) q rfl ≫
    HomologicalComplex.homologyMap (twistedFuksPair R (d := d) χ hab).g q

theorem twistedFuksDifferential_comp {a b c e : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (q : ℕ) :
    twistedFuksDifferential R (d := d) χ hbc hce (q+1) ≫
      twistedFuksDifferential R (d := d) χ hab hbc q = 0 := by
  unfold twistedFuksDifferential
  rw [Category.assoc, ← Category.assoc (HomologicalComplex.homologyMap _ _),
    (twistedFuksPair_shortExact R (d := d) χ hbc).comp_δ (q+1) q rfl, zero_comp, comp_zero]

/-- If the lower level has zero homology in the tested degree, the relative
boundary detects the entire kernel of the next absolute inclusion: that
inclusion is injective exactly when the actual relative boundary vanishes. -/
theorem mono_twistedFuksInclusion_iff_differential_zero {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ)
    (lower : IsZero ((twistedFuksPair R (d := d) χ hab).X₁.homology q)) :
    Mono (HomologicalComplex.homologyMap (twistedFuksPair R (d := d) χ hbc).f q) ↔
      twistedFuksDifferential R (d := d) χ hab hbc q = 0 := by
  let U := twistedFuksPair R (d := d) χ hbc
  let L := twistedFuksPair R (d := d) χ hab
  have hu := twistedFuksPair_shortExact R (d := d) χ hbc
  have hl := twistedFuksPair_shortExact R (d := d) χ hab
  letI : Mono (HomologicalComplex.homologyMap L.g q) :=
    (hl.homology_exact₂ q).mono_g (lower.eq_zero_of_src _)
  change Mono (HomologicalComplex.homologyMap U.f q) ↔
    hu.δ (q+1) q rfl ≫ HomologicalComplex.homologyMap L.g q = 0
  constructor
  · intro hi
    have hδ : hu.δ (q+1) q rfl = 0 :=
      (cancel_mono (HomologicalComplex.homologyMap U.f q)).mp
        ((hu.δ_comp (q+1) q rfl).trans zero_comp.symm)
    rw [hδ, zero_comp]
  · intro h
    exact (hu.homology_exact₁ (q+1) q rfl).mono_g
      ((cancel_mono (HomologicalComplex.homologyMap L.g q)).mp (h.trans zero_comp.symm))

end NRR.PrimePowerTopology
