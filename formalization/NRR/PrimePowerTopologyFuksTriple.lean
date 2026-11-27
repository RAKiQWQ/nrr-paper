import NRR.PrimePowerTopologyFuksExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Relative homology for three nested compactified Fuks levels, with the
actual maps of pairs and arbitrary orientation character. -/

noncomputable section
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n] (χ : Equiv.Perm (Fin n) →* Rˣ)

private def levelProjection (k : ℕ) :
    Csing R (TopCat.of (compactifiedFuksLevel d n k)) ⟶ twistedFuksLevelComplex R (d := d) χ k :=
  twistedChainProj R χ _ (fuksLevelAction R k)

private theorem levelProjection_f {k l : ℕ} (h : k ≤ l) :
    levelProjection R (d := d) χ k ≫ twistedFuksInclusion R χ h =
      CsingMap R (compactifiedFuksInclusion h) ≫ levelProjection R χ l :=
  twistedChainProj_map R χ _ _ _ _ (CsingMap_equivariant R _ _ _
    (fun σ => (compactifiedFuksInclusion_equivariant h σ).symm))

private theorem levelProjection_g {k l : ℕ} (h : k ≤ l) :
    levelProjection R (d := d) χ l ≫ twistedFuksQuotient R χ h =
      relProj R (compactifiedFuksInclusion h) ≫ twistedFuksRelativeProj R χ h :=
  twistedChainProj_map R χ _ _ _ _ (fun σ =>
    (relProj_comp_relComplexMap R _ _ (compactifiedFuksInclusion_equivariant h σ)).symm)

theorem twistedFuksInclusion_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    twistedFuksInclusion R (d := d) χ hab ≫ twistedFuksInclusion R χ hbc =
      twistedFuksInclusion R χ (hab.trans hbc) := by
  have hπ : Epi (levelProjection R (d := d) χ a) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [← Category.assoc, levelProjection_f, Category.assoc, levelProjection_f,
    ← Category.assoc, ← CsingMap_comp, levelProjection_f]
  rfl

private theorem twistedFuksInclusion_refl (a : ℕ) :
    twistedFuksInclusion R (d := d) χ (le_refl a) = 𝟙 _ := by
  have hπ : Epi (levelProjection R (d := d) χ a) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [Category.comp_id, levelProjection_f]
  change CsingMap R (𝟙 _) ≫ _ = _
  rw [CsingMap_id, Category.id_comp]

/-- Naturality of the quotient on absolute twisted chains for maps of pairs
of levels. -/
theorem twistedFuksQuotient_naturality {a b c e : ℕ}
    (hab : a ≤ b) (hce : c ≤ e) (hac : a ≤ c) (hbe : b ≤ e) :
    twistedFuksQuotient R (d := d) χ hab ≫ twistedFuksRelativeMap R χ hab hce hac hbe =
      twistedFuksInclusion R χ hbe ≫ twistedFuksQuotient R χ hce := by
  have hπ : Epi (levelProjection R (d := d) χ b) := coequalizer.π_epi
  apply hπ.left_cancellation
  rw [← Category.assoc, levelProjection_g, Category.assoc, twistedFuksRelativeProj_map,
    ← Category.assoc, fuksRelativeMap, relProj_comp_relComplexMap,
    Category.assoc, ← levelProjection_g, ← Category.assoc, ← levelProjection_f, Category.assoc]

/-- The maps are induced by the inclusions of pairs
`(B,A) → (C,A) → (C,B)` for the indicated filtration levels. -/
def twistedFuksTriple {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk
    (twistedFuksRelativeMap R (d := d) χ hab (hab.trans hbc) (le_refl a) hbc)
    (twistedFuksRelativeMap R (d := d) χ (hab.trans hbc) hbc hab (le_refl c)) (by
      have hπ : Epi (twistedFuksQuotient R (d := d) χ hab) :=
        (twistedFuksPair_shortExact R (d := d) χ hab).epi_g
      apply hπ.left_cancellation
      rw [← Category.assoc, twistedFuksQuotient_naturality, Category.assoc,
        twistedFuksQuotient_naturality, twistedFuksInclusion_refl, Category.id_comp,
        comp_zero]
      exact (twistedFuksPair R (d := d) χ hbc).zero)

/-- For degreewise short exact presentations of B/A, C/A and C/B, the
maps induced by a nested pair of inclusions give the third exact row. -/
private theorem quotientTriple_shortExact
    {A B C Q P V : ChainComplex (ModuleCat R) ℕ}
    {i : A ⟶ B} {j : B ⟶ C} {k : A ⟶ C} {p : B ⟶ Q} {s : C ⟶ P} {t : C ⟶ V}
    {u : Q ⟶ P} {v : P ⟶ V}
    (wAB : i ≫ p = 0) (wAC : k ≫ s = 0) (wBC : j ≫ t = 0) (wT : u ≫ v = 0)
    (h₁ : (ShortComplex.mk i p wAB).ShortExact) (h₂ : (ShortComplex.mk k s wAC).ShortExact)
    (h₃ : (ShortComplex.mk j t wBC).ShortExact)
    (fcomp : i ≫ j = k) (square : p ≫ u = j ≫ s) (quotient : s ≫ v = t) :
    (ShortComplex.mk u v wT).ShortExact := by
  let AB := ShortComplex.mk i p wAB
  let AC := ShortComplex.mk k s wAC
  let BC := ShortComplex.mk j t wBC
  let T := ShortComplex.mk u v wT
  apply HomologicalComplex.shortExact_of_degreewise_shortExact T
  intro q
  let E := HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) q
  have hAB : (AB.map E).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact AB).mp
      h₁ q
  have hAC : (AC.map E).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact AC).mp
      h₂ q
  have hBC : (BC.map E).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact BC).mp
      h₃ q
  have inc (x : AB.X₁.X q) : BC.f.f q (AB.f.f q x) = AC.f.f q x :=
    congrArg (fun m => m.f q x) fcomp
  have sq (x : AB.X₂.X q) : T.f.f q (AB.g.f q x) = AC.g.f q (BC.f.f q x) :=
    congrArg (fun m => m.f q x) square
  have proj (x : AC.X₂.X q) : T.g.f q (AC.g.f q x) = BC.g.f q x :=
    congrArg (fun m => m.f q x) quotient
  refine ShortComplex.ShortExact.mk' ((T.map E).moduleCat_exact_iff.mpr ?_)
    ((ModuleCat.mono_iff_injective _).mpr ?_) ((ModuleCat.epi_iff_surjective _).mpr ?_)
  · intro y hy
    obtain ⟨z, rfl⟩ := hAC.moduleCat_surjective_g y
    obtain ⟨x, hx⟩ := (BC.map E).moduleCat_exact_iff.mp hBC.exact z ((proj z).symm.trans hy)
    exact ⟨AB.g.f q x, (sq x).trans (congrArg (AC.g.f q) hx)⟩
  · apply (injective_iff_map_eq_zero (T.f.f q).hom).mpr
    intro y hy
    obtain ⟨x, rfl⟩ := hAB.moduleCat_surjective_g y
    obtain ⟨z, hz⟩ := (AC.map E).moduleCat_exact_iff.mp hAC.exact (BC.f.f q x)
      ((sq x).symm.trans hy)
    have hx := hBC.moduleCat_injective_f ((inc z).trans hz)
    exact (congrArg (AB.g.f q) hx).symm.trans ((AB.map E).moduleCat_zero_apply z)
  · intro y
    obtain ⟨x, hx⟩ := hBC.moduleCat_surjective_g y
    exact ⟨AC.g.f q x, (proj x).trans hx⟩

set_option maxHeartbeats 1000000 in
/-- The three relative twisted chain complexes of a triple form a short exact sequence. -/
theorem twistedFuksTriple_shortExact {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (twistedFuksTriple R (d := d) χ hab hbc).ShortExact := by
  apply quotientTriple_shortExact R
    (i := twistedFuksInclusion R (d := d) χ hab) (j := twistedFuksInclusion R χ hbc)
    (k := twistedFuksInclusion R χ (hab.trans hbc))
    (p := twistedFuksQuotient R χ hab) (s := twistedFuksQuotient R χ (hab.trans hbc))
    (t := twistedFuksQuotient R χ hbc)
    (u := twistedFuksRelativeMap R χ hab (hab.trans hbc) (le_refl a) hbc)
    (v := twistedFuksRelativeMap R χ (hab.trans hbc) hbc hab (le_refl c))
    (twistedFuksPair R χ hab).zero (twistedFuksPair R χ (hab.trans hbc)).zero
    (twistedFuksPair R χ hbc).zero (twistedFuksTriple R χ hab hbc).zero
    (twistedFuksPair_shortExact R χ hab) (twistedFuksPair_shortExact R χ (hab.trans hbc))
    (twistedFuksPair_shortExact R χ hbc) (twistedFuksInclusion_comp R χ hab hbc)
    (twistedFuksQuotient_naturality R χ hab (hab.trans hbc) (le_refl a) hbc)
  rw [twistedFuksQuotient_naturality, twistedFuksInclusion_refl, Category.id_comp]

/-- Quotient the two absolute terms of the pair (C,B) by A; the relative
term C/B is carried identically to the last term of the triple. -/
def twistedFuksPairToTriple {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    twistedFuksPair R (d := d) χ hbc ⟶ twistedFuksTriple R (d := d) χ hab hbc where
  τ₁ := twistedFuksQuotient R χ hab
  τ₂ := twistedFuksQuotient R χ (hab.trans hbc)
  τ₃ := 𝟙 _
  comm₁₂ := twistedFuksQuotient_naturality R χ hab (hab.trans hbc) (le_refl a) hbc
  comm₂₃ := by
    change twistedFuksQuotient R χ (hab.trans hbc) ≫
      twistedFuksRelativeMap R χ (hab.trans hbc) hbc hab (le_refl c) =
      twistedFuksQuotient R χ hbc ≫ 𝟙 _
    rw [twistedFuksQuotient_naturality, twistedFuksInclusion_refl, Category.id_comp,
      Category.comp_id]

/-- The differential obtained from the two level pairs is exactly the
connecting morphism of the actual relative triple. -/
theorem twistedFuksDifferential_eq_tripleδ {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    twistedFuksDifferential R (d := d) χ hab hbc q =
      (twistedFuksTriple_shortExact R (d := d) χ hab hbc).δ (q+1) q rfl := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (twistedFuksPairToTriple R (d := d) χ hab hbc) (twistedFuksPair_shortExact R χ hbc)
    (twistedFuksTriple_shortExact R χ hab hbc) (q+1) q rfl
  change twistedFuksDifferential R χ hab hbc q =
    HomologicalComplex.homologyMap (𝟙 _) (q+1) ≫ _ at h
  simpa only [HomologicalComplex.homologyMap_id, Category.id_comp] using h

/-- In relative homology a class survives the passage from (B,A) to (C,A)
injectively in degree q exactly when the incoming degree-(q+1) boundary is zero. -/
theorem mono_twistedFuksRelativeInclusion_iff {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    Mono (HomologicalComplex.homologyMap
      (twistedFuksRelativeMap R (d := d) χ hab (hab.trans hbc) (le_refl a) hbc) q) ↔
      twistedFuksDifferential R (d := d) χ hab hbc q = 0 := by
  let T := twistedFuksTriple R (d := d) χ hab hbc
  have ht := twistedFuksTriple_shortExact R (d := d) χ hab hbc
  rw [twistedFuksDifferential_eq_tripleδ]
  change Mono (HomologicalComplex.homologyMap T.f q) ↔ ht.δ (q+1) q rfl = 0
  constructor
  · intro hm
    exact (cancel_mono (HomologicalComplex.homologyMap T.f q)).mp
      ((ht.δ_comp (q+1) q rfl).trans zero_comp.symm)
  · exact (ht.homology_exact₁ (q+1) q rfl).mono_g

end NRR.PrimePowerTopology
