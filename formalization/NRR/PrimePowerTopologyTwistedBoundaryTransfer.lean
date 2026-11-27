import NRR.PrimePowerTopologyMinimalTwistedHomology
import NRR.PrimePowerTopologyFuksTriple

/-! Naturality of the genuine signed chain transfer, including the actual
connecting morphisms of the Fuks filtration. No homology projection is
assumed to be epimorphic, and no group-order scalar is inverted. -/

noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

section TransferNaturality

variable {G : Type} [Group G] [Fintype G] (χ : G →* Rˣ)
    {K L : ChainComplex (ModuleCat R) ℕ}
    (ρ : G → (K ⟶ K)) (τ : G → (L ⟶ L))
    (f : K ⟶ L) (equivariant : ∀ g, ρ g ≫ f = f ≫ τ g)

include equivariant in
/-- The finite signed transfer commutes with each equivariant chain map. -/
theorem twistedChainTransfer_naturality :
    twistedChainTransfer R χ K ρ ≫ f = f ≫ twistedChainTransfer R χ L τ := by
  classical
  rw [twistedChainTransfer, twistedChainTransfer, Preadditive.sum_comp,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Linear.smul_comp, Linear.comp_smul, equivariant]

/-- Naturality after descending through the actual chain cokernels. The
only epimorphism cancelled here is the chain-level cokernel projection. -/
@[reassoc]
theorem twistedChainTransferDesc_naturality
    (lawρ : ∀ g h, ρ (g*h) = ρ h ≫ ρ g)
    (lawτ : ∀ g h, τ (g*h) = τ h ≫ τ g) :
    twistedChainMap R χ K ρ τ f equivariant ≫ twistedChainTransferDesc R χ L τ lawτ =
      twistedChainTransferDesc R χ K ρ lawρ ≫ f := by
  have hπ : Epi (twistedChainProj R χ K ρ) := coequalizer.π_epi
  apply hπ.left_cancellation
  simp only [twistedChainProj_map_assoc, twistedChainProj_transferDesc_assoc,
    twistedChainProj_transferDesc]
  exact (twistedChainTransfer_naturality R χ ρ τ f equivariant).symm

end TransferNaturality

private theorem relativeQuotientTriple_shortExact
    {A B C Q P V : ChainComplex (ModuleCat R) ℕ}
    {i : A ⟶ B} {j : B ⟶ C} {k : A ⟶ C} {p : B ⟶ Q} {s : C ⟶ P} {t : C ⟶ V}
    {u : Q ⟶ P} {v : P ⟶ V}
    (wAB : i ≫ p = 0) (wAC : k ≫ s = 0) (wBC : j ≫ t = 0) (wT : u ≫ v = 0)
    (h₁ : (ShortComplex.mk i p wAB).ShortExact)
    (h₂ : (ShortComplex.mk k s wAC).ShortExact)
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
    (HomologicalComplex.shortExact_iff_degreewise_shortExact AB).mp h₁ q
  have hAC : (AC.map E).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact AC).mp h₂ q
  have hBC : (BC.map E).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact BC).mp h₃ q
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

section Fuks

variable {d n : ℕ} [NeZero n] (χ : Equiv.Perm (Fin n) →* Rˣ)

theorem fuksLevelAction_mul (k : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    fuksLevelAction R (d := d) k (σ*τ) =
      fuksLevelAction R k τ ≫ fuksLevelAction R k σ := by
  unfold fuksLevelAction
  rw [compactifiedFuksRelabelMap_mul, CsingMap_comp]

/-- Transfer from actual twisted absolute chains of a compactified level. -/
def fuksLevelTransfer (k : ℕ) :
    twistedFuksLevelComplex R (d := d) χ k ⟶
      Csing R (TopCat.of (compactifiedFuksLevel d n k)) :=
  twistedChainTransferDesc R χ _ (fuksLevelAction R k) (fuksLevelAction_mul R k)

/-- Transfer from the actual twisted relative chains of any two levels. -/
def fuksRelativeTransfer {a b : ℕ} (hab : a ≤ b) :
    twistedFuksRelativeComplex R (d := d) χ hab ⟶
      fuksRelativeComplex R (d := d) (n := n) hab :=
  twistedChainTransferDesc R χ _ (fuksRelativeRelabel R hab)
    (fuksRelativeRelabel_mul R hab)

@[reassoc]
theorem fuksLevelTransfer_inclusion {a b : ℕ} (hab : a ≤ b) :
    twistedFuksInclusion R (d := d) χ hab ≫ fuksLevelTransfer R χ b =
      fuksLevelTransfer R χ a ≫ CsingMap R (compactifiedFuksInclusion hab) :=
  twistedChainTransferDesc_naturality R χ _ _ _ _ _ _

@[reassoc]
theorem fuksLevelTransfer_quotient {a b : ℕ} (hab : a ≤ b) :
    twistedFuksQuotient R (d := d) χ hab ≫ fuksRelativeTransfer R χ hab =
      fuksLevelTransfer R χ b ≫ relProj R (compactifiedFuksInclusion hab) :=
  twistedChainTransferDesc_naturality R χ _ _ _ _ _ _

/-- Naturality for all actual maps of Fuks pairs, including both arrows
of each three-level relative short exact sequence. -/
@[reassoc]
theorem fuksRelativeTransfer_naturality {a b c e : ℕ}
    (hab : a ≤ b) (hce : c ≤ e) (hac : a ≤ c) (hbe : b ≤ e) :
    twistedFuksRelativeMap R (d := d) χ hab hce hac hbe ≫
        fuksRelativeTransfer R χ hce =
      fuksRelativeTransfer R χ hab ≫ fuksRelativeMap R hab hce hac hbe :=
  twistedChainTransferDesc_naturality R χ _ _ _ _ _ _

/-- Naturality on the homology of the actual relative chain complexes. -/
@[reassoc]
theorem fuksRelativeTransfer_homology_naturality {a b c e : ℕ}
    (hab : a ≤ b) (hce : c ≤ e) (hac : a ≤ c) (hbe : b ≤ e) (q : ℕ) :
    HomologicalComplex.homologyMap
        (twistedFuksRelativeMap R (d := d) χ hab hce hac hbe) q ≫
        HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hce) q =
      HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hab) q ≫
        HomologicalComplex.homologyMap (fuksRelativeMap R hab hce hac hbe) q := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    fuksRelativeTransfer_naturality]

/-- A genuine morphism from the twisted pair sequence to the ordinary
singular-chain pair sequence, with signed transfer on all three terms. -/
def fuksPairTransfer {a b : ℕ} (hab : a ≤ b) :
    twistedFuksPair R (d := d) χ hab ⟶
      relShortComplex R (compactifiedFuksInclusion (d := d) (n := n) hab) where
  τ₁ := fuksLevelTransfer R χ a
  τ₂ := fuksLevelTransfer R χ b
  τ₃ := fuksRelativeTransfer R χ hab
  comm₁₂ := (fuksLevelTransfer_inclusion R χ hab).symm
  comm₂₃ := (fuksLevelTransfer_quotient R χ hab).symm

/-- Naturality of the actual pair connecting map under signed transfer. -/
@[reassoc]
theorem twistedFuksPairδ_transfer {a b : ℕ} (hab : a ≤ b) (q : ℕ) :
    (twistedFuksPair_shortExact R (d := d) χ hab).δ (q+1) q rfl ≫
        HomologicalComplex.homologyMap (fuksLevelTransfer R χ a) q =
      HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hab) (q+1) ≫
        relδ R q (compactifiedFuksInclusion hab) :=
  HomologicalComplex.HomologySequence.δ_naturality (fuksPairTransfer R χ hab)
    (twistedFuksPair_shortExact R χ hab)
    (relShortComplex_shortExact R (compactifiedFuksInclusion hab)) (q+1) q rfl

/-- The ordinary Fuks differential on actual relative singular homology. -/
def fuksDifferential {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    (fuksRelativeComplex R (d := d) (n := n) hbc).homology (q+1) ⟶
      (fuksRelativeComplex R (d := d) (n := n) hab).homology q :=
  relδ R q (compactifiedFuksInclusion hbc) ≫
    HomologicalComplex.homologyMap (relProj R (compactifiedFuksInclusion hab)) q

omit [NeZero n] in
private theorem compactifiedFuksInclusion_refl (a : ℕ) :
    compactifiedFuksInclusion (d := d) (n := n) (le_refl a) = 𝟙 _ := by
  ext x
  rfl

omit [NeZero n] in
private theorem fuksQuotient_naturality {a b c e : ℕ}
    (hab : a ≤ b) (hce : c ≤ e) (hac : a ≤ c) (hbe : b ≤ e) :
    relProj R (compactifiedFuksInclusion (d := d) (n := n) hab) ≫
        fuksRelativeMap R hab hce hac hbe =
      CsingMap R (compactifiedFuksInclusion hbe) ≫
        relProj R (compactifiedFuksInclusion hce) :=
  relProj_comp_relComplexMap R _ _ _

/-- The ordinary relative short complex for three actual compactified levels. -/
def fuksTriple {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk
    (fuksRelativeMap R (d := d) (n := n) hab (hab.trans hbc) (le_refl a) hbc)
    (fuksRelativeMap R (hab.trans hbc) hbc hab (le_refl c)) (by
      have hπ : Epi (relProj R (compactifiedFuksInclusion (d := d) (n := n) hab)) :=
        coequalizer.π_epi
      apply hπ.left_cancellation
      rw [← Category.assoc, fuksQuotient_naturality, Category.assoc,
        fuksQuotient_naturality, compactifiedFuksInclusion_refl, CsingMap_id,
        Category.id_comp, comp_zero]
      exact (relShortComplex R (compactifiedFuksInclusion hbc)).zero)

theorem fuksTriple_shortExact {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (fuksTriple R (d := d) (n := n) hab hbc).ShortExact := by
  apply relativeQuotientTriple_shortExact R
    (i := CsingMap R (compactifiedFuksInclusion (d := d) (n := n) hab))
    (j := CsingMap R (compactifiedFuksInclusion hbc))
    (k := CsingMap R (compactifiedFuksInclusion (hab.trans hbc)))
    (p := relProj R (compactifiedFuksInclusion hab))
    (s := relProj R (compactifiedFuksInclusion (hab.trans hbc)))
    (t := relProj R (compactifiedFuksInclusion hbc))
    (u := fuksRelativeMap R hab (hab.trans hbc) (le_refl a) hbc)
    (v := fuksRelativeMap R (hab.trans hbc) hbc hab (le_refl c))
    (relShortComplex R (compactifiedFuksInclusion hab)).zero
    (relShortComplex R (compactifiedFuksInclusion (hab.trans hbc))).zero
    (relShortComplex R (compactifiedFuksInclusion hbc)).zero (fuksTriple R hab hbc).zero
    (relShortComplex_shortExact R (compactifiedFuksInclusion hab))
    (relShortComplex_shortExact R (compactifiedFuksInclusion (hab.trans hbc)))
    (relShortComplex_shortExact R (compactifiedFuksInclusion hbc))
    (by rw [← CsingMap_comp]; congr 1)
    (fuksQuotient_naturality R hab (hab.trans hbc) (le_refl a) hbc)
  rw [fuksQuotient_naturality, compactifiedFuksInclusion_refl, CsingMap_id,
    Category.id_comp]

def fuksPairToTriple {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    relShortComplex R (compactifiedFuksInclusion (d := d) (n := n) hbc) ⟶
      fuksTriple R (d := d) (n := n) hab hbc where
  τ₁ := relProj R (compactifiedFuksInclusion hab)
  τ₂ := relProj R (compactifiedFuksInclusion (hab.trans hbc))
  τ₃ := 𝟙 _
  comm₁₂ := fuksQuotient_naturality R hab (hab.trans hbc) (le_refl a) hbc
  comm₂₃ := by
    change relProj R (compactifiedFuksInclusion (hab.trans hbc)) ≫
      fuksRelativeMap R (hab.trans hbc) hbc hab (le_refl c) =
      relProj R (compactifiedFuksInclusion hbc) ≫ 𝟙 _
    rw [fuksQuotient_naturality, compactifiedFuksInclusion_refl, CsingMap_id,
      Category.id_comp, Category.comp_id]

theorem fuksDifferential_eq_tripleδ {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    fuksDifferential R (d := d) (n := n) hab hbc q =
      (fuksTriple_shortExact R (d := d) (n := n) hab hbc).δ (q+1) q rfl := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (fuksPairToTriple R (d := d) (n := n) hab hbc)
    (relShortComplex_shortExact R (compactifiedFuksInclusion hbc))
    (fuksTriple_shortExact R hab hbc) (q+1) q rfl
  change fuksDifferential R (d := d) (n := n) hab hbc q =
    HomologicalComplex.homologyMap (𝟙 _) (q+1) ≫ _ at h
  simpa only [HomologicalComplex.homologyMap_id, Category.id_comp] using h

/-- Signed transfer is a morphism between the genuine three-level
twisted and ordinary relative chain short exact sequences. -/
def fuksTripleTransfer {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    twistedFuksTriple R (d := d) χ hab hbc ⟶
      fuksTriple R (d := d) (n := n) hab hbc where
  τ₁ := fuksRelativeTransfer R χ hab
  τ₂ := fuksRelativeTransfer R χ (hab.trans hbc)
  τ₃ := fuksRelativeTransfer R χ hbc
  comm₁₂ := (fuksRelativeTransfer_naturality R χ hab (hab.trans hbc) (le_refl a) hbc).symm
  comm₂₃ := (fuksRelativeTransfer_naturality R χ (hab.trans hbc) hbc hab (le_refl c)).symm

/-- Transfer commutes with the actual relative boundary between successive
Fuks pairs, over arbitrary commutative coefficient rings. -/
@[reassoc]
theorem twistedFuksDifferential_transfer {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    twistedFuksDifferential R (d := d) χ hab hbc q ≫
        HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hab) q =
      HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hbc) (q+1) ≫
        fuksDifferential R (d := d) (n := n) hab hbc q := by
  unfold twistedFuksDifferential fuksDifferential
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    show (twistedFuksPair R χ hab).g ≫ fuksRelativeTransfer R χ hab =
        fuksLevelTransfer R χ b ≫ relProj R (compactifiedFuksInclusion hab) from
      fuksLevelTransfer_quotient R χ hab,
    HomologicalComplex.homologyMap_comp, ← Category.assoc,
    twistedFuksPairδ_transfer, Category.assoc]

/-- The same formula written with the actual twisted triple connecting map. -/
@[reassoc]
theorem twistedFuksTripleδ_transfer {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    (twistedFuksTriple_shortExact R (d := d) χ hab hbc).δ (q+1) q rfl ≫
        HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hab) q =
      HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hbc) (q+1) ≫
        fuksDifferential R (d := d) (n := n) hab hbc q := by
  rw [← twistedFuksDifferential_eq_tripleδ]
  exact twistedFuksDifferential_transfer R χ hab hbc q

/-- Naturality expressed entirely by the two actual triple connecting maps. -/
@[reassoc]
theorem fuksTripleδ_transfer {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    (twistedFuksTriple_shortExact R (d := d) χ hab hbc).δ (q+1) q rfl ≫
        HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hab) q =
      HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hbc) (q+1) ≫
        (fuksTriple_shortExact R (d := d) (n := n) hab hbc).δ (q+1) q rfl :=
  HomologicalComplex.HomologySequence.δ_naturality (fuksTripleTransfer R χ hab hbc)
    (twistedFuksTriple_shortExact R χ hab hbc)
    (fuksTriple_shortExact R hab hbc) (q+1) q rfl

/-- In the first possible target degree, the actual twisted-boundary
detector is computed entirely by ordinary boundary after transfer. -/
@[reassoc]
theorem twistedFuksDifferential_minimalCoefficient {c : ℕ}
    (hbc : d ≤ c) (hd : 0 < d) (i₀ : Fin n) :
    twistedFuksDifferential R (d := d) χ (show d-1 ≤ d by omega) hbc (d+n) ≫
        coherentTwistedMinimalCoefficient R χ hd i₀ =
      HomologicalComplex.homologyMap (fuksRelativeTransfer R χ hbc) (d+n+1) ≫
        fuksDifferential R (d := d) (n := n) (show d-1 ≤ d by omega) hbc (d+n) ≫
          coherentMinimalRelativeCoefficient R hd i₀ 1 := by
  unfold coherentTwistedMinimalCoefficient
  change twistedFuksDifferential R χ (show d-1 ≤ d by omega) hbc (d+n) ≫
      HomologicalComplex.homologyMap
        (fuksRelativeTransfer R χ (show d-1 ≤ d by omega)) (d+n) ≫
      coherentMinimalRelativeCoefficient R hd i₀ 1 = _
  rw [← Category.assoc, twistedFuksDifferential_transfer, Category.assoc]

end Fuks

end NRR.PrimePowerTopology
