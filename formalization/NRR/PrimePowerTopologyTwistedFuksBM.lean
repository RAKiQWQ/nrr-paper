import NRR.PrimePowerTopologyAssociatedBM
import NRR.PrimePowerTopologyTwistedFuksPersistence

/-! Identification of the terminal Fuks pair with the compactified BM
source, before and after taking the character quotient. -/

noncomputable section
open CategoryTheory Limits Set Topology
open scoped OnePoint
open NRR.SingularHomology NRR.PrimePower

namespace NRR.PrimePowerTopology

/-- An equivariant chain isomorphism descends through the actual chain
cokernels. Its inverse is automatically equivariant. -/
def twistedChainIsoOfEquivariant {R G : Type} [CommRing R] [Group G] (χ : G →* Rˣ)
    {K L : ChainComplex (ModuleCat R) ℕ} (ρ : G → (K ⟶ K)) (τ : G → (L ⟶ L))
    (e : K ≅ L) (h : ∀ g, ρ g ≫ e.hom = e.hom ≫ τ g) :
    twistedChainComplex R χ K ρ ≅ twistedChainComplex R χ L τ := by
  have hi (g : G) : τ g ≫ e.inv = e.inv ≫ ρ g := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h g, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨twistedChainMap R χ K ρ τ e.hom h, twistedChainMap R χ L τ ρ e.inv hi, ?_, ?_⟩
  · have hπ : Epi (twistedChainProj R χ K ρ) := coequalizer.π_epi
    apply hπ.left_cancellation
    simp only [twistedChainProj_map_assoc, Category.assoc, twistedChainProj_map,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · have hπ : Epi (twistedChainProj R χ L τ) := coequalizer.π_epi
    apply hπ.left_cancellation
    simp only [twistedChainProj_map_assoc, Category.assoc, twistedChainProj_map,
      Iso.inv_hom_id_assoc, Category.comp_id]

/-- An isomorphism of topological pairs induces an isomorphism of their
ordinary relative singular complexes. -/
def singularPairChainIso {R : Type} [CommRing R]
    {A X B Y : TopCat.{0}} (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    (u : A ≅ B) (v : X ≅ Y) (w : i ≫ v.hom = u.hom ≫ j) :
    relComplex R i ≅ relComplex R j := by
  letI : IsIso (CsingMap R u.hom) := by unfold CsingMap; infer_instance
  letI : IsIso (CsingMap R v.hom) := by unfold CsingMap; infer_instance
  exact cokernel.mapIso (CsingMap R i) (CsingMap R j)
    (asIso (CsingMap R u.hom)) (asIso (CsingMap R v.hom))
    (by change CsingMap R i ≫ CsingMap R v.hom = CsingMap R u.hom ≫ CsingMap R j
        rw [← CsingMap_comp, ← CsingMap_comp, w])

variable (R : Type) [CommRing R] (d n : ℕ) [NeZero n]

private def topFuksBMHomeomorph :
    compactifiedFuksLevel (d+1) n ((d+1)*n) ≃ₜ OnePoint (Configuration (d+2) n) :=
  (Homeomorph.setCongr (compactifiedFuksLevel_top (d+1) n)).trans (Homeomorph.Set.univ _)

private def lowerFuksBMHomeomorph :
    compactifiedFuksLevel (d+1) n d ≃ₜ ({∞} : Set (OnePoint (Configuration (d+2) n))) :=
  Homeomorph.setCongr (compactifiedFuksLevel_eq_infty_of_lt (Nat.lt_succ_self d))

/-- The upper factor forgets membership in the full Fuks level. The lower
factor identifies the singleton infinity on each side of the pair. -/
def topFuksBMTwistedChainIso (χ : Equiv.Perm (Fin n) →* Rˣ) (hn : 2 ≤ n) :
    twistedFuksRelativeComplex R (d := d+1) χ (show d ≤ (d+1)*n by nlinarith) ≅
      associatedBMTwistedSource R (d := d+2) χ := by
  let h : d ≤ (d+1)*n := by nlinarith
  let i := compactifiedFuksInclusion (d := d+1) (n := n) h
  let j := associatedBMSourceIncl (d+2) n
  let u := TopCat.isoOfHomeo (X := TopCat.of (compactifiedFuksLevel (d+1) n d))
    (Y := TopCat.of ({∞} : Set (OnePoint (Configuration (d+2) n)))) (lowerFuksBMHomeomorph d n)
  let v := TopCat.isoOfHomeo (X := TopCat.of (compactifiedFuksLevel (d+1) n ((d+1)*n)))
    (Y := TopCat.of (OnePoint (Configuration (d+2) n))) (topFuksBMHomeomorph d n)
  have w : i ≫ v.hom = u.hom ≫ j := rfl
  let e := singularPairChainIso (R := R) i j u v w
  apply twistedChainIsoOfEquivariant χ (fuksRelativeRelabel R h) (associatedBMSourceRelativeAction R) e
  intro g
  change relComplexMap R i i _ ≫ relComplexMap R i j w =
    relComplexMap R i j w ≫ relComplexMap R j j _
  apply relativeSingularChainMap_equivariant R i j
    (fun g => compactifiedFuksRelabelMap g) (fun g => compactifiedFuksRelabelMap g)
    (fun _ => 𝟙 _) associatedBMSourceRelabelMap
    (compactifiedFuksInclusion_equivariant h) associatedBMSourceIncl_equivariant w
  intro σ
  rfl

/-- In the compactified configuration pair itself, the minimal class has
nonzero image for a power-of-two number of labels. -/
theorem bm_twistedMinimalClass_two_pow_ne_zero {d n a : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (hpow : n = 2^a)
    (i₀ : Fin n) :
    HomologicalComplex.homologyMap (topFuksBMTwistedChainIso (ZMod 2) d n χ hn).hom ((d+1)+n)
      (HomologicalComplex.homologyMap (twistedFuksRelativeMap (ZMod 2) (d := d+1) χ
        (Nat.le_succ d) (show d ≤ (d+1)*n by nlinarith) (le_refl d)
        (show d+1 ≤ (d+1)*n by nlinarith)) ((d+1)+n)
          (coherentTwistedMinimalClass (ZMod 2) χ (show 0 < d+1 by omega) i₀)) ≠ 0 := by
  let e := topFuksBMTwistedChainIso (ZMod 2) d n χ hn
  let f := HomologicalComplex.homologyMap e.hom ((d+1)+n)
  intro hz
  apply twistedMinimalClass_two_pow_survives χ hn hpow i₀
  exact (ModuleCat.mono_iff_injective f).mp inferInstance (hz.trans (map_zero f.hom).symm)

end NRR.PrimePowerTopology
