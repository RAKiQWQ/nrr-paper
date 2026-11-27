import NRR.PrimePowerTopologyTwistedFundamentalCycle
import NRR.PrimePowerTopologyStaircaseLocalGeometry
import NRR.PrimePowerTopologyStaircaseLocalChart
import NRR.SingularHomologySimplexLocalDetection

/-! At the selected finite configuration, the actual full staircase chain
has exactly one surviving local singular simplex. -/

noncomputable section
open Set Topology CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

def staircaseSelectedComplement {d n : ℕ} (hd : 0 < d) :
    Set (OnePoint (Configuration d n)) :=
  {(staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n))}ᶜ

def staircaseSelectedInfinityMap {d n : ℕ} (hd : 0 < d) :
    TopCat.of ({∞} : Set (OnePoint (Configuration d n))) ⟶
      TopCat.of (staircaseSelectedComplement (n := n) hd) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, by
    have hx : x.val = ∞ := x.property
    rw [hx]
    exact OnePoint.infty_ne_coe _⟩, continuous_subtype_val.subtype_mk _⟩

theorem staircaseSelectedLocalization_square {d n : ℕ} (hd : 0 < d) :
    associatedBMSourceIncl d n ≫ 𝟙 _ =
      staircaseSelectedInfinityMap (n := n) hd ≫
        subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
          (staircaseSelectedComplement (n := n) hd) := rfl

def staircaseSelectedLocalization (R : Type) [CommRing R] {d n : ℕ} (hd : 0 < d) :
    relComplex R (associatedBMSourceIncl d n) ⟶
      relComplex R (subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
        (staircaseSelectedComplement (n := n) hd)) :=
  relComplexMap R _ _ (staircaseSelectedLocalization_square hd)

theorem staircaseRelativeGenerator_localization (R : Type) [CommRing R]
    {d n : ℕ} (hd : 0 < d) (π : Equiv.Perm (Fin (n*d))) :
    configurationStaircaseRelativeGenerator R π ≫
      (staircaseSelectedLocalization R hd).f (n*d) =
      staircaseRelativeGenerator R (X := TopCat.of (OnePoint (Configuration d n)))
        (staircaseSelectedComplement hd) (configurationCubeCollapse d n) π := by
  unfold configurationStaircaseRelativeGenerator staircaseRelativeGenerator
  change simplexι R (configurationStaircaseSSetSimplex π) ≫
    (relProj R (associatedBMSourceIncl d n)).f (n*d) ≫
      (staircaseSelectedLocalization R hd).f (n*d) = _
  rw [← HomologicalComplex.comp_f, staircaseSelectedLocalization,
    relProj_comp_relComplexMap, CsingMap_id, Category.id_comp]
  rfl

theorem staircaseRelativeGenerator_other_local_zero (R : Type) [CommRing R]
    {d n : ℕ} (hd : 0 < d) (π : Equiv.Perm (Fin (n*d)))
    (hπ : π ≠ Equiv.refl _) :
    staircaseRelativeGenerator R (X := TopCat.of (OnePoint (Configuration d n)))
      (staircaseSelectedComplement hd) (configurationCubeCollapse d n) π = 0 := by
  apply staircaseRelativeSimplex_zero R (staircaseSelectedComplement hd)
    (configurationStaircaseSSetSimplex π)
  intro x
  exact configurationStaircaseSimplex_avoids_selected hd π hπ x

/-- Localization kills every chamber except the identity chamber, whose
coefficient is one. This is an equality of actual singular-chain maps. -/
theorem configurationStaircaseChain_localization (R : Type) [CommRing R]
    {d n : ℕ} (hd : 0 < d) :
    staircaseRelativeChain R (X := TopCat.of (OnePoint (Configuration d n)))
      {∞} (configurationCubeCollapse d n) ≫
      (staircaseSelectedLocalization R hd).f (n*d) =
    staircaseRelativeGenerator R (X := TopCat.of (OnePoint (Configuration d n)))
      (staircaseSelectedComplement hd) (configurationCubeCollapse d n) (Equiv.refl _) := by
  classical
  unfold staircaseRelativeChain
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  change (∑ π : Equiv.Perm (Fin (n*d)), (Equiv.Perm.sign π : ℤ) •
    (configurationStaircaseRelativeGenerator R π ≫
      (staircaseSelectedLocalization R hd).f (n*d))) = _
  simp_rw [staircaseRelativeGenerator_localization R hd]
  rw [Finset.sum_eq_single (Equiv.refl _)]
  · simp
  · intro π _ hπ
    rw [staircaseRelativeGenerator_other_local_zero R hd π hπ, smul_zero]
  · simp

theorem configurationTwistedFundamentalChain_transfer_localization (p : ℕ)
    {d n : ℕ} (hd : 0 < d) :
    configurationTwistedFundamentalChain p d n ≫
      (twistedFundamentalSourceTransfer (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)).f (n*d) ≫
      (staircaseSelectedLocalization (ZMod p) hd).f (n*d) =
    staircaseRelativeGenerator (ZMod p) (X := TopCat.of (OnePoint (Configuration d n)))
      (staircaseSelectedComplement hd) (configurationCubeCollapse d n) (Equiv.refl _) := by
  rw [← Category.assoc, configurationTwistedFundamentalChain_transfer p hd,
    configurationStaircaseChain_localization]

def staircaseBarycenterColoring (m : ℕ) : SimplexFundamental.ColoringSubspace m :=
  SimplexFundamental.puncturedColoringSubspace m (staircaseBarycenter m)
    (by intro i; simp [one_div])

def staircaseSelectedIdentityMap (R : Type) [CommRing R] {d n : ℕ} (hd : 0 < d) :
    relComplex R (SimplexFundamental.boundaryIncl (n*d)) ⟶
      relComplex R (subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
        (staircaseSelectedComplement hd)) :=
  relComplexMap R _ _ (staircaseBarycenterColoring (n*d)).square ≫
    relComplexMap R _ _ (staircaseSelectedSimplexPunctured_square hd)

theorem staircaseSelectedIdentityChain_map (R : Type) [CommRing R] {d n : ℕ} (hd : 0 < d) :
    SimplexFundamental.identityRelativeChain R (n*d) ≫
      (staircaseSelectedIdentityMap R hd).f (n*d) =
    staircaseRelativeGenerator R (X := TopCat.of (OnePoint (Configuration d n)))
      (staircaseSelectedComplement hd) (configurationCubeCollapse d n) (Equiv.refl _) := by
  have hp : relProj R (SimplexFundamental.boundaryIncl (n*d)) ≫
      staircaseSelectedIdentityMap R (n := n) hd =
    CsingMap R (TopCat.ofHom (configurationStaircaseSimplex (Equiv.refl (Fin (n*d))))) ≫
      relProj R (subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
        (staircaseSelectedComplement hd)) := by
    unfold staircaseSelectedIdentityMap
    rw [← Category.assoc, relProj_comp_relComplexMap, CsingMap_id,
      Category.id_comp, relProj_comp_relComplexMap]
  unfold SimplexFundamental.identityRelativeChain
  rw [Category.assoc, ← HomologicalComplex.comp_f, hp, HomologicalComplex.comp_f]
  unfold SimplexFundamental.identityChain
  change simplexι R (SimplexFundamental.identitySingularSimplex (n*d)) ≫
    (simplicialChainMap R (TopCat.toSSet.map (TopCat.ofHom
      (configurationStaircaseSimplex (Equiv.refl (Fin (n*d))))))).f (n*d) ≫ _ = _
  rw [simplexι_chainMap_f_assoc]
  rfl

theorem staircaseSelectedIdentityClass_map (p : ℕ) {d n : ℕ} (hd : 0 < d) :
    HomologicalComplex.homologyMap (staircaseSelectedIdentityMap (ZMod p) hd) (n*d)
      (SimplexFundamental.identityClass (ZMod p) (n*d)) =
    HomologicalComplex.homologyMap (staircaseSelectedLocalization (ZMod p) hd) (n*d)
      (configurationOrdinaryStaircaseClass p d n) := by
  let K := relComplex (ZMod p) (SimplexFundamental.boundaryIncl (n*d))
  let L := relComplex (ZMod p) (associatedBMSourceIncl d n)
  let M := relComplex (ZMod p) (subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
    (staircaseSelectedComplement hd))
  let F := staircaseSelectedIdentityMap (ZMod p) (n := n) hd
  let G := staircaseSelectedLocalization (ZMod p) (n := n) hd
  have hc : SimplexFundamental.identityRelativeCycle (ZMod p) (n*d) ≫
      HomologicalComplex.cyclesMap F (n*d) = configurationOrdinaryStaircaseCycle p d n ≫
        HomologicalComplex.cyclesMap G (n*d) := by
    apply (cancel_mono (M.iCycles (n*d))).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      SimplexFundamental.identityRelativeCycle_i, staircaseSelectedIdentityChain_map,
      Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]
    rw [show configurationOrdinaryStaircaseCycle p d n ≫ L.iCycles (n*d) = _ from
      L.liftCycles_i _ _ _ _]
    exact (configurationStaircaseChain_localization (ZMod p) hd).symm
  have he : SimplexFundamental.identityRelativeCycle (ZMod p) (n*d) ≫ K.homologyπ (n*d) ≫
      HomologicalComplex.homologyMap F (n*d) =
    configurationOrdinaryStaircaseCycle p d n ≫ L.homologyπ (n*d) ≫
      HomologicalComplex.homologyMap G (n*d) := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]
  exact congrArg (fun f => f 1) he

/-- The actual full staircase class is nonzero. The unique local simplex
is detected by a proved coloring cocycle, and its actual local chart
induces an isomorphism. -/
theorem configurationOrdinaryStaircaseClass_ne_zero (p : ℕ) [Nontrivial (ZMod p)]
    {d n : ℕ} (hd : 0 < d) : configurationOrdinaryStaircaseClass p d n ≠ 0 := by
  let P := staircaseBarycenterColoring (n*d)
  let f := HrelMap (ZMod p) (n*d) _ _ (staircaseSelectedSimplexPunctured_square (n := n) hd)
  haveI : IsIso f := isIso_configurationStaircaseSimplex_selected_local (ZMod p) hd (n*d)
  have hn := P.identityClass_image_ne_zero (ZMod p)
  intro hz
  apply hn
  apply (ModuleCat.mono_iff_injective f).mp inferInstance
  rw [map_zero]
  have h := staircaseSelectedIdentityClass_map (n := n) p hd
  rw [hz,map_zero] at h
  simpa only [staircaseSelectedIdentityMap, HomologicalComplex.homologyMap_comp,
    ModuleCat.comp_apply] using h

end NRR.PrimePowerTopology
