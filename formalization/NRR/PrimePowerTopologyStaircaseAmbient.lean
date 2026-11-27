import NRR.PrimePowerTopologyTwistedFundamentalCycle
import NRR.PrimePowerTopologyMinimalGeneration

/-! The full staircase configuration cycle is the image of an actual
ambient compactification cycle. -/

noncomputable section
open Set Topology CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

def configurationAmbientCubeCollapse (d n : ℕ) :
    C(ConfigurationCube d n,OnePoint (Fin n → Space d)) :=
  ⟨fun x => (configurationCubeInteriorEuclidean d n).onePointCongr
      (openCollapse (configurationCubeInterior d n) x),
    (configurationCubeInteriorEuclidean d n).onePointCongr.continuous.comp
      (continuous_openCollapse _ (isOpen_configurationCubeInterior d n))⟩

theorem configurationAmbientCubeCollapse_boundary {d n : ℕ}
    (x : ConfigurationCube d n) (hx : x ∈ staircaseCubeBoundary (n*d)) :
    configurationAmbientCubeCollapse d n x = ∞ := by
  have hi : x ∉ configurationCubeInterior d n := by
    intro hi
    obtain ⟨a, ha | ha⟩ := hx
    · have h := (hi a).1
      rw [ha] at h
      exact lt_irrefl _ h
    · have h := (hi a).2
      rw [ha] at h
      exact lt_irrefl _ h
  simp [configurationAmbientCubeCollapse, openCollapse, hi]

abbrev configurationAmbientInfinityIncl (d n : ℕ) :=
  subIncl (Y := TopCat.of (OnePoint (Fin n → Space d))) {∞}

def configurationAmbientInfinityMap (d n : ℕ) :
    TopCat.of ({∞} : Set (OnePoint (Fin n → Space d))) ⟶
      TopCat.of ({∞} : Set (OnePoint (Configuration d n))) :=
  TopCat.ofHom ⟨fun _ => ⟨∞,rfl⟩, continuous_const⟩

theorem configurationAmbientCollapse_square (d n : ℕ) :
    configurationAmbientInfinityIncl d n ≫ TopCat.ofHom (configurationOnePointCollapse d n) =
      configurationAmbientInfinityMap d n ≫ associatedBMSourceIncl d n := by
  ext z
  have hz : z.val = ∞ := z.property
  change configurationOnePointCollapse d n z.val = ∞
  rw [hz, configurationOnePointCollapse_infty]

def configurationAmbientRelativeCollapse (R : Type) [CommRing R] (d n : ℕ) :
    relComplex R (configurationAmbientInfinityIncl d n) ⟶
      relComplex R (associatedBMSourceIncl d n) :=
  relComplexMap R _ _ (configurationAmbientCollapse_square d n)

theorem configurationAmbientStaircaseGenerator_collapse (R : Type) [CommRing R]
    {d n : ℕ} (π : Equiv.Perm (Fin (n*d))) :
    staircaseRelativeGenerator R (X := TopCat.of (OnePoint (Fin n → Space d)))
      {∞} (configurationAmbientCubeCollapse d n) π ≫
      (configurationAmbientRelativeCollapse R d n).f (n*d) =
      configurationStaircaseRelativeGenerator R π := by
  unfold staircaseRelativeGenerator
  change simplexι R _ ≫ (relProj R (configurationAmbientInfinityIncl d n)).f (n*d) ≫
    (configurationAmbientRelativeCollapse R d n).f (n*d) = _
  rw [← HomologicalComplex.comp_f, configurationAmbientRelativeCollapse,
    relProj_comp_relComplexMap, HomologicalComplex.comp_f]
  change simplexι R _ ≫ (simplicialChainMap R
    (TopCat.toSSet.map (TopCat.ofHom (configurationOnePointCollapse d n)))).f (n*d) ≫ _ = _
  rw [simplexι_chainMap_f_assoc]
  rfl

theorem configurationAmbientStaircaseChain_collapse (R : Type) [CommRing R]
    (d n : ℕ) :
    staircaseRelativeChain R (X := TopCat.of (OnePoint (Fin n → Space d)))
      {∞} (configurationAmbientCubeCollapse d n) ≫
      (configurationAmbientRelativeCollapse R d n).f (n*d) =
    staircaseRelativeChain R (X := TopCat.of (OnePoint (Configuration d n)))
      {∞} (configurationCubeCollapse d n) := by
  unfold staircaseRelativeChain
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro π _
  rw [Preadditive.zsmul_comp]
  exact congrArg (fun f => (Equiv.Perm.sign π : ℤ) • f)
    (configurationAmbientStaircaseGenerator_collapse R π)

def configurationAmbientStaircaseCycle (p d n : ℕ) :
    ModuleCat.of (ZMod p) (ZMod p) ⟶
      (relComplex (ZMod p) (configurationAmbientInfinityIncl d n)).cycles (n*d) :=
  (relComplex (ZMod p) (configurationAmbientInfinityIncl d n)).liftCycles
    (staircaseRelativeChain (ZMod p) (X := TopCat.of (OnePoint (Fin n → Space d)))
      {∞} (configurationAmbientCubeCollapse d n)) (n*d-1) (by cases n*d <;> simp)
    (staircaseRelativeChain_cycle_all (ZMod p)
      (X := TopCat.of (OnePoint (Fin n → Space d))) {∞} (configurationAmbientCubeCollapse d n)
      (fun x hx => Set.mem_singleton_iff.mpr (configurationAmbientCubeCollapse_boundary x hx)))

def configurationAmbientStaircaseClass (p d n : ℕ) :
    Hrel (ZMod p) (n*d) (configurationAmbientInfinityIncl d n) :=
  (configurationAmbientStaircaseCycle p d n ≫
    (relComplex (ZMod p) (configurationAmbientInfinityIncl d n)).homologyπ (n*d)) 1

theorem configurationAmbientStaircaseClass_collapse (p d n : ℕ) :
    HomologicalComplex.homologyMap (configurationAmbientRelativeCollapse (ZMod p) d n) (n*d)
      (configurationAmbientStaircaseClass p d n) = configurationOrdinaryStaircaseClass p d n := by
  let K := relComplex (ZMod p) (configurationAmbientInfinityIncl d n)
  let L := relComplex (ZMod p) (associatedBMSourceIncl d n)
  let f := configurationAmbientRelativeCollapse (ZMod p) d n
  have hc : configurationAmbientStaircaseCycle p d n ≫
      HomologicalComplex.cyclesMap f (n*d) = configurationOrdinaryStaircaseCycle p d n := by
    apply (cancel_mono (L.iCycles (n*d))).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]
    rw [show configurationAmbientStaircaseCycle p d n ≫ K.iCycles (n*d) = _ from
      K.liftCycles_i _ _ _ _, configurationAmbientStaircaseChain_collapse]
    exact (L.liftCycles_i _ _ _ _).symm
  have he : configurationAmbientStaircaseCycle p d n ≫ K.homologyπ (n*d) ≫
      HomologicalComplex.homologyMap f (n*d) =
      configurationOrdinaryStaircaseCycle p d n ≫ L.homologyπ (n*d) := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]
  exact congrArg (fun f => f 1) he

/-- The transferred class is in the actual ambient image in every positive
degree. Its ambient preimage is nonzero whenever the ordinary class is. -/
theorem configurationOrdinaryStaircaseClass_ambient_image (p d n : ℕ) (hpos : 0 < n*d) :
    ∃ a : Habs (ZMod p) (n*d) (TopCat.of (OnePoint (Fin n → Space d))),
      relJ (ZMod p) (n*d) (associatedBMSourceIncl d n)
        (HabsMap (ZMod p) (n*d) (TopCat.ofHom (configurationOnePointCollapse d n)) a) =
        configurationOrdinaryStaircaseClass p d n := by
  obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  haveI : IsIso (relJ (ZMod p) (n*d) (configurationAmbientInfinityIncl d n)) := by
    rw [hq]
    exact (relativeOfContractiblePositiveIso (ZMod p) q _).isIso_hom
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective
    (relJ (ZMod p) (n*d) (configurationAmbientInfinityIncl d n))).mp inferInstance
    (configurationAmbientStaircaseClass p d n)
  refine ⟨a,?_⟩
  have he := relJ_naturality (ZMod p) (n*d) _ _ (configurationAmbientCollapse_square d n)
  have hh := congrArg (fun f => f a) he
  change HomologicalComplex.homologyMap (configurationAmbientRelativeCollapse (ZMod p) d n) (n*d)
    (relJ (ZMod p) (n*d) (configurationAmbientInfinityIncl d n) a) = _ at hh
  rw [ha,configurationAmbientStaircaseClass_collapse] at hh
  exact hh.symm

theorem configurationOrdinaryStaircaseClass_ambient_image_nonzero
    (p d n : ℕ) (hpos : 0 < n*d)
    (hc : configurationOrdinaryStaircaseClass p d n ≠ 0) :
    ∃ a : Habs (ZMod p) (n*d) (TopCat.of (OnePoint (Fin n → Space d))), a ≠ 0 ∧
      relJ (ZMod p) (n*d) (associatedBMSourceIncl d n)
        (HabsMap (ZMod p) (n*d) (TopCat.ofHom (configurationOnePointCollapse d n)) a) =
        configurationOrdinaryStaircaseClass p d n := by
  obtain ⟨a,ha⟩ := configurationOrdinaryStaircaseClass_ambient_image p d n hpos
  refine ⟨a,?_,ha⟩
  intro hz
  apply hc
  rw [← ha,hz,map_zero,map_zero]

end NRR.PrimePowerTopology
