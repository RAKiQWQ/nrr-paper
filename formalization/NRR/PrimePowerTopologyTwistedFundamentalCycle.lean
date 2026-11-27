import NRR.PrimePowerTopologyTwistedFundamentalSource
import NRR.PrimePowerTopologyStaircaseRelabel
import NRR.PrimePowerTopologyStaircaseCycle

/-! An actual orbit-representative fundamental cycle. Its signed transfer
is the full staircase cycle, without dividing by the order of the group. -/

noncomputable section
open Set Topology CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

abbrev ConfigurationStaircaseOrbit (d n : ℕ) :=
  freeOrbitIndex (G := ConfigurationGroup n) (S := Equiv.Perm (Fin (n*d)))

instance configurationStaircaseOrbitFintype (d n : ℕ) :
    Fintype (ConfigurationStaircaseOrbit d n) := by
  classical
  exact Fintype.ofSurjective (fun π : Equiv.Perm (Fin (n*d)) =>
    (Quotient.mk'' π : ConfigurationStaircaseOrbit d n)) Quotient.mk''_surjective

/-- The relative generator before taking character coinvariants. -/
def configurationStaircaseRelativeGenerator (R : Type) [CommRing R] {d n : ℕ}
    (π : Equiv.Perm (Fin (n*d))) :
    ModuleCat.of R R ⟶ (relComplex R (associatedBMSourceIncl d n)).X (n*d) :=
  staircaseRelativeGenerator R (X := TopCat.of (OnePoint (Configuration d n)))
    {∞} (configurationCubeCollapse d n) π

theorem configurationStaircaseRelativeGenerator_relabel
    (R : Type) [CommRing R] {d n : ℕ} (g : ConfigurationGroup n)
    (π : Equiv.Perm (Fin (n*d))) :
    configurationStaircaseRelativeGenerator R π ≫
      (associatedBMSourceRelativeAction R g).f (n*d) =
      configurationStaircaseRelativeGenerator R (g • π) := by
  unfold configurationStaircaseRelativeGenerator staircaseRelativeGenerator
  change simplexι R (configurationStaircaseSSetSimplex π) ≫
    (relProj R (associatedBMSourceIncl d n)).f (n*d) ≫
      (associatedBMSourceRelativeAction R g).f (n*d) = _
  rw [← HomologicalComplex.comp_f, associatedBMSourceRelativeAction,
    relProj_comp_relComplexMap, HomologicalComplex.comp_f]
  change simplexι R (configurationStaircaseSSetSimplex π) ≫
    (simplicialChainMap R (TopCat.toSSet.map (associatedBMSourceRelabelMap g))).f (n*d) ≫ _ = _
  rw [simplexι_chainMap_f_assoc]
  congr 2
  apply (TopCat.toSSetObjEquiv _ _).injective
  exact configurationStaircaseSimplex_relabel g π

theorem configurationStaircaseSign_relabel (p : ℕ) {d n : ℕ}
    (g : ConfigurationGroup n) (π : Equiv.Perm (Fin (n*d))) :
    (((associatedAmbientOrientationMod p d n g)⁻¹ : (ZMod p)ˣ) : ZMod p) *
      ((Equiv.Perm.sign π : ℤ) : ZMod p) =
      ((Equiv.Perm.sign (g • π) : ℤ) : ZMod p) := by
  have h : Units.map (Int.castRingHom (ZMod p)).toMonoidHom
      (Equiv.Perm.sign (g • π)) =
      (associatedAmbientOrientationMod p d n g)⁻¹ *
        Units.map (Int.castRingHom (ZMod p)).toMonoidHom (Equiv.Perm.sign π) := by
    change Units.map _ (Equiv.Perm.sign (π * (configurationAxisRelabel d g)⁻¹)) = _
    rw [map_mul, map_inv, map_mul, map_inv, configurationAxisRelabel_orientation]
    exact mul_comm _ _
  exact (congrArg Units.val h).symm

/-- One genuinely represented simplex per free label orbit, with its
ambient orientation coefficient. -/
def configurationTwistedFundamentalChain (p : ℕ) (d n : ℕ) :
    ModuleCat.of (ZMod p) (ZMod p) ⟶
      (associatedBMTwistedSource (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)).X (n*d) :=
  ∑ i : ConfigurationStaircaseOrbit d n,
    ((Equiv.Perm.sign i.out : ℤ) : ZMod p) •
      configurationAmbientTwistedStaircaseGenerator p i.out

theorem configurationStaircaseGenerator_transfer (p : ℕ) {d n : ℕ}
    (π : Equiv.Perm (Fin (n*d))) :
    configurationAmbientTwistedStaircaseGenerator p π ≫
      (twistedFundamentalSourceTransfer (ZMod p)
        (associatedAmbientOrientationMod p d n)).f (n*d) =
      ∑ g : ConfigurationGroup n,
        (((associatedAmbientOrientationMod p d n g)⁻¹ : (ZMod p)ˣ) : ZMod p) •
          configurationStaircaseRelativeGenerator (ZMod p) (g • π) := by
  change configurationStaircaseRelativeGenerator (ZMod p) π ≫
    (twistedChainProj (ZMod p) (associatedAmbientOrientationMod p d n) _ _).f (n*d) ≫
      (twistedChainTransferDesc (ZMod p) _ _ _
        (twistedFundamentalSourceAction_mul (ZMod p))).f (n*d) = _
  rw [← HomologicalComplex.comp_f, twistedChainProj_transferDesc]
  unfold twistedChainTransfer
  have hs := map_sum (HomologicalComplex.Hom.fAddMonoidHom
    (C₁ := relComplex (ZMod p) (associatedBMSourceIncl d n))
    (C₂ := relComplex (ZMod p) (associatedBMSourceIncl d n)) (n*d))
    (fun g : ConfigurationGroup n =>
      (((associatedAmbientOrientationMod p d n g)⁻¹ : (ZMod p)ˣ) : ZMod p) •
        associatedBMSourceRelativeAction (ZMod p) g) Finset.univ
  change (∑ g : ConfigurationGroup n,
    (((associatedAmbientOrientationMod p d n g)⁻¹ : (ZMod p)ˣ) : ZMod p) •
      associatedBMSourceRelativeAction (ZMod p) g).f (n*d) = _ at hs
  rw [hs, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro g _
  change configurationStaircaseRelativeGenerator (ZMod p) π ≫
    (((((associatedAmbientOrientationMod p d n) g)⁻¹ : (ZMod p)ˣ) : ZMod p) •
      (associatedBMSourceRelativeAction (ZMod p) g).f (n*d)) = _
  rw [Linear.comp_smul, configurationStaircaseRelativeGenerator_relabel]

/-- Expanding signed transfer yields each actual staircase chamber exactly
once. The statement holds in characteristic dividing the group order. -/
theorem configurationTwistedFundamentalChain_transfer (p : ℕ) {d n : ℕ} (hd : 0 < d) :
    configurationTwistedFundamentalChain p d n ≫
      (twistedFundamentalSourceTransfer (ZMod p)
        (associatedAmbientOrientationMod p d n)).f (n*d) =
      staircaseRelativeChain (ZMod p) (X := TopCat.of (OnePoint (Configuration d n)))
        {∞} (configurationCubeCollapse d n) := by
  classical
  unfold configurationTwistedFundamentalChain
  rw [Preadditive.sum_comp]
  simp_rw [Linear.smul_comp, configurationStaircaseGenerator_transfer, Finset.smul_sum,
    smul_smul]
  simp_rw [mul_comm (((Equiv.Perm.sign _ : ℤ) : ZMod p)), configurationStaircaseSign_relabel]
  let e := freeOrbitEquiv (configurationStaircaseChamber_action_free (n := n) hd)
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  change (∑ gi : ConfigurationGroup n × ConfigurationStaircaseOrbit d n,
    ((Equiv.Perm.sign (e gi) : ℤ) : ZMod p) •
      configurationStaircaseRelativeGenerator (ZMod p) (e gi)) = _
  calc
    _ = ∑ π : Equiv.Perm (Fin (n*d)), ((Equiv.Perm.sign π : ℤ) : ZMod p) •
        configurationStaircaseRelativeGenerator (ZMod p) π :=
      e.sum_comp (fun π => ((Equiv.Perm.sign π : ℤ) : ZMod p) •
        configurationStaircaseRelativeGenerator (ZMod p) π)
    _ = _ := by
      unfold staircaseRelativeChain configurationStaircaseRelativeGenerator
      simp only [Int.cast_smul_eq_zsmul]

theorem configurationCubeCollapse_cubeBoundary {d n : ℕ}
    (x : ConfigurationCube d n) (hx : x ∈ staircaseCubeBoundary (n*d)) :
    configurationCubeCollapse d n x = ∞ := by
  apply configurationCubeCollapse_boundary
  intro hi
  obtain ⟨a, ha | ha⟩ := hx
  · have h := (hi a).1
    rw [ha] at h
    exact lt_irrefl _ h
  · have h := (hi a).2
    rw [ha] at h
    exact lt_irrefl _ h

theorem staircaseRelativeChain_cycle_all (R : Type) [CommRing R]
    {X : TopCat.{0}} (A : Set X) {m : ℕ} (c : C(StaircaseCube m,X))
    (hc : ∀ x ∈ staircaseCubeBoundary m, c x ∈ A) :
    staircaseRelativeChain R A c ≫
      (relComplex R (subIncl (Y := X) A)).d m (m-1) = 0 := by
  cases m with
  | zero => simp
  | succ q => exact staircaseRelativeChain_cycle R A c hc

/-- The orbit-representative sum is an actual cycle, as detected by the
injective chain transfer in the boundary degree. -/
theorem configurationTwistedFundamentalChain_cycle (p : ℕ) {d n : ℕ} (hd : 0 < d) :
    configurationTwistedFundamentalChain p d n ≫
      (associatedBMTwistedSource (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)).d (n*d) (n*d-1) = 0 := by
  let t := twistedFundamentalSourceTransfer (ZMod p) (d := d) (associatedAmbientOrientationMod p d n)
  haveI : Mono (t.f (n*d-1)) := (ModuleCat.mono_iff_injective _).mpr
    (twistedFundamentalSourceTransfer_injective (ZMod p) _ _)
  apply (cancel_mono (t.f (n*d-1))).mp
  rw [zero_comp, Category.assoc, ← t.comm, ← Category.assoc]
  rw [show configurationTwistedFundamentalChain p d n ≫ t.f (n*d) = _ from
    configurationTwistedFundamentalChain_transfer p hd]
  exact staircaseRelativeChain_cycle_all (ZMod p)
    (X := TopCat.of (OnePoint (Configuration d n))) {∞} (configurationCubeCollapse d n)
    (fun x hx => Set.mem_singleton_iff.mpr (configurationCubeCollapse_cubeBoundary x hx))

/-- The genuine twisted fundamental cycle, before passing to homology. -/
def configurationTwistedFundamentalCycle (p d n : ℕ) (hd : 0 < d) :
    ModuleCat.of (ZMod p) (ZMod p) ⟶
      (associatedBMTwistedSource (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)).cycles (n*d) :=
  (associatedBMTwistedSource (ZMod p) (d := d) (associatedAmbientOrientationMod p d n)).liftCycles
    (configurationTwistedFundamentalChain p d n) (n*d-1)
    (by cases n*d <;> simp) (configurationTwistedFundamentalChain_cycle p hd)

@[reassoc (attr := simp)] theorem configurationTwistedFundamentalCycle_i
    (p d n : ℕ) (hd : 0 < d) :
    configurationTwistedFundamentalCycle p d n hd ≫
      (associatedBMTwistedSource (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)).iCycles (n*d) =
      configurationTwistedFundamentalChain p d n :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The class of an actual orbit-representative cycle. This is a different
construction from projecting the ordered fundamental class. -/
def configurationGenuineTwistedFundamentalClass (p d n : ℕ) (hd : 0 < d) :
    (associatedBMTwistedSource (ZMod p) (d := d)
      (associatedAmbientOrientationMod p d n)).homology (n*d) :=
  (configurationTwistedFundamentalCycle p d n hd ≫
    (associatedBMTwistedSource (ZMod p) (d := d)
      (associatedAmbientOrientationMod p d n)).homologyπ (n*d)) 1

/-- The ordinary staircase cycle in the infinity-relative configuration
complex. -/
def configurationOrdinaryStaircaseCycle (p d n : ℕ) :
    ModuleCat.of (ZMod p) (ZMod p) ⟶
      (relComplex (ZMod p) (associatedBMSourceIncl d n)).cycles (n*d) :=
  (relComplex (ZMod p) (associatedBMSourceIncl d n)).liftCycles
    (staircaseRelativeChain (ZMod p) (X := TopCat.of (OnePoint (Configuration d n)))
      {∞} (configurationCubeCollapse d n)) (n*d-1) (by cases n*d <;> simp)
    (staircaseRelativeChain_cycle_all (ZMod p)
      (X := TopCat.of (OnePoint (Configuration d n))) {∞} (configurationCubeCollapse d n)
      (fun x hx => Set.mem_singleton_iff.mpr (configurationCubeCollapse_cubeBoundary x hx)))

def configurationOrdinaryStaircaseClass (p d n : ℕ) :
    Hrel (ZMod p) (n*d) (associatedBMSourceIncl d n) :=
  (configurationOrdinaryStaircaseCycle p d n ≫
    (relComplex (ZMod p) (associatedBMSourceIncl d n)).homologyπ (n*d)) 1

/-- Transfer of the genuine twisted class is the class of the full actual
staircase cycle. -/
theorem configurationGenuineTwistedFundamentalClass_transfer (p d n : ℕ) (hd : 0 < d) :
    HomologicalComplex.homologyMap
      (twistedFundamentalSourceTransfer (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)) (n*d)
      (configurationGenuineTwistedFundamentalClass p d n hd) =
      configurationOrdinaryStaircaseClass p d n := by
  let K := associatedBMTwistedSource (ZMod p) (d := d) (associatedAmbientOrientationMod p d n)
  let L := relComplex (ZMod p) (associatedBMSourceIncl d n)
  let t := twistedFundamentalSourceTransfer (ZMod p) (d := d) (associatedAmbientOrientationMod p d n)
  have hc : configurationTwistedFundamentalCycle p d n hd ≫
      HomologicalComplex.cyclesMap t (n*d) = configurationOrdinaryStaircaseCycle p d n := by
    apply (cancel_mono (L.iCycles (n*d))).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      configurationTwistedFundamentalCycle_i, configurationTwistedFundamentalChain_transfer p hd]
    exact (L.liftCycles_i _ _ _ _).symm
  have he : configurationTwistedFundamentalCycle p d n hd ≫ K.homologyπ (n*d) ≫
      HomologicalComplex.homologyMap t (n*d) =
      configurationOrdinaryStaircaseCycle p d n ≫ L.homologyπ (n*d) := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]
  exact congrArg (fun f => f 1) he

end NRR.PrimePowerTopology
