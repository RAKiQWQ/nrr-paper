import NRR.PrimePowerTopologyAssociatedBMDesuspension
import NRR.PrimePowerTopologyEulerThomAssembly
import NRR.PrimePowerTopologyTwistedFundamentalSource
import NRR.PrimePowerTopologyPrimePowerPersistence

/-! Nontriviality of the genuine orientation-twisted Euler target.
Geometric desuspension, the fiber determinant computation, and the actual
bottom chain projection turn the surviving configuration class into a
character-covariant ordinary detector. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ}

private theorem targetNonzero_homologyMap_smul
    {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (r : R) (q : ℕ) :
    HomologicalComplex.homologyMap (r • f) q = r • HomologicalComplex.homologyMap f q := by
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map
      (r • f) = r • (HomologicalComplex.shortComplexFunctor (ModuleCat R)
        (ComplexShape.down ℕ) q).map f by rfl,
    ShortComplex.homologyMap_smul]

def configurationAbsoluteTwistedProjection (χ : ConfigurationGroup n →* Rˣ) (q : ℕ) :
    Habs R q (TopCat.of (OnePoint (Configuration (d+1) n))) ⟶
      (associatedBMTwistedSource R (d := d+1) χ).homology q :=
  relJ R q (associatedBMSourceIncl (d+1) n) ≫ HomologicalComplex.homologyMap
    (twistedChainProj R χ _ (associatedBMSourceRelativeAction R)) q

@[reassoc]
theorem configurationAbsoluteTwistedProjection_covariance
    (χ : ConfigurationGroup n →* Rˣ) (q : ℕ) (g : ConfigurationGroup n) :
    HabsMap R q (associatedBMSourceRelabelMap g) ≫
        configurationAbsoluteTwistedProjection R (d := d) χ q =
      (χ g : R) • configurationAbsoluteTwistedProjection R χ q := by
  unfold configurationAbsoluteTwistedProjection
  rw [← Category.assoc,← relJ_naturality R q _ _ (associatedBMSourceIncl_equivariant g),
    Category.assoc]
  change relJ R q _ ≫ (HomologicalComplex.homologyMap (associatedBMSourceRelativeAction R g) q ≫
    HomologicalComplex.homologyMap (twistedChainProj R χ _ (associatedBMSourceRelativeAction R)) q) = _
  rw [← HomologicalComplex.homologyMap_comp,chainAction_proj,targetNonzero_homologyMap_smul,
    Linear.comp_smul]

theorem isZero_configurationBMSource_below (hn : 2 ≤ n) (q : ℕ) (hq : q < d+n) :
    IsZero (Hrel R q (associatedBMSourceIncl (d+1) n)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  letI : NeZero m := ⟨by omega⟩
  let W := OnePoint (Configuration (d+1) (m+1) × Space 0)
  let E := OnePoint (Configuration (d+1) (m+1))
  let ambient := TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of W)
    (spaceProductZeroHomeomorph (Configuration (d+1) (m+1))).symm.onePointCongr
  let source := TopCat.of ({∞} : Set E)
  let point := TopCat.isoOfHomeo (X := source) (Y := TopCat.of Unit)
    (Homeomorph.homeomorphOfUnique _ _)
  let i := associatedBMSourceIncl (d+1) (m+1)
  let j := homologyPointIncl (X := TopCat.of W) ∞
  have w : i ≫ ambient.hom = point.hom ≫ j := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    rintro ⟨z,hz⟩
    have h : z = ∞ := hz
    subst z
    rfl
  letI := isIso_HrelMap_of_isIso R q i j w
  exact IsZero.of_iso (isZero_configurationProductBM_below R d m 0 q (by omega))
    (asIso (HrelMap R q i j w))

/-- The source projection is actually surjective in the bottom degree,
including in characteristic dividing the permutation-group order. -/
theorem epi_configurationAbsoluteTwistedProjection
    (χ : ConfigurationGroup n →* Rˣ) (hn : 2 ≤ n) :
    Epi (configurationAbsoluteTwistedProjection R (d := d) χ (d+n)) := by
  let q := d+n
  letI : IsIso (relJ R q (associatedBMSourceIncl (d+1) n)) :=
    by
      have hi := (positiveSingletonRelativeIso R q (by dsimp [q]; omega)
        (X := TopCat.of (OnePoint (Configuration (d+1) n))) ∞).isIso_hom
      rw [positiveSingletonRelativeIso_hom] at hi
      exact hi
  letI : Epi (HomologicalComplex.homologyMap
      (twistedChainProj R χ _ (associatedBMSourceRelativeAction R (d := d+1))) q) :=
    epi_twistedProjection_of_free_orbits χ (associatedBMSourceRelativeAction R)
      (twistedFundamentalSourceAction_mul R) (twistedFundamentalSourceOrbitBasis R)
      (twistedFundamentalSourceOrbitBasis_relabel R) q
      (fun i hi => isZero_configurationBMSource_below R hn i hi)
  unfold configurationAbsoluteTwistedProjection
  infer_instance

/-- A nonzero bottom twisted configuration group gives a nonzero genuine
Euler target, with exactly the fiber determinant twist. -/
theorem nontrivial_associatedBMTwistedTarget_of_bottomSource [NeZero n]
    (η χ : ConfigurationGroup n →* Rˣ) (hn : 2 ≤ n)
    (hχ : ∀ g, (χ g : R) = (((Equiv.Perm.sign g : ℤ)^d : ℤ) : R) * (η g : R))
    [Nontrivial ((associatedBMTwistedSource R (d := d+1) η).homology (d+n))] :
    Nontrivial ((associatedBMTwistedTarget R (d := d+1) χ).homology ((d+1)*n)) := by
  let Q := (d+1)*n
  let q := d+n
  let E := associatedBMBottomAbsoluteIso R d n hn
  let A := positiveSingletonRelativeIso R Q
    (by dsimp [Q]; exact Nat.mul_pos (Nat.succ_pos d) (NeZero.pos n))
    (X := TopCat.of (OnePoint (AssociatedCover (d+1) n))) ∞
  let P := configurationAbsoluteTwistedProjection R (d := d) η q
  let u := A.inv ≫ E.hom ≫ P
  have habs (g : ConfigurationGroup n) :
      HabsMap R Q (associatedBMCoverRelabelMap g) ≫ E.hom ≫ P =
        (χ g : R) • (E.hom ≫ P) := by
    dsimp only [Q,q,E,P]
    rw [associatedBMCoverRelabelMap_bottom R hn g,
      ← Int.cast_smul_eq_zsmul R ((Equiv.Perm.sign g : ℤ)^d),Linear.smul_comp,
      ← Category.assoc,← associatedBMBottomAbsoluteIso_base_naturality,
      Category.assoc,configurationAbsoluteTwistedProjection_covariance,
      Linear.comp_smul,smul_smul,← hχ]
  have hrel (g : ConfigurationGroup n) :
      A.hom ≫ HomologicalComplex.homologyMap
        (associatedBMCoverInfinityRelativeAction R g) Q =
        HabsMap R Q (associatedBMCoverRelabelMap g) ≫ A.hom := by
    simp only [A,positiveSingletonRelativeIso_hom]
    change relJ R Q _ ≫ HrelMap R Q _ _ (associatedBMCoverInfinityIncl_equivariant g) = _
    exact relJ_naturality R Q _ _ (associatedBMCoverInfinityIncl_equivariant g)
  have hu (g : ConfigurationGroup n) :
      HomologicalComplex.homologyMap (associatedBMCoverInfinityRelativeAction R g) Q ≫ u =
        (χ g : R) • u := by
    apply (cancel_epi A.hom).mp
    dsimp [u]
    rw [← Category.assoc A.hom, hrel]
    simp only [Category.assoc,Iso.hom_inv_id_assoc,Linear.comp_smul]
    exact habs g
  letI : Epi P := epi_configurationAbsoluteTwistedProjection R η hn
  obtain ⟨c,hc⟩ := exists_ne (0 : (associatedBMTwistedSource R (d := d+1) η).homology q)
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective P).mp inferInstance c
  let z := A.hom (E.inv x)
  apply nontrivial_associatedBMTwistedTarget_of_covariant_detector R χ hn u hu z
  change P (E.hom (A.inv (A.hom (E.inv x)))) ≠ 0
  have hA := congrArg (fun f => f (E.inv x)) A.hom_inv_id
  have hE := congrArg (fun f => f x) E.inv_hom_id
  simp only [ConcreteCategory.comp_apply,ModuleCat.id_apply] at hA hE
  rw [hA,hE,hx]
  exact hc

/-- The prime-power configuration class gives a nontrivial actual Euler
target in every ambient dimension at least two, including odd primes. -/
theorem nontrivial_associatedBMTwistedTarget_primePower_succ
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hn : 2 ≤ n) (hpow : n = p^a) :
    Nontrivial ((associatedBMTwistedTarget (ZMod p) (d := d+2)
      (associatedAmbientOrientationMod p (d+2) n)).homology ((d+2)*n)) := by
  let η := permutationOrientationMod p n
  let i₀ : Fin n := ⟨0,NeZero.pos n⟩
  letI : Nontrivial ((associatedBMTwistedSource (ZMod p) (d := d+2) η).homology ((d+1)+n)) := by
    apply nontrivial_of_ne _ 0
    exact bm_twistedMinimalClass_primePower_ne_zero (d := d) hp hn hpow i₀
  apply nontrivial_associatedBMTwistedTarget_of_bottomSource (ZMod p)
    (d := d+1) η (associatedAmbientOrientationMod p (d+2) n) hn
  intro g
  have hs : (((Equiv.Perm.sign g : ℤ) : ZMod p)) = (η g : ZMod p) := rfl
  simp only [associatedAmbientOrientationMod,MonoidHom.pow_apply,Units.val_pow_eq_pow_val,
    Int.cast_pow,hs]
  exact pow_succ (η g : ZMod p) (d+1)

/-- The orientation-twisted Euler target is nonzero for every positive
horizontal dimension and every prime-power number of labels. -/
theorem nontrivial_associatedBMTwistedTarget_primePower
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hd : 0 < d)
    (hn : 2 ≤ n) (hpow : n = p^a) :
    Nontrivial ((associatedBMTwistedTarget (ZMod p) (d := d+1)
      (associatedAmbientOrientationMod p (d+1) n)).homology ((d+1)*n)) := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  exact nontrivial_associatedBMTwistedTarget_primePower_succ hp hn hpow

end NRR.PrimePowerTopology
