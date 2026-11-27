import NRR.PrimePowerTopologyEulerThomInclusion
import NRR.PrimePowerTopologyEulerThomDetection

/-! Explicit scalar coordinates for the genuine Euler/Thom factorization.
The normal group has rank one, and its closed inclusion generates the
actual Euler target. Over a field, a nonzero target makes this inclusion
an isomorphism. The remaining source calculation is precisely the scalar
of the collapse of a genuine twisted cycle. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]

/-- The normal rank-one comparison in the actual ambient degree. -/
def verticalNormalAmbientDegreeIso (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n) :
    ModuleCat.of R R ≅ (verticalNormalPointTwisted R (d := d) χ).homology ((d+1)*n) := by
  simpa only [Nat.add_mul, Nat.one_mul] using verticalNormalTopIso R χ hd hn i₀

/-- The chosen generator belongs to the genuine twisted normal complex. -/
def verticalNormalGenerator (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n) :
    (verticalNormalPointTwisted R (d := d) χ).homology ((d+1)*n) :=
  (verticalNormalAmbientDegreeIso R χ hd hn i₀).hom 1

theorem verticalNormalGenerator_ne_zero [Nontrivial R]
    (χ : ConfigurationGroup n →* Rˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n) :
    verticalNormalGenerator R χ hd hn i₀ ≠ 0 := by
  intro hz
  have h := congrArg (verticalNormalAmbientDegreeIso R χ hd hn i₀).inv hz
  simp [verticalNormalGenerator] at h

theorem verticalNormal_eq_coordinate_smul (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    (z : (verticalNormalPointTwisted R (d := d) χ).homology ((d+1)*n)) :
    z = (verticalNormalAmbientDegreeIso R χ hd hn i₀).inv z •
      verticalNormalGenerator R χ hd hn i₀ := by
  let e := verticalNormalAmbientDegreeIso R χ hd hn i₀
  change z = e.inv z • e.hom 1
  rw [← map_smul]
  simpa only [smul_eq_mul, mul_one] using (e.toLinearEquiv.apply_symm_apply z).symm

/-- The Euler target generator is the image of the actual closed normal
inclusion, rather than a projected ordered fundamental class. -/
def verticalEulerTargetGenerator (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n) :
    (associatedBMTwistedTarget R (d := d+1) χ).homology ((d+1)*n) :=
  HomologicalComplex.homologyMap (verticalNormalTwistedInclude R χ) ((d+1)*n)
    (verticalNormalGenerator R χ hd hn i₀)

/-- The concrete normal image spans the whole twisted Euler target,
over every commutative ring. -/
theorem verticalEulerTargetGenerator_spans (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    (z : (associatedBMTwistedTarget R (d := d+1) χ).homology ((d+1)*n)) :
    ∃ a : R, z = a • verticalEulerTargetGenerator R χ hd hn i₀ := by
  let f := HomologicalComplex.homologyMap (verticalNormalTwistedInclude R (d := d) χ) ((d+1)*n)
  letI : Epi f := epi_verticalNormalTwistedInclude R χ hn
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance z
  refine ⟨(verticalNormalAmbientDegreeIso R χ hd hn i₀).inv x, ?_⟩
  conv_lhs => rw [verticalNormal_eq_coordinate_smul R χ hd hn i₀ x]
  exact f.hom.map_smul _ _

/-- A scalar-valued homomorphism recording the actual normal collapse. -/
def verticalEulerCoefficient (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n) :
    (associatedBMTwistedSource R (d := d+1) χ).homology ((d+1)*n) ⟶ ModuleCat.of R R :=
  HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R χ) ((d+1)*n) ≫
    (verticalNormalAmbientDegreeIso R χ hd hn i₀).inv

/-- The genuine Euler image is its collapse coefficient times the
geometrically defined normal-image generator. -/
theorem associatedBMTwistedEulerMap_apply_eq_coefficient_smul
    (χ : ConfigurationGroup n →* Rˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    (c : (associatedBMTwistedSource R (d := d+1) χ).homology ((d+1)*n)) :
    associatedBMTwistedEulerMap R χ ((d+1)*n) c =
      verticalEulerCoefficient R χ hd hn i₀ c • verticalEulerTargetGenerator R χ hd hn i₀ := by
  rw [associatedBMTwistedEulerMap_eq_pointNormal, ModuleCat.comp_apply]
  conv_lhs => rw [verticalNormal_eq_coordinate_smul R χ hd hn i₀
    (HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R χ) ((d+1)*n) c)]
  exact (HomologicalComplex.homologyMap (verticalNormalTwistedInclude R χ) ((d+1)*n)).hom.map_smul _ _

omit [NeZero n] in
/-- A covariant ordinary detector on the genuine total cover certifies
nontriviality of the twisted Euler target. This is the exact interface for
dimension descent followed by the surviving sign-twisted Fuks class. -/
theorem nontrivial_associatedBMTwistedTarget_of_covariant_detector
    (χ : ConfigurationGroup n →* Rˣ) (hn : 2 ≤ n)
    {M : ModuleCat R} (u : Hrel R ((d+1)*n) (associatedBMCoverInfinityIncl (d+1) n) ⟶ M)
    (hu : ∀ g, HomologicalComplex.homologyMap
      (associatedBMCoverInfinityRelativeAction R g) ((d+1)*n) ≫ u = (χ g : R) • u)
    (z : Hrel R ((d+1)*n) (associatedBMCoverInfinityIncl (d+1) n)) (hz : u z ≠ 0) :
    Nontrivial ((associatedBMTwistedTarget R (d := d+1) χ).homology ((d+1)*n)) := by
  obtain ⟨ψ, hψ, _⟩ := existsUnique_associatedBMTargetDetector R χ (Nat.succ_pos d) hn u hu
  let f := HomologicalComplex.homologyMap (associatedBMCoverToTarget R (d := d+1) (n := n)) ((d+1)*n) ≫
    HomologicalComplex.homologyMap (twistedChainProj R χ (relComplex R
      (associatedBMTargetIncl (d+1) n)) (associatedBMTargetRelativeAction R)) ((d+1)*n)
  have hw : f ≫ ψ = u := by simpa only [f, Category.assoc] using hψ
  apply nontrivial_of_ne (f z) 0
  intro he
  apply hz
  have hzero : (f ≫ ψ) z = 0 := (congrArg (fun x => ψ x) he).trans (map_zero ψ.hom)
  exact (congrArg (fun m => m z) hw).symm.trans hzero

section Field
variable (F : Type) [Field F]

/-- Nontriviality of the Euler target already detects its concrete generator. -/
theorem verticalEulerTargetGenerator_ne_zero
    (χ : ConfigurationGroup n →* Fˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    [Nontrivial ((associatedBMTwistedTarget F (d := d+1) χ).homology ((d+1)*n))] :
    verticalEulerTargetGenerator F χ hd hn i₀ ≠ 0 := by
  intro hz
  obtain ⟨z, hzne⟩ := exists_ne (0 : (associatedBMTwistedTarget F (d := d+1) χ).homology ((d+1)*n))
  obtain ⟨a, ha⟩ := verticalEulerTargetGenerator_spans F χ hd hn i₀ z
  exact hzne (by rw [ha, hz, smul_zero])

/-- Over a field the genuine closed normal inclusion is an isomorphism
as soon as its Euler target is nontrivial. -/
theorem isIso_verticalNormalTwistedInclude_of_nontrivial
    (χ : ConfigurationGroup n →* Fˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    [Nontrivial ((associatedBMTwistedTarget F (d := d+1) χ).homology ((d+1)*n))] :
    IsIso (HomologicalComplex.homologyMap (verticalNormalTwistedInclude F (d := d) χ) ((d+1)*n)) := by
  let f := HomologicalComplex.homologyMap (verticalNormalTwistedInclude F (d := d) χ) ((d+1)*n)
  letI : Epi f := epi_verticalNormalTwistedInclude F χ hn
  letI : Mono f := (ModuleCat.mono_iff_injective f).mpr (by
    apply (injective_iff_map_eq_zero f.hom).mpr
    intro x hx
    obtain h := verticalNormal_eq_coordinate_smul F χ hd hn i₀ x
    rw [h, map_smul] at hx
    have ha := (smul_eq_zero.mp hx).resolve_right (verticalEulerTargetGenerator_ne_zero F χ hd hn i₀)
    rw [h, ha, zero_smul])
  exact isIso_of_mono_of_epi f

/-- The final nonvanishing calculation is a genuine twisted source
coefficient and a nontriviality calculation in the Euler target. -/
theorem associatedBMTwistedEulerMap_apply_ne_zero_iff_coefficient
    (χ : ConfigurationGroup n →* Fˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    [Nontrivial ((associatedBMTwistedTarget F (d := d+1) χ).homology ((d+1)*n))]
    (c : (associatedBMTwistedSource F (d := d+1) χ).homology ((d+1)*n)) :
    associatedBMTwistedEulerMap F χ ((d+1)*n) c ≠ 0 ↔
      verticalEulerCoefficient F χ hd hn i₀ c ≠ 0 := by
  rw [associatedBMTwistedEulerMap_apply_eq_coefficient_smul F χ hd hn i₀ c,
    smul_ne_zero_iff]
  exact and_iff_left (verticalEulerTargetGenerator_ne_zero F χ hd hn i₀)

/-- A nonzero collapse coefficient of an actual twisted source class
therefore obstructs every nowhere-zero equivariant section. -/
theorem equivariant_has_zero_of_verticalEulerCoefficient_ne_zero
    (χ : ConfigurationGroup n →* Fˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    [Nontrivial ((associatedBMTwistedTarget F (d := d+1) χ).homology ((d+1)*n))]
    (c : (associatedBMTwistedSource F (d := d+1) χ).homology ((d+1)*n))
    (hc : verticalEulerCoefficient F χ hd hn i₀ c ≠ 0)
    (f : C(Configuration (d+1) n, ReducedValues (d+1) n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) : ∃ x, f x = 0 := by
  apply equivariant_has_zero_of_associatedBMTwistedEulerMap_ne_zero F χ ((d+1)*n) _ f he
  intro hz
  have hc' := (associatedBMTwistedEulerMap_apply_ne_zero_iff_coefficient F χ hd hn i₀ c).mpr hc
  exact hc' (by rw [hz]; rfl)

end Field
end NRR.PrimePowerTopology
