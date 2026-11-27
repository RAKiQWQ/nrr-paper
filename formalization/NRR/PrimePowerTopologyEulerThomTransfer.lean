import NRR.PrimePowerTopologyEulerThomAssembly
import NRR.PrimePowerTopologyTwistedFundamentalSource

/-! Signed transfer detects the normal collapse of a genuine twisted
source class. Only functoriality of actual relative singular chains is
used; transfer is not assumed injective on homology. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]

theorem verticalNormalPointAction_mul (g h : ConfigurationGroup n) :
    verticalNormalPointAction R (d := d) (g*h) =
      verticalNormalPointAction R h ≫ verticalNormalPointAction R g := by
  have hp : Epi (relProj R (verticalNormalPointIncl d n)) := coequalizer.π_epi
  apply hp.left_cancellation
  simp only [verticalNormalPointAction, relProj_comp_relComplexMap_assoc,
    relProj_comp_relComplexMap]
  rw [← Category.assoc, ← CsingMap_comp]
  congr 2
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p =>
    apply congrArg ((↑) : VerticalAssociated d n → OnePoint (VerticalAssociated d n))
    change (canonicalEulerThomKernelRelabel (g*h) p.1, (g*h) • p.2) =
      (canonicalEulerThomKernelRelabel g (canonicalEulerThomKernelRelabel h p.1),
        g • (h • p.2))
    apply Prod.ext
    · rfl
    · exact mul_smul g h p.2

/-- The genuine signed transfer from the compactified normal pair. -/
def verticalNormalTransfer (χ : ConfigurationGroup n →* Rˣ) :
    verticalNormalPointTwisted R (d := d) χ ⟶ relComplex R (verticalNormalPointIncl d n) :=
  twistedChainTransferDesc R χ _ (verticalNormalPointAction R) (verticalNormalPointAction_mul R)

/-- Normal collapse and signed transfer commute on actual chains. -/
@[reassoc]
theorem verticalNormalTwistedCollapse_transfer (χ : ConfigurationGroup n →* Rˣ) :
    verticalNormalTwistedCollapse R (d := d) χ ≫ verticalNormalTransfer R χ =
      twistedFundamentalSourceTransfer R χ ≫ relComplexMap R _ _ verticalNormalCollapse_square := by
  exact twistedChainTransferDesc_naturality R χ
    (associatedBMSourceRelativeAction R) (verticalNormalPointAction R)
    (relComplexMap R _ _ verticalNormalCollapse_square)
    (relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) associatedBMSourceRelabelMap
      (fun _ => 𝟙 _) canonicalEulerThomRelabelMap associatedBMSourceIncl_equivariant
      verticalNormalPointIncl_equivariant verticalNormalCollapse_square canonicalEulerThomCollapseMap_equivariant)
    (twistedFundamentalSourceAction_mul R) (verticalNormalPointAction_mul R)

@[reassoc]
theorem verticalNormalTwistedCollapse_homology_transfer (χ : ConfigurationGroup n →* Rˣ) (q : ℕ) :
    HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R (d := d) χ) q ≫
        HomologicalComplex.homologyMap (verticalNormalTransfer R χ) q =
      HomologicalComplex.homologyMap (twistedFundamentalSourceTransfer R χ) q ≫
        HrelMap R q _ _ verticalNormalCollapse_square := by
  rw [← HomologicalComplex.homologyMap_comp, verticalNormalTwistedCollapse_transfer,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- An ordinary local detector applied after transfer proves twisted
collapse nonvanishing, even in characteristic dividing the group order. -/
theorem verticalNormalTwistedCollapse_ne_zero_of_transfer
    (χ : ConfigurationGroup n →* Rˣ) (q : ℕ)
    (c : (associatedBMTwistedSource R (d := d+1) χ).homology q)
    (hc : HrelMap R q _ _ (verticalNormalCollapse_square (d := d) (n := n))
      (HomologicalComplex.homologyMap (twistedFundamentalSourceTransfer R χ) q c) ≠ 0) :
    HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R χ) q c ≠ 0 := by
  intro hz
  apply hc
  have h := congrArg (fun m => m c) (verticalNormalTwistedCollapse_homology_transfer R χ q)
  simp only [ModuleCat.comp_apply, hz, map_zero] at h
  exact h.symm

/-- The actual open normal collapse detects every nonzero ambient
compactification class in positive degree. No identification of a chosen
cycle with the abstractly normalized fundamental class is required. -/
theorem verticalNormalCollapse_ambientImage_ne_zero (q : ℕ)
    (a : Habs R (q+1) (TopCat.of (OnePoint (Fin n → Space (d+1))))) (ha : a ≠ 0) :
    HrelMap R (q+1) _ _ (verticalNormalCollapse_square (d := d) (n := n))
      (relJ R (q+1) (associatedBMSourceIncl (d+1) n)
        (HabsMap R (q+1) (TopCat.ofHom (configurationOnePointCollapse (d+1) n)) a)) ≠ 0 := by
  let F := TopCat.ofHom (configurationOnePointCollapse (d+1) n)
  let G := TopCat.ofHom (canonicalEulerThomCollapse (d := d) (n := n))
  obtain ⟨t, ht⟩ := heightChamber_nonempty n 1
  let p : VerticalAssociated d n := (verticalAssociatedHigherStratum (0 : Fin n)).symm
    ((verticalCoordinates (0 : Fin n)).symm (0, ⟨t, heightChamber_injective ht⟩))
  let j := subIncl (Y := TopCat.of (OnePoint (VerticalAssociated d n))) {(p : OnePoint _)}ᶜ
  haveI : IsIso (HabsMap R (q+1) (F ≫ G) ≫ relJ R (q+1) j) :=
    isIso_normalAmbientCollapse_local R p q
  haveI : Mono (HabsMap R (q+1) (F ≫ G)) :=
    mono_of_mono (HabsMap R (q+1) (F ≫ G)) (relJ R (q+1) j)
  haveI : IsIso (relJ R (q+1) (verticalNormalPointIncl d n)) :=
    (pointRelativePositiveIso R q (X := TopCat.of (OnePoint (VerticalAssociated d n))) ∞).isIso_hom
  let f := HabsMap R (q+1) (F ≫ G) ≫ relJ R (q+1) (verticalNormalPointIncl d n)
  have he : HabsMap R (q+1) F ≫ relJ R (q+1) (associatedBMSourceIncl (d+1) n) ≫
      HrelMap R (q+1) _ _ verticalNormalCollapse_square = f := by
    dsimp only [f]
    rw [relJ_naturality R (q+1) _ _ verticalNormalCollapse_square, HabsMap_comp, Category.assoc]
  intro hz
  apply ha
  apply (ModuleCat.mono_iff_injective f).mp inferInstance
  rw [map_zero]
  exact (congrArg (fun m => m a) he).symm.trans hz

/-- A transferred staircase class can be detected by its actual ambient
class, without comparing the chosen orientation normalizations. -/
theorem verticalNormalTwistedCollapse_ne_zero_of_transfer_ambientImage
    (χ : ConfigurationGroup n →* Rˣ) (q : ℕ)
    (c : (associatedBMTwistedSource R (d := d+1) χ).homology (q+1))
    (a : Habs R (q+1) (TopCat.of (OnePoint (Fin n → Space (d+1))))) (ha : a ≠ 0)
    (hc : HomologicalComplex.homologyMap (twistedFundamentalSourceTransfer R χ) (q+1) c =
      relJ R (q+1) (associatedBMSourceIncl (d+1) n)
        (HabsMap R (q+1) (TopCat.ofHom (configurationOnePointCollapse (d+1) n)) a)) :
    HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R χ) (q+1) c ≠ 0 := by
  apply verticalNormalTwistedCollapse_ne_zero_of_transfer R χ (q+1) c
  rw [hc]
  exact verticalNormalCollapse_ambientImage_ne_zero R q a ha

/-- In particular, a genuine twisted class transferring to the actual
ordered fundamental class is detected by the proved ordinary local chart. -/
theorem verticalNormalTwistedCollapse_ne_zero_of_transfer_fundamental
    [Nontrivial R] (χ : ConfigurationGroup n →* Rˣ) (hpos : 0 < n*(d+1))
    (c : (associatedBMTwistedSource R (d := d+1) χ).homology (n*(d+1)))
    (hc : HomologicalComplex.homologyMap (twistedFundamentalSourceTransfer R χ) (n*(d+1)) c =
      configurationBMFundamentalClass R (d+1) n hpos) :
    HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R χ) (n*(d+1)) c ≠ 0 := by
  apply verticalNormalTwistedCollapse_ne_zero_of_transfer R χ (n*(d+1)) c
  rw [hc]
  exact verticalNormalCollapse_fundamental_ne_zero R hpos

/-- In ambient degree, nonzero ordinary transferred normal image is
equivalent to a nonzero collapse coefficient in the direction needed for
the Euler obstruction. -/
theorem verticalEulerCoefficient_ne_zero_of_transfer
    (χ : ConfigurationGroup n →* Rˣ) (hd : 0 < d) (hn : 2 ≤ n) (i₀ : Fin n)
    (c : (associatedBMTwistedSource R (d := d+1) χ).homology ((d+1)*n))
    (hc : HrelMap R ((d+1)*n) _ _ (verticalNormalCollapse_square (d := d) (n := n))
      (HomologicalComplex.homologyMap (twistedFundamentalSourceTransfer R χ) ((d+1)*n) c) ≠ 0) :
    verticalEulerCoefficient R χ hd hn i₀ c ≠ 0 := by
  intro hz
  apply verticalNormalTwistedCollapse_ne_zero_of_transfer R χ ((d+1)*n) c hc
  let e := verticalNormalAmbientDegreeIso R χ hd hn i₀
  have hi := (ModuleCat.mono_iff_injective e.inv).mp inferInstance
  exact hi (hz.trans (map_zero e.inv.hom).symm)

end NRR.PrimePowerTopology
