import NRR.PrimePowerTopologyEulerThomRank
import NRR.PrimePowerTopologyShuffleIncidenceDegree

/-! Local detection of the ordered ambient fundamental class in the
compactified normal coordinates of the vertical stratum. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

private abbrev normalAmbientCollapse :=
  (canonicalEulerThomCollapse (d := d) (n := n)).comp (configurationOnePointCollapse (d+1) n)

private def normalAmbientChart :
    C(VerticalAssociated d n,OnePoint (Fin n → Space (d+1))) :=
  ⟨fun p => ((canonicalEulerThomCoordinates.symm p).val.val : OnePoint (Fin n → Space (d+1))),
    OnePoint.continuous_coe.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp canonicalEulerThomCoordinates.symm.continuous))⟩

private theorem normalAmbientChart_open : IsOpenEmbedding (normalAmbientChart (d := d) (n := n)) :=
  OnePoint.isOpenEmbedding_coe.comp ((isOpen_injectiveSites (d+1) n).isOpenEmbedding_subtypeVal.comp
    (isOpen_canonicalEulerThomOpen.isOpenEmbedding_subtypeVal.comp
      canonicalEulerThomCoordinates.symm.isOpenEmbedding))

private theorem normalCollapse_on_open (x : canonicalEulerThomOpen d n) :
    canonicalEulerThomCollapse (x.val : OnePoint (Configuration (d+1) n)) =
      (canonicalEulerThomCoordinates x : OnePoint (VerticalAssociated d n)) :=
  canonicalEulerThomCollapse_of_mem x.val x.property

private theorem normalAmbientCollapse_chart (p : VerticalAssociated d n) :
    normalAmbientCollapse (normalAmbientChart p) = (p : OnePoint (VerticalAssociated d n)) := by
  change canonicalEulerThomCollapse (configurationOnePointCollapse (d+1) n
    ((canonicalEulerThomCoordinates.symm p).val.val : OnePoint _)) = _
  rw [configurationOnePointCollapse_config,normalCollapse_on_open,Homeomorph.apply_symm_apply]

private theorem normalAmbientCollapse_fiber (p : VerticalAssociated d n)
    (z : OnePoint (Fin n → Space (d+1)))
    (hz : normalAmbientCollapse z = (p : OnePoint (VerticalAssociated d n))) :
    z = normalAmbientChart p := by
  induction z using OnePoint.rec with
  | infty => exact False.elim ((OnePoint.coe_ne_infty p) hz.symm)
  | coe x =>
    change canonicalEulerThomCollapse (configurationOnePointCollapse (d+1) n (x : OnePoint _)) = _ at hz
    by_cases hx : Function.Injective x
    · let c : Configuration (d+1) n := ⟨x,hx⟩
      rw [configurationOnePointCollapse_config c] at hz
      by_cases hc : c ∈ canonicalEulerThomOpen d n
      · let y : canonicalEulerThomOpen d n := ⟨c,hc⟩
        rw [normalCollapse_on_open y] at hz
        have he : y = canonicalEulerThomCoordinates.symm p :=
          canonicalEulerThomCoordinates.eq_symm_apply.mpr (OnePoint.coe_injective hz)
        exact congrArg (fun q : canonicalEulerThomOpen d n =>
          (q.val.val : OnePoint (Fin n → Space (d+1)))) he
      · rw [canonicalEulerThomCollapse_of_not_mem c hc] at hz
        exact False.elim ((OnePoint.coe_ne_infty p) hz.symm)
    · rw [configurationOnePointCollapse_collision x hx,canonicalEulerThomCollapse_infty] at hz
      exact False.elim ((OnePoint.coe_ne_infty p) hz.symm)

variable (R : Type) [Ring R]

/-- Composing the two open collapses, then localizing at any finite normal
point, gives an isomorphism in every positive degree. -/
theorem isIso_normalAmbientCollapse_local (p : VerticalAssociated d n) (q : ℕ) :
    IsIso (HabsMap R (q+1) (TopCat.ofHom (normalAmbientCollapse (d := d) (n := n))) ≫
      relJ R (q+1) (subIncl (Y := TopCat.of (OnePoint (VerticalAssociated d n)))
        {(p : OnePoint (VerticalAssociated d n))}ᶜ)) := by
  let v : C(VerticalAssociated d n,OnePoint (VerticalAssociated d n)) :=
    ⟨OnePoint.some,OnePoint.continuous_coe⟩
  letI := contractibleSpace_compl_point_of_sphere_homeomorph (n*(d+1))
    (vectorOnePointSphere (Fin n → Space (d+1)) _ (finrank_configurationAmbient _ _))
    (normalAmbientChart p)
  exact isIso_HabsMap_comp_localization_of_open_chart R normalAmbientCollapse normalAmbientChart v
    normalAmbientChart_open OnePoint.isOpenEmbedding_coe normalAmbientCollapse_chart p
    (normalAmbientCollapse_fiber p) q

private theorem mono_normalAmbientCollapse (q : ℕ) :
    Mono (HabsMap R (q+1) (TopCat.ofHom (normalAmbientCollapse (d := d) (n := n)))) := by
  obtain ⟨t,ht⟩ := heightChamber_nonempty n 1
  let p : VerticalAssociated d n := (verticalAssociatedHigherStratum (0 : Fin n)).symm
    ((verticalCoordinates (0 : Fin n)).symm (0,⟨t,heightChamber_injective ht⟩))
  let i := subIncl (Y := TopCat.of (OnePoint (VerticalAssociated d n))) {(p : OnePoint _)}ᶜ
  letI : IsIso (HabsMap R (q+1) (TopCat.ofHom normalAmbientCollapse) ≫ relJ R (q+1) i) :=
    isIso_normalAmbientCollapse_local R p q
  exact mono_of_mono (HabsMap R (q+1) (TopCat.ofHom normalAmbientCollapse)) (relJ R (q+1) i)

/-- The ordinary fundamental class survives the actual collapse into the
point-relative normal model, over every nonzero coefficient ring. -/
theorem verticalNormalCollapse_fundamental_ne_zero [Nontrivial R] (hpos : 0 < n*(d+1)) :
    HrelMap R (n*(d+1)) _ _ (verticalNormalCollapse_square (d := d) (n := n))
      (configurationBMFundamentalClass R (d+1) n hpos) ≠ 0 := by
  let k := n*(d+1)
  let F := TopCat.ofHom (configurationOnePointCollapse (d+1) n)
  let G := TopCat.ofHom (canonicalEulerThomCollapse (d := d) (n := n))
  let a := vectorOnePointFundamentalClass R (Fin n → Space (d+1)) k (finrank_configurationAmbient _ _) hpos
  have ha : a ≠ 0 := vectorOnePointFundamentalClass_ne_zero R _ _ _ _
  have hmono : Mono (HabsMap R k (F ≫ G) ≫ relJ R k (verticalNormalPointIncl d n)) := by
    obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 from hpos.ne')
    rw [hq]
    letI : Mono (HabsMap R (q+1) (F ≫ G)) := mono_normalAmbientCollapse R q
    letI : IsIso (relJ R (q+1) (verticalNormalPointIncl d n)) :=
      (pointRelativePositiveIso R q (X := TopCat.of (OnePoint (VerticalAssociated d n))) ∞).isIso_hom
    infer_instance
  have hn := relJ_naturality R k _ _ (verticalNormalCollapse_square (d := d) (n := n))
  have he : HabsMap R k F ≫ relJ R k (associatedBMSourceIncl (d+1) n) ≫
      HrelMap R k _ _ verticalNormalCollapse_square =
      HabsMap R k (F ≫ G) ≫ relJ R k (verticalNormalPointIncl d n) := by
    rw [hn,HabsMap_comp,Category.assoc]
  intro hz
  apply ha
  apply (ModuleCat.mono_iff_injective _).mp hmono
  rw [map_zero]
  exact (congrArg (fun m => ModuleCat.Hom.hom m a) he).symm.trans hz

end NRR.PrimePowerTopology
