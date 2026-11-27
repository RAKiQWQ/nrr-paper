import NRR.PrimePowerTopologyMinimalGeneration
import NRR.SingularHomologyClosedCollapse

/-! Local detection of a sphere map on singular homology by excision at a
point with a single preimage and matching open charts. -/

noncomputable section

open Set Topology CategoryTheory Limits
open NRR.PrimePowerTopology

namespace NRR.SingularHomology

private theorem chart_puncture_cover {X T : Type} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace T] {u : T → X} (hu : IsOpenEmbedding u) (t : T) :
    interior (range u) ∪ interior ({u t}ᶜ : Set X) = univ := by
  rw [hu.isOpen_range.interior_eq, isClosed_singleton.isOpen_compl.interior_eq]
  apply eq_univ_of_forall
  intro x
  by_cases h : x = u t
  · exact Or.inl ⟨t,h.symm⟩
  · exact Or.inr h

section LocalChart
variable (R : Type) [Ring R]
    {X Y T : Type} [TopologicalSpace X] [T1Space X] [TopologicalSpace Y] [T1Space Y]
    [TopologicalSpace T] (f : C(X,Y)) (u : C(T,X)) (v : C(T,Y))
    (hu : IsOpenEmbedding u) (hv : IsOpenEmbedding v) (hcomm : ∀ t, f (u t) = v t)
    (t : T) (hfiber : ∀ x, f x = v t → x = u t)

include hcomm hfiber in
private theorem chart_maps_puncture : MapsTo f ({u t}ᶜ : Set X) ({v t}ᶜ : Set Y) :=
  fun _ hx e => hx (hfiber _ e)

include hu hv in
/-- Excision identifies the local homology at the two chart points in all degrees. -/
theorem isIso_localHomologyMap_of_open_chart (q : ℕ) : IsIso (HrelMap R q
    (subIncl (Y := TopCat.of X) {u t}ᶜ) (subIncl (Y := TopCat.of Y) {v t}ᶜ)
    (mvRestrictMap_subIncl _ _ (TopCat.ofHom f) (chart_maps_puncture f u v hcomm t hfiber)).symm) := by
  let U := range u
  let V := range v
  let N := ({u t}ᶜ : Set X)
  let M := ({v t}ᶜ : Set Y)
  let F := TopCat.ofHom f
  have hU : MapsTo F U V := by
    rintro x ⟨a,rfl⟩
    exact ⟨a, (hcomm a).symm⟩
  have hiff (x : X) : x ∈ N ↔ F x ∈ M :=
    not_congr ⟨fun h : x = u t => h ▸ hcomm t, hfiber x⟩
  have hN : MapsTo F N M := fun x hx => (hiff x).mp hx
  let e : U ≃ₜ V := hu.isEmbedding.toHomeomorph.symm.trans hv.isEmbedding.toHomeomorph
  have he (x : U) : (e x).val = F x.val := by
    obtain ⟨a,ha⟩ := hu.isEmbedding.toHomeomorph.surjective x
    rw [← ha]
    change v (hu.isEmbedding.toHomeomorph.symm (hu.isEmbedding.toHomeomorph a)) = f (u a)
    rw [Homeomorph.symm_apply_apply, hcomm]
  let l := mvRestrictMap (X := TopCat.of X) (Y := TopCat.of Y) U V F hU
  letI : IsIso l := (TopCat.isIso_iff_isHomeomorph _).mpr (by
    have hh : (⇑l : U → V) = e := funext fun x => Subtype.ext (he x).symm
    rw [hh]
    exact e.isHomeomorph)
  let e' : (U ∩ N : Set X) ≃ₜ (V ∩ M : Set Y) :=
    (intersectionSubtypeHomeomorph U N).trans ((e.subtype (fun x => by
      rw [he]
      exact hiff x.val)).trans (intersectionSubtypeHomeomorph V M).symm)
  let l' := mvIntersectionMap (X := TopCat.of X) (Y := TopCat.of Y) U N V M F hU hN
  letI : IsIso l' := (TopCat.isIso_iff_isHomeomorph _).mpr (by
    have hh : (⇑l' : (U ∩ N : Set X) → (V ∩ M : Set Y)) = e' := by
      funext x
      exact Subtype.ext (he ⟨x.val,x.property.1⟩).symm
    rw [hh]
    exact e'.isHomeomorph)
  exact isIso_HrelMap_of_excisionComparison (X := TopCat.of X) (Y := TopCat.of Y)
    R U N V M F hU hN (chart_puncture_cover hu t) (chart_puncture_cover hv t) q

include hu hv hcomm hfiber in
/-- When only the source puncture is contractible, the map into the
target local group still detects every positive-degree source class. -/
theorem isIso_HabsMap_comp_localization_of_open_chart [ContractibleSpace ({u t}ᶜ : Set X)]
    (q : ℕ) : IsIso (HabsMap R (q+1) (TopCat.ofHom f) ≫
      relJ R (q+1) (subIncl (Y := TopCat.of Y) {v t}ᶜ)) := by
  let N := ({u t}ᶜ : Set X)
  let M := ({v t}ᶜ : Set Y)
  let F := TopCat.ofHom f
  let w := (mvRestrictMap_subIncl (X := TopCat.of X) (Y := TopCat.of Y) N M F
    (chart_maps_puncture f u v hcomm t hfiber)).symm
  let g := HrelMap R (q+1) (subIncl (Y := TopCat.of X) N) (subIncl (Y := TopCat.of Y) M) w
  letI : IsIso g := isIso_localHomologyMap_of_open_chart R f u v hu hv hcomm t hfiber (q+1)
  let a := relativeOfContractiblePositiveIso R q (subIncl (Y := TopCat.of X) N)
  have h : HabsMap R (q+1) F ≫ relJ R (q+1) (subIncl (Y := TopCat.of Y) M) = a.hom ≫ g :=
    (relJ_naturality R (q+1) _ _ w).symm
  rw [h]
  infer_instance

include hu hv hcomm hfiber in
theorem isIso_HabsMap_of_open_chart
    [ContractibleSpace ({u t}ᶜ : Set X)] [ContractibleSpace ({v t}ᶜ : Set Y)]
    (q : ℕ) : IsIso (HabsMap R (q+1) (TopCat.ofHom f)) := by
  let F := TopCat.ofHom f
  let b := relativeOfContractiblePositiveIso R q (subIncl (Y := TopCat.of Y) {v t}ᶜ)
  letI : IsIso (HabsMap R (q+1) F ≫ b.hom) :=
    isIso_HabsMap_comp_localization_of_open_chart R f u v hu hv hcomm t hfiber q
  exact IsIso.of_isIso_comp_right (HabsMap R (q+1) F) b.hom

end LocalChart

end NRR.SingularHomology
