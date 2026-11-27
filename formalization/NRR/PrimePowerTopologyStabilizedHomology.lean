import NRR.PrimePowerTopologyInfinityNeighborhood
import NRR.SingularHomologyFiniteCellGroups
import NRR.PrimePowerTopologyRelativePairOrbitBasisAssociatedBM
import NRR.PrimePowerTopologyTwistedBottomComparison

/-! The stabilized Fuks filtration computes the first possible degree of
the point-relative homology of the associated total space. This uses the
actual disk attachments with an arbitrary Euclidean factor. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] (d m k : ℕ) [NeZero m]

private def levelPoint (r : ℕ) : stabilizedFuksLevel d (m+1) k r :=
  ⟨∞,stabilizedFuksLevel_infty _ _ _ _⟩

private theorem degree_lower (c : Configuration (d+1) (m+1)) : d ≤ fuksComplexity c := by
  have h := (mem_fuksLevel_iff_complexity c).mpr (le_refl (fuksComplexity c))
  obtain ⟨P,hP,_⟩ := mem_fuksLevel_iff.mp h
  exact (fuksPatternCost_lower P).trans hP

private theorem initialLevel_singleton (r : ℕ) (hr : r ≤ d)
    (x : stabilizedFuksLevel d (m+1) k r) : x = levelPoint d m k r := by
  apply Subtype.ext
  rcases x.property with h | ⟨p,hp,he⟩
  · exact h
  · exact False.elim ((Nat.not_lt_of_le ((degree_lower d m p.1).trans' hr)) hp)

private theorem levelPoint_epi (r q : ℕ) (hq : q < d+(m+1)+k) :
    Epi (HabsMap R q (homologyPointIncl (X := TopCat.of (stabilizedFuksLevel d (m+1) k r))
      (levelPoint d m k r))) := by
  induction r with
  | zero =>
      let p := homologyPointIncl (X := TopCat.of (stabilizedFuksLevel d (m+1) k 0))
        (levelPoint d m k 0)
      let e : Unit ≃ₜ stabilizedFuksLevel d (m+1) k 0 :=
        { toFun := fun _ => levelPoint d m k 0
          invFun := fun _ => ()
          left_inv := fun _ => rfl
          right_inv := fun x => (initialLevel_singleton d m k 0 (Nat.zero_le _) x).symm
          continuous_toFun := continuous_const
          continuous_invFun := continuous_const }
      letI : IsIso p := (TopCat.isIso_iff_isHomeomorph _).mpr e.isHomeomorph
      change Epi (HabsMap R q p)
      unfold HabsMap CsingMap
      infer_instance
  | succ r ih =>
      let Y := TopCat.of (stabilizedFuksLevel d (m+1) k (r+1))
      let A := stabilizedFuksLowerSubset d m k r
      let i := subIncl (Y := Y) A
      let P := stabilizedFuksFiniteAttachment d m k r
      have hz : IsZero (Hrel R q i) := by
        by_cases hr : r < d
        · haveI : IsEmpty (StabilizedFuksCellIndex d m r) := ⟨fun c => by
            have h := c.2.property
            unfold generalCellFuksDegree at h
            omega⟩
          exact P.isZero_relative_of_empty R q
        · let a := r + m + k
          have hdim : Module.finrank ℝ (StabilizedFuksParameters m k r) = a+1 := by
            simp only [StabilizedFuksParameters,finrank_euclideanSpace_fin]
            dsimp [a]
            omega
          exact P.isZero_relative_off_dimension R
            ⟨levelPoint d m k (r+1),stabilizedFuksLevel_infty _ _ _ _⟩ a q hdim
            (by dsimp [a]; omega)
      letI : Epi (HabsMap R q i) := (pair_exact_iota_j R q i).epi_f (hz.eq_zero_of_tgt _)
      let e := TopCat.isoOfHomeo (X := TopCat.of (stabilizedFuksLevel d (m+1) k r))
        (Y := TopCat.of A) (stabilizedFuksLowerHomeomorph d m k r)
      have he : IsIso (HabsMap R q e.hom) := by unfold HabsMap CsingMap; infer_instance
      have w : homologyPointIncl (X := Y) (levelPoint d m k (r+1)) =
          homologyPointIncl (X := TopCat.of (stabilizedFuksLevel d (m+1) k r))
            (levelPoint d m k r) ≫ e.hom ≫ i := rfl
      rw [w,HabsMap_comp,HabsMap_comp]
      infer_instance

private theorem pointRelative_zero_of_epi {X : TopCat.{0}} (x : X) (q : ℕ)
    (he : Epi (HabsMap R q (homologyPointIncl x))) :
    IsZero (Hrel R q (homologyPointIncl x)) := by
  let i := homologyPointIncl x
  have hj : relJ R q i = 0 := (pair_exact_iota_j R q i).epi_f_iff.mp he
  cases q with
  | zero =>
      letI : Epi ((relProj R i).f 0) := (relShortComplex_degreewise_shortExact R i 0).epi_g
      letI : Epi (relJ R 0 i) :=
        HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (relProj R i) 0 (by intro j; simp)
      exact IsZero.of_epi_eq_zero _ hj
  | succ q =>
      exact IsZero.of_epi_eq_zero (pointRelativePositiveIso R q x).hom hj

/-- Below the smallest stabilized cell, the ordinary BM groups vanish. -/
theorem isZero_configurationProductBM_below (q : ℕ) (hq : q < d+(m+1)+k) :
    IsZero (Hrel R q (homologyPointIncl
      (X := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space k))) ∞)) := by
  apply pointRelative_zero_of_epi
  let t := d*(m+1)+1
  let e := TopCat.isoOfHomeo (X := TopCat.of (stabilizedFuksLevel d (m+1) k t))
    (Y := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space k)))
    (stabilizedFuksTopHomeomorph d m k)
  have w : homologyPointIncl (X := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space k))) ∞ =
      homologyPointIncl (X := TopCat.of (stabilizedFuksLevel d (m+1) k t))
        (levelPoint d m k t) ≫ e.hom := rfl
  letI := levelPoint_epi R d m k t q hq
  letI : IsIso (HabsMap R q e.hom) := by unfold HabsMap CsingMap; infer_instance
  rw [w,HabsMap_comp]
  infer_instance

/-- With the reduced-value representation as fiber, the bottom possible
degree of the total-space BM homology is the ambient configuration dimension. -/
theorem isZero_associatedBMCoverInfinity_below {D n q : ℕ}
    (hD : 0 < D) (hn : 2 ≤ n) (hq : q < D*n) :
    IsZero (Hrel R q (associatedBMCoverInfinityIncl D n)) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  letI : NeZero m := ⟨by omega⟩
  let l := d*m
  let fiber : ReducedValues (d+1) (m+1) ≃L[ℝ] Space l :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [finrank_reducedValues,finrank_euclideanSpace_fin]; rfl)
  let W := OnePoint (Configuration (d+1) (m+1) × Space l)
  let E := OnePoint (AssociatedCover (d+1) (m+1))
  let ambient := TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of W)
    ((Homeomorph.prodCongr (Homeomorph.refl _) fiber.toHomeomorph).onePointCongr)
  let source := TopCat.of ({∞} : Set E)
  let point := TopCat.isoOfHomeo (X := source) (Y := TopCat.of Unit)
    (Homeomorph.homeomorphOfUnique _ _)
  let i := associatedBMCoverInfinityIncl (d+1) (m+1)
  let j := homologyPointIncl (X := TopCat.of W) ∞
  have w : i ≫ ambient.hom = point.hom ≫ j := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    obtain ⟨z,hz⟩ := a
    have h : z = ∞ := hz
    subst z
    rfl
  letI := isIso_HrelMap_of_isIso R q i j w
  exact IsZero.of_iso (isZero_configurationProductBM_below R d m l q (by
    dsimp [l]; nlinarith)) (asIso (HrelMap R q i j w))

end NRR.PrimePowerTopology
