import NRR.PrimePowerTopologyEulerThomRank
import NRR.PrimePowerTopologyBMTargetComparison

/-! In the first possible degree, the closed vertical normal locus
generates the ordinary homology of the compactified total space and the
twisted relative Euler target. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

private def stabilizedLevelMap (d n k : ℕ) {r s : ℕ} (h : r ≤ s) :
    TopCat.of (stabilizedFuksLevel d n k r) ⟶ TopCat.of (stabilizedFuksLevel d n k s) :=
  TopCat.ofHom ⟨Set.inclusion (stabilizedFuksLevel_mono d n k h),
    continuous_subtype_val.subtype_mk _⟩

private theorem epi_stabilizedMinimalLevelMap (d m k : ℕ) [NeZero m]
    {r : ℕ} (hr : d+1 ≤ r) :
    Epi (HabsMap R (d+(m+1)+k) (stabilizedLevelMap d (m+1) k hr)) := by
  let q := d+(m+1)+k
  induction r, hr using Nat.le_induction with
  | base =>
    rw [show stabilizedLevelMap d (m+1) k (le_refl (d+1)) = 𝟙 _ from rfl,HabsMap_id]
    infer_instance
  | succ r hr ih =>
    let Y := TopCat.of (stabilizedFuksLevel d (m+1) k (r+1))
    let A := stabilizedFuksLowerSubset d m k r
    let i := subIncl (Y := Y) A
    let P := stabilizedFuksFiniteAttachment d m k r
    have hz : IsZero (Hrel R q i) := by
      apply P.isZero_relative_off_dimension R
        ⟨⟨∞,stabilizedFuksLevel_infty _ _ _ _⟩,stabilizedFuksLevel_infty _ _ _ _⟩ (r+m+k)
      · simp only [StabilizedFuksParameters,finrank_euclideanSpace_fin]
        omega
      · dsimp [q]
        omega
    letI : Epi (HabsMap R q i) := (pair_exact_iota_j R q i).epi_f (hz.eq_zero_of_tgt _)
    let e := TopCat.isoOfHomeo (X := TopCat.of (stabilizedFuksLevel d (m+1) k r))
      (Y := TopCat.of A) (stabilizedFuksLowerHomeomorph d m k r)
    haveI : IsIso (HabsMap R q e.hom) := by unfold HabsMap CsingMap; infer_instance
    change Epi (HabsMap R q (stabilizedLevelMap d (m+1) k hr ≫ e.hom ≫ i))
    rw [HabsMap_comp,HabsMap_comp]
    infer_instance

private theorem epi_stabilizedMinimalVal (d m k : ℕ) [NeZero m] :
    Epi (HabsMap R (d+(m+1)+k)
      (subIncl (Y := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space k)))
        (stabilizedFuksLevel d (m+1) k (d+1)))) := by
  let t := d*(m+1)+1
  have ht : d+1 ≤ t := by dsimp [t]; nlinarith
  let e := TopCat.isoOfHomeo (X := TopCat.of (stabilizedFuksLevel d (m+1) k t))
    (Y := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space k)))
    (stabilizedFuksTopHomeomorph d m k)
  haveI : IsIso (HabsMap R (d+(m+1)+k) e.hom) := by unfold HabsMap CsingMap; infer_instance
  letI := epi_stabilizedMinimalLevelMap R d m k ht
  change Epi (HabsMap R _ (stabilizedLevelMap d (m+1) k ht ≫ e.hom))
  rw [HabsMap_comp]
  infer_instance

variable {d n : ℕ} [NeZero n]

private def normalFiberEuclidean (d m : ℕ) :
    ReducedValues (d+1) (m+1) ≃L[ℝ] Space (d*m) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_reducedValues,finrank_euclideanSpace_fin]; rfl)

private def normalCoverEuclidean (d m : ℕ) : OnePoint (AssociatedCover (d+1) (m+1)) ≃ₜ
    OnePoint (Configuration (d+1) (m+1) × Space (d*m)) :=
  ((Homeomorph.refl _).prodCongr (normalFiberEuclidean d m).toHomeomorph).onePointCongr

private def normalImageChart (d m : ℕ) : OnePoint (VerticalAssociated d (m+1)) ≃ₜ
    stabilizedFuksLevel d (m+1) (d*m) (d+1) := by
  let e := normalCoverEuclidean d m
  let f := e ∘ (canonicalEulerThomIncludeCompact (d := d) (n := m+1))
  have hf : Continuous f := e.continuous.comp canonicalEulerThomIncludeCompact.continuous
  have hi : Function.Injective f :=
    e.injective.comp (Option.map_injective isClosedEmbedding_canonicalEulerThomInclude.injective)
  refine (hf.isClosedEmbedding hi).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr ?_)
  ext z
  induction z using OnePoint.rec with
  | infty => exact iff_of_true ⟨∞,rfl⟩ (stabilizedFuksLevel_infty _ _ _ _)
  | coe p =>
    rcases p with ⟨c,v⟩
    rw [stabilizedFuksLevel_coe,Nat.lt_succ_iff,← mem_fuksLevel_iff_complexity,fuksLevel_minimal]
    constructor
    · rintro ⟨w,hw⟩
      induction w using OnePoint.rec with
      | infty => exact False.elim ((OnePoint.coe_ne_infty (c,v)) hw.symm)
      | coe w =>
        have hp : ((canonicalEulerThomInclude w).1,normalFiberEuclidean d m w.2) = (c,v) :=
          Option.some.inj hw
        have h : (canonicalEulerThomInclude w).1 = c := congrArg Prod.fst hp
        rw [← h]
        exact (canonicalSection_zero_iff _).mp w.1.val.property
    · intro hc
      let w : VerticalAssociated d (m+1) :=
        (⟨⟨c.val,(canonicalSection_zero_iff c).mpr hc⟩,c.property⟩,(normalFiberEuclidean d m).symm v)
      refine ⟨(w : OnePoint _),?_⟩
      exact congrArg (fun x : Space (d*m) => OnePoint.some (c,x))
        ((normalFiberEuclidean d m).apply_symm_apply v)

/-- The actual closed inclusion of the normal locus generates ordinary
absolute homology in the ambient configuration degree. -/
theorem epi_HabsMap_verticalNormalInclude (hn : 2 ≤ n) :
    Epi (HabsMap R ((d+1)*n) (TopCat.ofHom (canonicalEulerThomIncludeCompact (d := d) (n := n)))) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  letI : NeZero m := ⟨by omega⟩
  let q := (d+1)*(m+1)
  let e := TopCat.isoOfHomeo (X := TopCat.of (OnePoint (VerticalAssociated d (m+1))))
    (Y := TopCat.of (stabilizedFuksLevel d (m+1) (d*m) (d+1))) (normalImageChart d m)
  let a := TopCat.isoOfHomeo (X := TopCat.of (OnePoint (AssociatedCover (d+1) (m+1))))
    (Y := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space (d*m)))) (normalCoverEuclidean d m)
  let i := subIncl (Y := TopCat.of (OnePoint (Configuration (d+1) (m+1) × Space (d*m))))
    (stabilizedFuksLevel d (m+1) (d*m) (d+1))
  let f := TopCat.ofHom (canonicalEulerThomIncludeCompact (d := d) (n := m+1))
  have w : f ≫ a.hom = e.hom ≫ i := rfl
  haveI : Epi (HabsMap R q i) := by
    rw [show q = d+(m+1)+d*m by dsimp [q]; ring]
    exact epi_stabilizedMinimalVal R d m (d*m)
  haveI : IsIso (HabsMap R q e.hom) := by unfold HabsMap CsingMap; infer_instance
  haveI : IsIso (HabsMap R q a.hom) := by unfold HabsMap CsingMap; infer_instance
  have h : Epi (HabsMap R q f ≫ HabsMap R q a.hom) := by
    rw [← HabsMap_comp,w,HabsMap_comp]
    infer_instance
  have hw : HabsMap R q f = (HabsMap R q f ≫ HabsMap R q a.hom) ≫ inv (HabsMap R q a.hom) := by simp
  change Epi (HabsMap R q f)
  rw [hw]
  infer_instance

private theorem isIso_relJ_associatedBMTarget {D n q : ℕ} :
    IsIso (relJ R (q+1) (associatedBMTargetIncl D n)) := by
  let i := associatedBMCoverInfinityIncl D n
  let j := associatedBMTargetIncl D n
  haveI : IsIso (relJ R (q+1) i) :=
    (relativeOfContractiblePositiveIso R q i).isIso_hom
  let f := HrelMap R (q+1) i j associatedBMPointToComplement_square
  letI : IsIso f := isIso_associatedBMPointToComplement R (q+1)
  have w : relJ R (q+1) i ≫ f = relJ R (q+1) j := by
    rw [show relJ R (q+1) i ≫ f = _ from
      relJ_naturality R (q+1) i j associatedBMPointToComplement_square,HabsMap_id,Category.id_comp]
  rw [← w]
  infer_instance

theorem epi_HrelMap_verticalNormalInclude (hn : 2 ≤ n) :
    Epi (HrelMap R ((d+1)*n) _ _ (verticalNormalInclude_square (d := d) (n := n))) := by
  let q := (d+1)*n
  have hq : 0 < q := Nat.mul_pos (Nat.succ_pos d) (NeZero.pos n)
  let j := associatedBMTargetIncl (d+1) n
  letI : IsIso (relJ R q j) := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    rw [ha]
    exact isIso_relJ_associatedBMTarget R
  let f := TopCat.ofHom (canonicalEulerThomIncludeCompact (d := d) (n := n))
  letI : Epi (HabsMap R q f) := epi_HabsMap_verticalNormalInclude R hn
  let i := verticalNormalPointIncl d n
  let g := HrelMap R q i j verticalNormalInclude_square
  haveI : Epi (relJ R q i ≫ g) := by
    rw [show relJ R q i ≫ g = HabsMap R q f ≫ relJ R q j from
      relJ_naturality R q i j verticalNormalInclude_square]
    infer_instance
  exact epi_of_epi (relJ R q i) g

/-- All twisted Euler-target classes in the first possible degree are
represented by classes of the closed normal locus. -/
theorem epi_verticalNormalTwistedInclude (χ : ConfigurationGroup n →* Rˣ) (hn : 2 ≤ n) :
    Epi (HomologicalComplex.homologyMap (verticalNormalTwistedInclude R (d := d) χ) ((d+1)*n)) := by
  let q := (d+1)*n
  let f := relComplexMap R _ _ (verticalNormalInclude_square (d := d) (n := n))
  let π := twistedChainProj R χ _ (verticalNormalPointAction R (d := d))
  let τ := twistedChainProj R χ _ (associatedBMTargetRelativeAction R (d := d+1))
  let g := verticalNormalTwistedInclude R (d := d) χ
  have w : π ≫ g = f ≫ τ := twistedChainProj_map R χ _ _ _ _ _
  letI : Epi (HomologicalComplex.homologyMap f q) := epi_HrelMap_verticalNormalInclude R hn
  letI : Epi (HomologicalComplex.homologyMap τ q) :=
    epi_associatedBMTargetProjection R χ (Nat.succ_pos d) hn (le_refl q)
  haveI : Epi (HomologicalComplex.homologyMap π q ≫ HomologicalComplex.homologyMap g q) := by
    rw [← HomologicalComplex.homologyMap_comp,w,HomologicalComplex.homologyMap_comp]
    infer_instance
  exact epi_of_epi (HomologicalComplex.homologyMap π q) (HomologicalComplex.homologyMap g q)

end NRR.PrimePowerTopology
