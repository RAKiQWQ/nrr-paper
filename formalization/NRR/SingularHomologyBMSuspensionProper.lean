import NRR.SingularHomologyBMSuspensionCollapse

/-! The maps used by BM suspension are the actual extensions of proper
maps, including closed embeddings and product reflection. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.PrimePowerTopology
open scoped OnePoint

namespace NRR.SingularHomology
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Proper maps extend continuously to the actual one-point compactifications.
No metrizability or local compactness assumption is needed for this fact. -/
def properOnePointMap (f : X → Y) (hf : IsProperMap f) :
    TopCat.of (OnePoint X) ⟶ TopCat.of (OnePoint Y) :=
  TopCat.ofHom ⟨OnePoint.map f, OnePoint.continuous_map hf.continuous (by
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨K, ⟨hKcl,hKco⟩, hKs⟩ := Filter.hasBasis_coclosedCompact.mem_iff.mp hs
    exact Filter.mem_of_superset
      ((hf.isCompact_preimage hKco).compl_mem_coclosedCompact_of_isClosed
        (hKcl.preimage hf.continuous)) (Set.preimage_mono hKs))⟩

@[simp] theorem properOnePointMap_infty (f : X → Y) (hf : IsProperMap f) :
    properOnePointMap f hf ∞ = ∞ := rfl

@[simp] theorem properOnePointMap_coe (f : X → Y) (hf : IsProperMap f) (x : X) :
    properOnePointMap f hf (x : OnePoint X) = (f x : OnePoint Y) := rfl

@[simp] theorem properOnePointMap_id :
    properOnePointMap (id : X → X) isProperMap_id = 𝟙 _ := by
  ext x
  exact congrFun OnePoint.map_id x

theorem properOnePointMap_comp (f : X → Y) (hf : IsProperMap f)
    (g : Y → Z) (hg : IsProperMap g) :
    properOnePointMap f hf ≫ properOnePointMap g hg =
      properOnePointMap (g ∘ f) (hg.comp hf) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrFun (OnePoint.map_comp g f).symm x

/-- The closed-stratum map uses the ordinary extension of its inclusion. -/
def closedEmbeddingOnePointMap (f : X → Y) (hf : IsClosedEmbedding f) :
    TopCat.of (OnePoint X) ⟶ TopCat.of (OnePoint Y) := properOnePointMap f hf.isProperMap

/-- Extension of a homeomorphism, agreeing literally with `onePointCongr`. -/
theorem properOnePointMap_homeomorph (e : X ≃ₜ Y) :
    properOnePointMap e e.isProperMap =
      TopCat.ofHom ⟨e.onePointCongr,e.onePointCongr.continuous⟩ := rfl

/-- Stabilization of an actual proper map, retaining the real coordinate. -/
def properRealProductMap (f : X → Y) (hf : IsProperMap f) :
    TopCat.of (OnePoint (X × ℝ)) ⟶ TopCat.of (OnePoint (Y × ℝ)) :=
  properOnePointMap (Prod.map f id) (hf.prodMap isProperMap_id)

/-- Stabilization of an actual proper map, reflecting the real coordinate. -/
def properRealReflectionMap (f : X → Y) (hf : IsProperMap f) :
    TopCat.of (OnePoint (X × ℝ)) ⟶ TopCat.of (OnePoint (Y × ℝ)) :=
  properOnePointMap (Prod.map f (fun t : ℝ => -t))
    (hf.prodMap (Homeomorph.neg ℝ).isProperMap)

variable (R : Type) [Ring R]

/-- The canonical point-relative singular homology map of a proper map. -/
def HbmMap (q : ℕ) (f : X → Y) (hf : IsProperMap f) : Hbm R q X ⟶ Hbm R q Y :=
  HrelMap R q (homologyPointIncl (X := TopCat.of (OnePoint X)) ∞)
    (homologyPointIncl (X := TopCat.of (OnePoint Y)) ∞)
    (f := properOnePointMap f hf) (fA := 𝟙 _) (by ext u; rfl)

/-- Absolute/reduced comparison is natural for the actual proper-map action. -/
@[reassoc]
theorem pointRelativePositiveIso_proper_naturality (q : ℕ) (f : X → Y) (hf : IsProperMap f) :
    (pointRelativePositiveIso R q (X := TopCat.of (OnePoint X)) ∞).hom ≫ HbmMap R (q+1) f hf =
      HabsMap R (q+1) (properOnePointMap f hf) ≫
        (pointRelativePositiveIso R q (X := TopCat.of (OnePoint Y)) ∞).hom :=
  relJ_naturality R (q+1) _ _ _

/-- Naturality of BM suspension for actual proper maps once their
geometrically chosen caps and overlap projections are compatible. -/
@[reassoc]
theorem bmSuspensionIso_proper_naturality
    (S : BMSuspensionCover X) (T : BMSuspensionCover Y)
    (f : X → Y) (hf : IsProperMap f)
    (hA : Set.MapsTo (properRealProductMap f hf) S.lower T.lower)
    (hB : Set.MapsTo (properRealProductMap f hf) S.upper T.upper)
    (hoverlap : mvIntersectionMap (X := TopCat.of (OnePoint (X × ℝ))) (Y := TopCat.of (OnePoint (Y × ℝ))) S.lower S.upper T.lower T.upper
        (properRealProductMap f hf) hA hB ≫ TopCat.ofHom T.overlap.toFun =
      TopCat.ofHom S.overlap.toFun ≫ properOnePointMap f hf)
    (q : ℕ) (hq : 0 < q) :
    (bmSuspensionIso R S q hq).hom ≫ HabsMap R q (properOnePointMap f hf) =
      HabsMap R (q+1) (properRealProductMap f hf) ≫ (bmSuspensionIso R T q hq).hom :=
  S.shift_naturality T R ⟨_,_,hA,hB,hoverlap⟩ q

/-- For reflection, the same proper-map naturality square has a minus sign. -/
@[reassoc]
theorem bmSuspensionIso_reflection_naturality
    (S : BMSuspensionCover X) (T : BMSuspensionCover Y)
    (f : X → Y) (hf : IsProperMap f)
    (hA : Set.MapsTo (properRealReflectionMap f hf) S.lower T.upper)
    (hB : Set.MapsTo (properRealReflectionMap f hf) S.upper T.lower)
    (hoverlap : mvSwappedIntersectionMap (X := TopCat.of (OnePoint (X × ℝ))) (Y := TopCat.of (OnePoint (Y × ℝ))) S.lower S.upper T.lower T.upper
        (properRealReflectionMap f hf) hA hB ≫ TopCat.ofHom T.overlap.toFun =
      TopCat.ofHom S.overlap.toFun ≫ properOnePointMap f hf)
    (q : ℕ) (hq : 0 < q) :
    (bmSuspensionIso R S q hq).hom ≫ HabsMap R q (properOnePointMap f hf) =
      -(HabsMap R (q+1) (properRealReflectionMap f hf) ≫
        (bmSuspensionIso R T q hq).hom) :=
  S.shift_reversing_naturality T R ⟨_,_,hA,hB,hoverlap⟩ q

/-- Reduced degree zero vanishes for every pointed path-connected space. -/
theorem isZero_pointRelative_zero {W : Type} [TopologicalSpace W]
    [PathConnectedSpace W] (p : W) :
    IsZero (Hrel R 0 (homologyPointIncl (X := TopCat.of W) p)) := by
  let i := homologyPointIncl (X := TopCat.of W) p
  letI : IsIso (HabsMap R 0 i) := isIso_HabsMap_zero_of_pathConnected R i
  have hj : relJ R 0 i = 0 := (pair_exact_iota_j R 0 i).epi_f_iff.mp (by
    change Epi (HabsMap R 0 i)
    infer_instance)
  letI : Epi ((relProj R i).f 0) := (relShortComplex_degreewise_shortExact R i 0).epi_g
  letI : Epi (relJ R 0 i) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
      (relProj R i) 0 (by intro j; simp)
  exact IsZero.of_epi_eq_zero _ hj

/-- Every actual real suspension has zero reduced degree-zero homology. -/
theorem isZero_bmRealProduct_zero (S : BMSuspensionCover X) :
    IsZero (Hbm R 0 (X × ℝ)) := by
  letI := S.pathConnectedSpace
  exact isZero_pointRelative_zero R (∞ : OnePoint (X × ℝ))

/-- The reduced first homology vanishes when the pointed base is path connected. -/
theorem isZero_bmRealProduct_one (S : BMSuspensionCover X)
    [PathConnectedSpace (OnePoint X)] : IsZero (Hbm R 1 (X × ℝ)) :=
  IsZero.of_iso (S.isZero_one R)
    (pointRelativePositiveIso R 0 (X := TopCat.of (OnePoint (X × ℝ))) ∞).symm

/-- The arc-collapse model also gives reduced degree-zero vanishing. -/
theorem isZero_bmCollapsed_zero {W : Type} [TopologicalSpace W] [T2Space X]
    (S : CollapsedBMSuspension X W) : IsZero (Hbm R 0 (X × ℝ)) := by
  letI := S.presentation.pathConnectedSpace
  letI := S.collapse.quotient.surjective.pathConnectedSpace S.collapse.map.continuous
  exact isZero_pointRelative_zero R (∞ : OnePoint (X × ℝ))

end NRR.SingularHomology
