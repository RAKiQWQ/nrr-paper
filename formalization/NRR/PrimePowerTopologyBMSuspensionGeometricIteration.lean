import NRR.PrimePowerTopologyBMSuspensionIteration
import NRR.SingularHomologyBMSuspensionGeometry

/-! Actual Euclidean BM dimension descent and its naturality for arbitrary
proper maps, configurations, and closed vertical cells. The only local input
is the concrete pointed good neighborhood at infinity, and configurations
and Euclidean charts supply that input without further hypotheses. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [Ring R]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- Apply the genuine geometric real-suspension isomorphism to every
Euclidean stabilization of a well-pointed compactification. -/
def geometricBMRealSuspensionSteps
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞) :
    BMRealSuspensionSteps R X := fun r q hq =>
  RealSuspension.geometricReducedSuspensionIso R (G r) q hq

/-- Actual dimension descent by `r` real coordinates, in every positive
target degree. -/
def geometricBMSpaceSuspensionIso
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Hbm R (q+r) (X × Space r) ≅ Hbm R q X :=
  bmSpaceSuspensionIsoOfSteps R (geometricBMRealSuspensionSteps R G) q hq r

theorem geometricBMRealSuspensionSteps_naturality
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (G' : ∀ r, PointGoodNeighborhood (OnePoint (Y × Space r)) ∞)
    (f : X → Y) (hf : IsProperMap f) :
    (geometricBMRealSuspensionSteps R G).Naturality R
      (geometricBMRealSuspensionSteps R G') f hf := by
  intro r q hq
  exact RealSuspension.geometricReducedSuspensionIso_proper_naturality R
    (G r) (G' r) (Prod.map f (id : Space r → Space r))
    (hf.prodMap isProperMap_id) q hq

/-- Genuine proper-map naturality, including closed inclusions. All
Euclidean factors are retained by the actual map `f × id`. -/
@[reassoc]
theorem geometricBMSpaceSuspensionIso_proper_naturality
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (G' : ∀ r, PointGoodNeighborhood (OnePoint (Y × Space r)) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (geometricBMSpaceSuspensionIso R G q hq r).hom ≫ HbmMap R q f hf =
      HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) ≫ (geometricBMSpaceSuspensionIso R G' q hq r).hom :=
  bmSpaceSuspensionIsoOfSteps_naturality R _ _ f hf
    (geometricBMRealSuspensionSteps_naturality R G G' f hf) q hq r

/-- Stabilize a specified genuine BM class by the inverse of geometric
dimension descent. -/
def geometricBMSpaceStabilizeClass
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (q : ℕ) (hq : 0 < q) (r : ℕ) (z : Hbm R q X) :
    Hbm R (q+r) (X × Space r) :=
  (geometricBMSpaceSuspensionIso R G q hq r).inv z

@[simp] theorem geometricBMSpaceSuspensionIso_stabilizeClass
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (q : ℕ) (hq : 0 < q) (r : ℕ) (z : Hbm R q X) :
    (geometricBMSpaceSuspensionIso R G q hq r).hom
      (geometricBMSpaceStabilizeClass R G q hq r z) = z := by
  exact congrArg (fun f => f z) (geometricBMSpaceSuspensionIso R G q hq r).inv_hom_id

/-- The specified stabilized class is natural under the actual product
proper map, with no choice of a representative cycle. -/
theorem geometricBMSpaceStabilizeClass_naturality
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (G' : ∀ r, PointGoodNeighborhood (OnePoint (Y × Space r)) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) (r : ℕ)
    (z : Hbm R q X) :
    HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) (geometricBMSpaceStabilizeClass R G q hq r z) =
      geometricBMSpaceStabilizeClass R G' q hq r (HbmMap R q f hf z) := by
  apply (ModuleCat.mono_iff_injective
    (geometricBMSpaceSuspensionIso R G' q hq r).hom).mp inferInstance
  have h := congrArg (fun k => k (geometricBMSpaceStabilizeClass R G q hq r z))
    (geometricBMSpaceSuspensionIso_proper_naturality R G G' f hf q hq r)
  simpa only [ConcreteCategory.comp_apply,
    geometricBMSpaceSuspensionIso_stabilizeClass] using h.symm

theorem geometricBMSpaceSuspensionMap_class_ne_zero_iff
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (G' : ∀ r, PointGoodNeighborhood (OnePoint (Y × Space r)) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) (r : ℕ)
    (z : Hbm R (q+r) (X × Space r)) :
    HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) z ≠ 0 ↔
      HbmMap R q f hf ((geometricBMSpaceSuspensionIso R G q hq r).hom z) ≠ 0 :=
  bmSpaceSuspensionMap_class_ne_zero_iffOfSteps R _ _ f hf
    (geometricBMRealSuspensionSteps_naturality R G G' f hf) q hq r z

/-- The geometric comparison also acts on ordinary absolute homology of
the actual one-point compactifications in positive degrees. -/
def geometricAbsoluteSpaceSuspensionIso
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Habs R (q+r) (TopCat.of (OnePoint (X × Space r))) ≅
      Habs R q (TopCat.of (OnePoint X)) :=
  bmAbsoluteSpaceSuspensionIsoOfSteps R (geometricBMRealSuspensionSteps R G) q hq r

@[reassoc]
theorem geometricAbsoluteSpaceSuspensionIso_proper_naturality
    (G : ∀ r, PointGoodNeighborhood (OnePoint (X × Space r)) ∞)
    (G' : ∀ r, PointGoodNeighborhood (OnePoint (Y × Space r)) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (geometricAbsoluteSpaceSuspensionIso R G q hq r).hom ≫
        HabsMap R q (properOnePointMap f hf) =
      HabsMap R (q+r) (properOnePointMap (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id)) ≫
          (geometricAbsoluteSpaceSuspensionIso R G' q hq r).hom :=
  bmAbsoluteSpaceSuspensionIsoOfSteps_naturality R _ _ f hf
    (geometricBMRealSuspensionSteps_naturality R G G' f hf) q hq r

/-- Actual configuration-space BM suspension; no suspension datum is
assumed. The good neighborhoods come from the proved finite cell collars. -/
def configurationBMSpaceSuspensionIso (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Hbm R (q+r) (Configuration d n × Space r) ≅ Hbm R q (Configuration d n) :=
  geometricBMSpaceSuspensionIso R
    (fun k => configurationSpaceProductInfinityGoodNeighborhood d n k hd hn) q hq r

/-- Actual Euclidean BM suspension, including a zero-dimensional base. -/
def euclideanBMSpaceSuspensionIso (a q : ℕ) (hq : 0 < q) (r : ℕ) :
    Hbm R (q+r) (Space a × Space r) ≅ Hbm R q (Space a) :=
  geometricBMSpaceSuspensionIso R (spaceProductInfinityGoodNeighborhood a) q hq r

/-- The natural square for any genuine proper map from a Euclidean source
to configuration space, with no extra geometric choices. -/
@[reassoc]
theorem euclideanToConfigurationBMSpaceSuspensionIso_naturality
    (a d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n)
    (f : Space a → Configuration d n) (hf : IsProperMap f)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (euclideanBMSpaceSuspensionIso R a q hq r).hom ≫ HbmMap R q f hf =
      HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) ≫
          (configurationBMSpaceSuspensionIso R d n hd hn q hq r).hom :=
  geometricBMSpaceSuspensionIso_proper_naturality R
    (spaceProductInfinityGoodNeighborhood a)
    (fun k => configurationSpaceProductInfinityGoodNeighborhood d n k hd hn) f hf q hq r

/-- Any proper map between genuine configuration spaces has natural
dimension descent in all stabilizing dimensions. -/
@[reassoc]
theorem configurationBMSpaceSuspensionIso_proper_naturality
    (d n e m : ℕ) (hd : 0 < d) (hn : 2 ≤ n) (he : 0 < e) (hm : 2 ≤ m)
    (f : Configuration d n → Configuration e m) (hf : IsProperMap f)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (configurationBMSpaceSuspensionIso R d n hd hn q hq r).hom ≫ HbmMap R q f hf =
      HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) ≫
          (configurationBMSpaceSuspensionIso R e m he hm q hq r).hom :=
  geometricBMSpaceSuspensionIso_proper_naturality R
    (fun k => configurationSpaceProductInfinityGoodNeighborhood d n k hd hn)
    (fun k => configurationSpaceProductInfinityGoodNeighborhood e m k he hm) f hf q hq r

instance locallyCompactSpace_heightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LocallyCompactSpace (heightChamber n σ) := (isOpen_heightChamber n σ).locallyCompactSpace

/-- The genuine parameter space of a single closed vertical cell has
unconditional Euclidean dimension descent. -/
def verticalCellBMSpaceSuspensionIso (d n : ℕ) (σ : Equiv.Perm (Fin n))
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Hbm R (q+r) ((Space d × heightChamber n σ) × Space r) ≅
      Hbm R q (Space d × heightChamber n σ) :=
  geometricBMSpaceSuspensionIso R
    (verticalCellParameterProductInfinityGoodNeighborhood d n σ) q hq r

/-- Naturality for the actual closed proper vertical-cell embedding.
In particular this is the inclusion square needed for stabilized Fuks classes. -/
@[reassoc]
theorem verticalCellBMSpaceSuspensionIso_inclusion_naturality
    (d n : ℕ) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (verticalCellBMSpaceSuspensionIso R d n σ q hq r).hom ≫
        HbmMap R q (verticalCellEmbedding (d := d) i₀ σ)
          (isClosedEmbedding_verticalCell i₀ σ).isProperMap =
      HbmMap R (q+r)
        (Prod.map (verticalCellEmbedding (d := d) i₀ σ) (id : Space r → Space r))
        ((isClosedEmbedding_verticalCell i₀ σ).isProperMap.prodMap isProperMap_id) ≫
          (configurationBMSpaceSuspensionIso R (d+1) n (by omega) hn q hq r).hom :=
  geometricBMSpaceSuspensionIso_proper_naturality R
    (verticalCellParameterProductInfinityGoodNeighborhood d n σ)
    (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k (by omega) hn)
    _ (isClosedEmbedding_verticalCell i₀ σ).isProperMap q hq r

/-- Vanishing or nonvanishing of the actual closed-cell inclusion map is
unchanged by an arbitrary Euclidean stabilization. -/
theorem verticalCellBMSpaceSuspensionMap_zero_iff
    (d n : ℕ) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    HbmMap R (q+r)
        (Prod.map (verticalCellEmbedding (d := d) i₀ σ) (id : Space r → Space r))
        ((isClosedEmbedding_verticalCell i₀ σ).isProperMap.prodMap isProperMap_id) = 0 ↔
      HbmMap R q (verticalCellEmbedding (d := d) i₀ σ)
        (isClosedEmbedding_verticalCell i₀ σ).isProperMap = 0 :=
  bmSpaceSuspensionMap_zero_iffOfSteps R _ _ _ _
    (geometricBMRealSuspensionSteps_naturality R
      (verticalCellParameterProductInfinityGoodNeighborhood d n σ)
      (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k (by omega) hn)
      _ (isClosedEmbedding_verticalCell i₀ σ).isProperMap) q hq r

/-- The product map in the natural square really is a closed embedding. -/
theorem isClosedEmbedding_stabilizedVerticalCell
    (d n : ℕ) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (r : ℕ) :
    IsClosedEmbedding
      (Prod.map (verticalCellEmbedding (d := d) i₀ σ) (id : Space r → Space r)) := by
  let f := verticalCellEmbedding (d := d) i₀ σ
  have he := (isClosedEmbedding_verticalCell (d := d) i₀ σ).isEmbedding.prodMap
    (show IsEmbedding (id : Space r → Space r) from .id)
  exact .of_isEmbedding_isClosedMap he
    (((isClosedEmbedding_verticalCell i₀ σ).isProperMap.prodMap isProperMap_id).isClosedMap)

/-- Nonvanishing of a specified genuine closed-cell image is preserved
and reflected at every Euclidean stabilization. -/
theorem verticalCellBMSpaceSuspensionMap_class_ne_zero_iff
    (d n : ℕ) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) (r : ℕ)
    (z : Hbm R (q+r) ((Space d × heightChamber n σ) × Space r)) :
    HbmMap R (q+r)
        (Prod.map (verticalCellEmbedding (d := d) i₀ σ) (id : Space r → Space r))
        ((isClosedEmbedding_verticalCell i₀ σ).isProperMap.prodMap isProperMap_id) z ≠ 0 ↔
      HbmMap R q (verticalCellEmbedding (d := d) i₀ σ)
        (isClosedEmbedding_verticalCell i₀ σ).isProperMap
        ((verticalCellBMSpaceSuspensionIso R d n σ q hq r).hom z) ≠ 0 :=
  geometricBMSpaceSuspensionMap_class_ne_zero_iff R
    (verticalCellParameterProductInfinityGoodNeighborhood d n σ)
    (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k (by omega) hn)
    _ (isClosedEmbedding_verticalCell i₀ σ).isProperMap q hq r z

/-- Naturality on the ordinary homology model used by Euler--Thom
comparison, for the actual compactified closed vertical-cell embedding. -/
@[reassoc]
theorem verticalCellAbsoluteSpaceSuspensionIso_inclusion_naturality
    (d n : ℕ) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (geometricAbsoluteSpaceSuspensionIso R
      (verticalCellParameterProductInfinityGoodNeighborhood d n σ) q hq r).hom ≫
        HabsMap R q (properOnePointMap (verticalCellEmbedding (d := d) i₀ σ)
          (isClosedEmbedding_verticalCell i₀ σ).isProperMap) =
      HabsMap R (q+r) (properOnePointMap
        (Prod.map (verticalCellEmbedding (d := d) i₀ σ) (id : Space r → Space r))
        ((isClosedEmbedding_verticalCell i₀ σ).isProperMap.prodMap isProperMap_id)) ≫
          (geometricAbsoluteSpaceSuspensionIso R
            (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k
              (by omega) hn) q hq r).hom :=
  geometricAbsoluteSpaceSuspensionIso_proper_naturality R
    (verticalCellParameterProductInfinityGoodNeighborhood d n σ)
    (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k (by omega) hn)
    _ (isClosedEmbedding_verticalCell i₀ σ).isProperMap q hq r

end NRR.PrimePowerTopology
