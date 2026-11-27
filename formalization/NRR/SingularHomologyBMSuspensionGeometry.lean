import NRR.SingularHomologyBMSuspensionModel

/-! Real BM suspension on the actual one-point compactification, obtained
from a pointed good neighborhood of infinity, with proper-map naturality. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Topology CategoryTheory Limits AlgebraicTopology unitInterval
open NRR.PrimePowerTopology NRR.SuspensionGeometry
open scoped OnePoint

namespace NRR.SingularHomology
namespace RealSuspension
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y]

theorem collapse_proper_naturality (f : X → Y) (hf : IsProperMap f) :
    TopCat.ofHom (Susp.map (properOnePointMap f hf).hom) ≫ TopCat.ofHom (collapse (X := Y)).map =
      TopCat.ofHom (collapse (X := X)).map ≫ properRealProductMap f hf := by
  ext z
  by_cases hz : z ∈ Susp.arc (∞ : OnePoint X)
  · obtain ⟨t,rfl⟩ := hz
    change collapse.map (Susp.mk (t,(∞ : OnePoint Y))) =
      properRealProductMap f hf (collapse.map (Susp.mk (t,(∞ : OnePoint X))))
    rw [collapse_arc,collapse_arc]
    rfl
  · have hr : z ∈ range (realEmbedding (X := X)) := by
      rw [range_realEmbedding]
      exact hz
    obtain ⟨⟨x,r⟩,rfl⟩ := hr
    change collapse.map (realEmbedding (f x,r)) =
      properRealProductMap f hf (collapse.map (realEmbedding (x,r)))
    rw [collapse_realEmbedding,collapse_realEmbedding]
    rfl

theorem collapse_reflection_naturality (f : X → Y) (hf : IsProperMap f) :
    TopCat.ofHom (Susp.reflect.comp (Susp.map (properOnePointMap f hf).hom)) ≫
        TopCat.ofHom (collapse (X := Y)).map =
      TopCat.ofHom (collapse (X := X)).map ≫ properRealReflectionMap f hf := by
  ext z
  by_cases hz : z ∈ Susp.arc (∞ : OnePoint X)
  · obtain ⟨t,rfl⟩ := hz
    change collapse.map (Susp.mk (σ t,(∞ : OnePoint Y))) =
      properRealReflectionMap f hf (collapse.map (Susp.mk (t,(∞ : OnePoint X))))
    rw [collapse_arc,collapse_arc]
    rfl
  · have hr : z ∈ range (realEmbedding (X := X)) := by
      rw [range_realEmbedding]
      exact hz
    obtain ⟨⟨x,r⟩,rfl⟩ := hr
    change collapse.map (Susp.mk (σ (realLevel r).val,(f x : OnePoint Y))) =
      properRealReflectionMap f hf (collapse.map (realEmbedding (x,r)))
    rw [← realLevel_neg]
    change collapse.map (realEmbedding (f x,-r)) = _
    rw [collapse_realEmbedding,collapse_realEmbedding]
    rfl

variable (R : Type) [Ring R]

def geometricSuspensionIso (G : PointGoodNeighborhood (OnePoint X) ∞) (q : ℕ) (hq : 0 < q) :
    Habs R (q+1) (TopCat.of (OnePoint (X × ℝ))) ≅ Habs R q (TopCat.of (OnePoint X)) :=
  (model G).shiftIso R q hq

@[reassoc]
theorem geometricSuspensionIso_proper_naturality
    (G : PointGoodNeighborhood (OnePoint X) ∞) (G' : PointGoodNeighborhood (OnePoint Y) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) :
    (geometricSuspensionIso R G q hq).hom ≫ HabsMap R q (properOnePointMap f hf) =
      HabsMap R (q+1) (properRealProductMap f hf) ≫ (geometricSuspensionIso R G' q hq).hom :=
  (model G).shift_naturality R (model G') (map (properOnePointMap f hf).hom)
    (properRealProductMap f hf) (collapse_proper_naturality f hf) q hq

@[reassoc]
theorem geometricSuspensionIso_reflection_naturality
    (G : PointGoodNeighborhood (OnePoint X) ∞) (G' : PointGoodNeighborhood (OnePoint Y) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) :
    (geometricSuspensionIso R G q hq).hom ≫ HabsMap R q (properOnePointMap f hf) =
      -(HabsMap R (q+1) (properRealReflectionMap f hf) ≫ (geometricSuspensionIso R G' q hq).hom) :=
  (model G).shift_reversing_naturality R (model G') (reversingMap (properOnePointMap f hf).hom)
    (properRealReflectionMap f hf) (collapse_reflection_naturality f hf) q hq

/-- The requested suspension isomorphism for actual point-relative singular homology. -/
def geometricReducedSuspensionIso (G : PointGoodNeighborhood (OnePoint X) ∞)
    (q : ℕ) (hq : 0 < q) : Hbm R (q+1) (X × ℝ) ≅ Hbm R q X := by
  cases q with
  | zero => omega
  | succ q =>
    exact (pointRelativePositiveIso R (q+1) (X := TopCat.of (OnePoint (X × ℝ))) ∞).symm ≪≫
      geometricSuspensionIso R G (q+1) hq ≪≫
      pointRelativePositiveIso R q (X := TopCat.of (OnePoint X)) ∞

/-- The geometric suspension comparison commutes with the actual point-relative
homology maps induced by every proper map and its product with the real line. -/
@[reassoc]
theorem geometricReducedSuspensionIso_proper_naturality
    (G : PointGoodNeighborhood (OnePoint X) ∞) (G' : PointGoodNeighborhood (OnePoint Y) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) :
    (geometricReducedSuspensionIso R G q hq).hom ≫ HbmMap R q f hf =
      HbmMap R (q+1) (Prod.map f (id : ℝ → ℝ)) (hf.prodMap isProperMap_id) ≫
        (geometricReducedSuspensionIso R G' q hq).hom := by
  cases q with
  | zero => omega
  | succ q =>
    let A := pointRelativePositiveIso R (q+1) (X := TopCat.of (OnePoint (X × ℝ))) ∞
    let B := pointRelativePositiveIso R (q+1) (X := TopCat.of (OnePoint (Y × ℝ))) ∞
    have hw : A.inv ≫ HabsMap R (q+1+1) (properRealProductMap f hf) =
        HbmMap R (q+1+1) (Prod.map f (id : ℝ → ℝ)) (hf.prodMap isProperMap_id) ≫ B.inv := by
      apply (cancel_epi A.hom).mp
      rw [Iso.hom_inv_id_assoc, ← Category.assoc]
      change _ = ((pointRelativePositiveIso R (q+1)
        (X := TopCat.of (OnePoint (X × ℝ))) ∞).hom ≫
          HbmMap R (q+1+1) (Prod.map f (id : ℝ → ℝ)) (hf.prodMap isProperMap_id)) ≫ B.inv
      rw [pointRelativePositiveIso_proper_naturality, Category.assoc]
      change _ = HabsMap R (q+1+1) (properRealProductMap f hf) ≫ B.hom ≫ B.inv
      rw [Iso.hom_inv_id, Category.comp_id]
    change (A.inv ≫ (geometricSuspensionIso R G (q+1) hq).hom ≫
        (pointRelativePositiveIso R q (X := TopCat.of (OnePoint X)) ∞).hom) ≫
          HbmMap R (q+1) f hf =
      HbmMap R (q+1+1) (Prod.map f (id : ℝ → ℝ)) (hf.prodMap isProperMap_id) ≫
        (B.inv ≫ (geometricSuspensionIso R G' (q+1) hq).hom ≫
          (pointRelativePositiveIso R q (X := TopCat.of (OnePoint Y)) ∞).hom)
    simp only [Category.assoc]
    rw [pointRelativePositiveIso_proper_naturality,
      geometricSuspensionIso_proper_naturality_assoc R G G' f hf (q+1) hq]
    rw [← Category.assoc, hw, Category.assoc]

/-- Naturality, with the shorter interface name used by geometric clients. -/
@[reassoc]
theorem geometricReducedSuspensionIso_naturality
    (G : PointGoodNeighborhood (OnePoint X) ∞) (G' : PointGoodNeighborhood (OnePoint Y) ∞)
    (f : X → Y) (hf : IsProperMap f) (q : ℕ) (hq : 0 < q) :
    (geometricReducedSuspensionIso R G q hq).hom ≫ HbmMap R q f hf =
      HbmMap R (q+1) (Prod.map f (id : ℝ → ℝ)) (hf.prodMap isProperMap_id) ≫
        (geometricReducedSuspensionIso R G' q hq).hom :=
  geometricReducedSuspensionIso_proper_naturality R G G' f hf q hq

end RealSuspension
end NRR.SingularHomology
