import NRR.PrimePowerTopologyInfinityNeighborhoodCore
import NRR.PrimePowerTopologyMinimalGeneration

/-! Pointed good neighborhoods of infinity in actual Euclidean
compactifications. A stereographic chart avoiding the antipode of infinity
transports the affine contraction fixing its chosen center. -/

noncomputable section
open Set Topology Metric
open scoped OnePoint
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

/-- A vector chart on an open neighborhood gives a contraction fixing the
marked point, with no dimension or nonzero-point assumptions. -/
def pointGoodNeighborhoodOfVectorChart {X E : Type} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set X) (hU : IsOpen U)
    (p : X) (hp : p ∈ U) (e : U ≃ₜ E) : PointGoodNeighborhood X p where
  neighborhood := U
  isOpen := hU
  mem := hp
  contraction := {
    toFun := fun z => e.symm ((1-(z.1 : ℝ)) • e ⟨p,hp⟩ + (z.1 : ℝ) • e z.2)
    continuous_toFun := e.symm.continuous.comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        continuous_const).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (e.continuous.comp continuous_snd)))
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp }
  fixed := by
    intro t
    change e.symm ((1-(t : ℝ)) • e ⟨p,hp⟩ + (t : ℝ) • e ⟨p,hp⟩) = ⟨p,hp⟩
    rw [← add_smul, sub_add_cancel, one_smul, e.symm_apply_apply]

/-- Every point of an actual metric sphere has an actual open pointed
good neighborhood, including the zero-dimensional sphere. -/
def spherePointGoodNeighborhood (q : ℕ) (b : Sph q) :
    PointGoodNeighborhood (Sph q) b :=
  pointGoodNeighborhoodOfVectorChart {x : Sph q | x ≠ -b}
    (isClosed_singleton.isOpen_compl) b (ne_neg_of_mem_unit_sphere ℝ b)
    (puncturedSphereChart q b)

/-- The actual one-point compactification of any finite-dimensional real
normed vector space is well pointed at infinity. -/
def vectorInfinityGoodNeighborhood (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    PointGoodNeighborhood (OnePoint V) ∞ := by
  let e := vectorOnePointSphere V (Module.finrank ℝ V) rfl
  simpa only [Homeomorph.symm_apply_apply] using
    (spherePointGoodNeighborhood _ (e ∞)).homeomorph e.symm

def spaceInfinityGoodNeighborhood (a : ℕ) :
    PointGoodNeighborhood (OnePoint (Space a)) ∞ :=
  vectorInfinityGoodNeighborhood (Space a)

def spaceProductInfinityGoodNeighborhood (a r : ℕ) :
    PointGoodNeighborhood (OnePoint (Space a × Space r)) ∞ :=
  vectorInfinityGoodNeighborhood (Space a × Space r)

/-- A genuine Euclidean chart supplies all the pointed neighborhoods
needed to iterate suspension, also for a closed cell in configuration space. -/
def vectorChartProductInfinityGoodNeighborhood {X V : Type} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : X ≃ₜ V) (r : ℕ) :
    PointGoodNeighborhood (OnePoint (X × Space r)) ∞ :=
  (vectorInfinityGoodNeighborhood (V × Space r)).homeomorph
    (e.prodCongr (Homeomorph.refl (Space r))).symm.onePointCongr

/-- The parameter space of a single actual vertical cell is Euclidean. -/
def verticalCellParameterProductInfinityGoodNeighborhood (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) :
    PointGoodNeighborhood (OnePoint ((Space d × heightChamber n σ) × Space r)) ∞ :=
  vectorChartProductInfinityGoodNeighborhood
    ((Homeomorph.refl (Space d)).prodCongr (heightChamberEuclidean n σ)) r

/-- The same neighborhoods on the closed vertical cell itself, transported
through its actual coordinate chart. -/
def verticalCellProductInfinityGoodNeighborhood {d n : ℕ} (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) :
    PointGoodNeighborhood (OnePoint (verticalCellSet d n σ × Space r)) ∞ :=
  (verticalCellParameterProductInfinityGoodNeighborhood d n σ r).homeomorph
    ((verticalCellCoordinates i₀ σ).prodCongr (Homeomorph.refl (Space r))).symm.onePointCongr

end NRR.PrimePowerTopology
