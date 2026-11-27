import NRR.ClosedPolyhedralConeGraph
import NRR.PrimePowerTopologyShuffleIncidenceDegree

/-! A common coordinate chart on the entire genuine characteristic
boundary, fixed on its gap-zero face. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

def twoColumnGapKernelEquiv {d n : ℕ} (S : Finset (Fin n)) :
    (Space (d+1) × (Fin n → ℝ)) ≃ₗ[ℝ]
      LinearMap.ker (twoColumnConeFunctional (d := d) S none) where
  toFun p := ⟨((horizontalHeight d p.1,p.2),0),rfl⟩
  invFun p := ((horizontalHeight d).symm p.val.1.1,p.val.1.2)
  left_inv p := by simp
  right_inv p := by
    apply Subtype.ext
    have hp : p.val.2 = 0 := p.property
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hp.symm
  map_add' p q := by
    apply Subtype.ext
    change (((horizontalHeight d) (p.1+q.1),p.2+q.2),0) =
      (((horizontalHeight d) p.1,p.2),0)+(((horizontalHeight d) q.1,q.2),0)
    simp [map_add]
  map_smul' a p := by
    apply Subtype.ext
    change (((horizontalHeight d) (a • p.1),a • p.2),0) =
      a • (((horizontalHeight d) p.1,p.2),0)
    simp [map_smul]

def twoColumnCharacteristicBoundaryConeHomeomorph {d n : ℕ}
    (S : Finset (Fin n)) :
    twoColumnCharacteristicBoundary (d := d) S ≃ₜ
      ClosedPolyhedralCone.compactifiedBoundary (twoColumnConeFunctional (d := d) S) :=
  (twoColumnCompactConeHomeomorph S).subtype
    (fun x => (twoColumnCompactConeHomeomorph_boundary_iff S x).symm)

/-- A single actual chart for the full characteristic boundary, obtained
by projecting the finite cone boundary along its positive direction. -/
def twoColumnBoundaryGraphHomeomorph {d n : ℕ} (S : Finset (Fin n)) :
    OnePoint (Space (d+1) × (Fin n → ℝ)) ≃ₜ
      twoColumnCharacteristicBoundary (d := d) S :=
  (twoColumnGapKernelEquiv (d := d) S).toContinuousLinearEquiv.toHomeomorph.onePointCongr.trans
    (((ClosedPolyhedralCone.finiteBoundaryGraphHomeomorph
      (twoColumnConeFunctional (d := d) S) (twoColumnConeDirection_positive S)
      (twoColumnConeFunctional (d := d) S none) (by rfl)).onePointCongr).trans
        ((ClosedPolyhedralCone.finiteBoundaryCompactificationHomeomorph
          (twoColumnConeFunctional (d := d) S)).trans
            (twoColumnCharacteristicBoundaryConeHomeomorph (d := d) S).symm))

/-- On every genuine shuffle face, the common graph chart retains the
original common position and labelled heights exactly. -/
theorem twoColumnBoundaryGraphHomeomorph_shuffle {d n : ℕ}
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle S σ) (p : Space (d+1) × heightChamber n σ) :
    twoColumnBoundaryGraphHomeomorph (d := d) S
        ((p.1,p.2.val) : Space (d+1) × (Fin n → ℝ)) =
      twoColumnShuffleBoundaryChart S σ hs p := by
  let x := twoColumnGapKernelEquiv (d := d) S (p.1,p.2.val)
  have hx : x.val ∈ ClosedPolyhedralCone.finiteBoundary (twoColumnConeFunctional S) := by
    refine ⟨(closedTwoColumnDomain_iff_cone S _).mp
      (twoColumnShuffleFace S σ hs p).property, ?_⟩
    intro h
    exact (lt_irrefl (0 : ℝ)) (h none)
  have he := ClosedPolyhedralCone.finiteBoundaryGraphHomeomorph_apply_of_boundary
    (twoColumnConeFunctional (d := d) S) (twoColumnConeDirection_positive S)
    (twoColumnConeFunctional (d := d) S none) (by rfl) x hx
  apply Subtype.ext
  apply congrArg OnePoint.some
  apply Subtype.ext
  exact he

end NRR.PrimePowerTopology
