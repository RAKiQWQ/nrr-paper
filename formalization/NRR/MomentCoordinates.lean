import NRR.Coordinates
import NRR.GlobalAssembly

/-! Splitting the horizontal additive moment into the complex coordinate
used by the planar construction and the remaining real coordinates. -/

noncomputable section
open Set Topology MeasureTheory

namespace NRR.MomentCoordinates

def twoComplex : Space 2 ≃L[ℝ] ℂ :=
  (Coordinates.horizontalHeight 1).trans
    ((Coordinates.spaceOne.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      Complex.equivRealProdCLM.symm)

def horizontalSplit (q : ℕ) : Space (q+2) ≃L[ℝ] ℂ × Space q :=
  (EuclideanSpace.finAddEquivProd (n := q) (m := 2)).trans
    (((ContinuousLinearEquiv.refl ℝ (Space q)).prodCongr twoComplex).trans
      (ContinuousLinearEquiv.prodComm ℝ (Space q) ℂ))

def complexProjection (q : ℕ) : Space (q+2) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℂ (Space q)).comp (horizontalSplit q).toContinuousLinearMap

def remainingProjection (q : ℕ) : Space (q+2) →L[ℝ] Space q :=
  (ContinuousLinearMap.snd ℝ ℂ (Space q)).comp (horizontalSplit q).toContinuousLinearMap

theorem zero_iff_projections {q : ℕ} (u : Space (q+2)) :
    u = 0 ↔ complexProjection q u = 0 ∧ remainingProjection q u = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _,map_zero _⟩
  · rintro ⟨hc,hr⟩
    apply (horizontalSplit q).injective
    apply Prod.ext
    · exact hc
    · exact hr

def complexMoment {B : Type*} [TopologicalSpace B] {q : ℕ}
    (W : C(B,Space (q+2))) : C(B,ℂ) :=
  ⟨fun C => complexProjection q (W C),(complexProjection q).continuous.comp W.continuous⟩

def remainingMoment {B : Type*} [TopologicalSpace B] {q : ℕ}
    (W : C(B,Space (q+2))) : C(B,Space q) :=
  ⟨fun C => remainingProjection q (W C),(remainingProjection q).continuous.comp W.continuous⟩

theorem balanced_complex {B ι : Type*} [TopologicalSpace B] [Fintype ι] {q : ℕ}
    (W : C(B,Space (q+2))) (C : ι → B) (balanced : ∑ i,W (C i) = 0) :
    ∑ i,complexMoment W (C i) = 0 := by
  change ∑ i,complexProjection q (W (C i)) = 0
  rw [← map_sum,balanced,map_zero]

theorem balanced_remaining {B ι : Type*} [TopologicalSpace B] [Fintype ι] {q : ℕ}
    (W : C(B,Space (q+2))) (C : ι → B) (balanced : ∑ i,W (C i) = 0) :
    ∑ i,remainingMoment W (C i) = 0 := by
  change ∑ i,remainingProjection q (W (C i)) = 0
  rw [← map_sum,balanced,map_zero]

theorem moment_zero_iff {B : Type*} [TopologicalSpace B] {q : ℕ}
    (W : C(B,Space (q+2))) (C : B) :
    W C = 0 ↔ complexMoment W C = 0 ∧ remainingMoment W C = 0 :=
  zero_iff_projections (W C)

end NRR.MomentCoordinates
