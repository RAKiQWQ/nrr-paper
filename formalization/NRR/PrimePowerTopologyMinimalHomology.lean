import NRR.PrimePowerTopologyMinimalRetraction
import NRR.PrimePowerTopologySphereHomology
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Fundamental classes of the actual compactified minimal Fuks cells.
Continuous cell retractions give genuine independent singular homology
classes; no cellular chain complex is substituted for the space. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

def minimalCellInclusionMap {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (Space d × heightChamber n σ)) ⟶
      TopCat.of (minimalSkeleton d n) :=
  TopCat.ofHom (minimalCellInclusion i₀ σ)

def minimalCellRetractionMap {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    TopCat.of (minimalSkeleton d n) ⟶
      TopCat.of (OnePoint (Space d × heightChamber n σ)) :=
  TopCat.ofHom (minimalCellRetraction i₀ σ)

@[simp] theorem minimalCellInclusionMap_retraction {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    minimalCellInclusionMap (d := d) i₀ σ ≫ minimalCellRetractionMap (d := d) i₀ σ = 𝟙 _ := by
  ext p
  exact minimalCellRetraction_same i₀ σ p

theorem minimalCellInclusionMap_retraction_other {d n : ℕ}
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) (hne : σ ≠ τ) :
    minimalCellInclusionMap (d := d) i₀ σ ≫ minimalCellRetractionMap (d := d) i₀ τ =
      TopCat.ofHom (ContinuousMap.const _ (∞ : OnePoint (Space d × heightChamber n τ))) := by
  ext p
  exact minimalCellRetraction_other i₀ τ σ hne p

variable (R : Type) [Ring R]

private def sphereTopHomologyIsoOfPos (m : ℕ) (hm : 0 < m) :
    Habs R m (TopCat.of (Sph m)) ≅ ModuleCat.of R R := by
  cases m with
  | zero => omega
  | succ m => exact sphereTopHomologyIso R m

/-- The genuine top homology of one compactified minimal Euclidean cell. -/
def minimalCellTopHomologyIso (d n : ℕ) (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    Habs R (d+n) (TopCat.of (OnePoint (Space d × heightChamber n σ))) ≅
      ModuleCat.of R R :=
  HabsIsoOfHomotopyEquiv R (d+n) (verticalCellSphere d n σ).toHomotopyEquiv ≪≫
    sphereTopHomologyIsoOfPos R (d+n) hdim

def minimalCellGenerator {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hdim : 0 < d+n) :
    ModuleCat.of R R ⟶ Habs R (d+n) (TopCat.of (minimalSkeleton d n)) :=
  (minimalCellTopHomologyIso R d n σ hdim).inv ≫
    HabsMap R (d+n) (minimalCellInclusionMap (d := d) i₀ σ)

def minimalCellCoefficient {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hdim : 0 < d+n) :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ⟶ ModuleCat.of R R :=
  HabsMap R (d+n) (minimalCellRetractionMap (d := d) i₀ σ) ≫
    (minimalCellTopHomologyIso R d n σ hdim).hom

theorem minimalCellGenerator_coefficient_same {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    minimalCellGenerator R i₀ σ hdim ≫ minimalCellCoefficient R i₀ σ hdim = 𝟙 _ := by
  have h : HabsMap R (d+n) (minimalCellInclusionMap (d := d) i₀ σ) ≫
      HabsMap R (d+n) (minimalCellRetractionMap (d := d) i₀ σ) = 𝟙 _ := by
    rw [← HabsMap_comp, minimalCellInclusionMap_retraction, HabsMap_id]
  unfold minimalCellGenerator minimalCellCoefficient
  rw [Category.assoc, ← Category.assoc _ _ (minimalCellTopHomologyIso R d n σ hdim).hom,
    h, Category.id_comp, Iso.inv_hom_id]

theorem minimalCellGenerator_coefficient_other {d n : ℕ}
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) (hne : σ ≠ τ) :
    minimalCellGenerator R i₀ σ hdim ≫ minimalCellCoefficient R i₀ τ hdim = 0 := by
  have h : HabsMap R (d+n) (minimalCellInclusionMap (d := d) i₀ σ) ≫
      HabsMap R (d+n) (minimalCellRetractionMap (d := d) i₀ τ) = 0 := by
    rw [← HabsMap_comp, minimalCellInclusionMap_retraction_other i₀ σ τ hne]
    exact HabsMap_const_eq_zero R (d+n) hdim.ne'
      (X := TopCat.of (OnePoint (Space d × heightChamber n σ)))
      (Y := TopCat.of (OnePoint (Space d × heightChamber n τ))) ∞
  unfold minimalCellGenerator minimalCellCoefficient
  rw [Category.assoc, ← Category.assoc _ _ (minimalCellTopHomologyIso R d n τ hdim).hom,
    h, zero_comp, comp_zero]

/-- Each actual sphere contributes a genuine nonzero class in the whole
minimal skeleton, detected by its continuous retraction coefficient. -/
def minimalFundamentalClass {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hdim : 0 < d+n) : Habs R (d+n) (TopCat.of (minimalSkeleton d n)) :=
  minimalCellGenerator R i₀ σ hdim 1

theorem minimalFundamentalClass_coefficient {d n : ℕ}
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    minimalCellCoefficient R i₀ τ hdim (minimalFundamentalClass R i₀ σ hdim) =
      if σ = τ then 1 else 0 := by
  classical
  by_cases h : σ = τ
  · subst τ
    simpa only [if_pos rfl] using
      congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
        (minimalCellGenerator_coefficient_same R i₀ σ hdim)
  · have he := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
      (minimalCellGenerator_coefficient_other R i₀ σ τ hdim h)
    simpa only [if_neg h] using he

theorem minimalFundamentalClass_ne_zero [Nontrivial R] {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    minimalFundamentalClass R i₀ σ hdim ≠ 0 := by
  intro hz
  have h := minimalFundamentalClass_coefficient R i₀ σ σ hdim
  rw [hz, map_zero, if_pos rfl] at h
  exact zero_ne_one h


/-- The actual cell fundamental classes are linearly independent in the
singular homology of the genuine lowest Fuks skeleton. -/
theorem linearIndependent_minimalFundamentalClass {d n : ℕ}
    (i₀ : Fin n) (hdim : 0 < d+n) :
    LinearIndependent R (fun σ : Equiv.Perm (Fin n) =>
      minimalFundamentalClass R i₀ σ hdim) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg τ
  let c : Habs R (d+n) (TopCat.of (minimalSkeleton d n)) →ₗ[R] R :=
    (minimalCellCoefficient R i₀ τ hdim).hom
  have cv (σ : Equiv.Perm (Fin n)) :
      c (minimalFundamentalClass R i₀ σ hdim) = if σ = τ then 1 else 0 :=
    minimalFundamentalClass_coefficient R i₀ σ τ hdim
  have h := congrArg c hg
  simp only [map_sum, map_smul, cv, map_zero, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at h
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

end NRR.PrimePowerTopology
