import NRR.PrimePowerTopologyVertical
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-! Actual Euclidean charts for the minimal vertical Fuks cells and sphere
charts for their one-point compactifications. -/

noncomputable section
open Set Topology Metric

namespace NRR.PrimePowerTopology

def boundedHeightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  heightChamber n σ ∩ {t | ∀ i,t i ∈ Ioo (-(Real.pi/2)) (Real.pi/2)}

theorem isOpen_boundedHeightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (boundedHeightChamber n σ) := by
  apply (isOpen_heightChamber n σ).inter
  have repr : {t : Fin n → ℝ | ∀ i,t i ∈ Ioo (-(Real.pi/2)) (Real.pi/2)} =
      ⋂ i : Fin n,(fun t : Fin n → ℝ => t i) ⁻¹' Ioo (-(Real.pi/2)) (Real.pi/2) := by
    ext t
    simp
  rw [repr]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

theorem convex_boundedHeightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Convex ℝ (boundedHeightChamber n σ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_heightChamber n σ hx.1 hy.1 ha hb hab,?_⟩
  intro i
  exact convex_Ioo (-(Real.pi/2)) (Real.pi/2) (hx.2 i) (hy.2 i) ha hb hab

theorem boundedHeightChamber_nonempty (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (boundedHeightChamber n σ).Nonempty := by
  obtain ⟨t,ht⟩ := heightChamber_nonempty n σ
  exact ⟨fun i => Real.arctan (t i),Real.arctan_strictMono.comp ht,
    fun i => Real.arctan_mem_Ioo (t i)⟩

theorem isBounded_boundedHeightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Bornology.IsBounded (boundedHeightChamber n σ) := by
  have hc := isCompact_univ_pi (fun _ : Fin n =>
    isCompact_Icc (a := -(Real.pi/2)) (b := Real.pi/2))
  apply hc.isBounded.subset
  intro t ht i _
  exact ⟨(ht.2 i).1.le,(ht.2 i).2.le⟩

/-- Coordinatewise arctangent bounds the ordering chamber while preserving
all strict label orderings. This does not assume a generic convex-set chart. -/
def boundHeightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    heightChamber n σ ≃ₜ boundedHeightChamber n σ where
  toFun t := ⟨fun i => Real.arctan (t.val i),
    Real.arctan_strictMono.comp t.property,fun i => Real.arctan_mem_Ioo (t.val i)⟩
  invFun t := ⟨fun i => Real.tanOrderIso ⟨t.val i,t.property.2 i⟩,by
    intro i j hij
    apply Real.tanOrderIso.strictMono
    exact t.property.1 hij⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    exact Real.tanOrderIso.apply_symm_apply (t.val i)
  right_inv t := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (Real.tanOrderIso.symm_apply_apply ⟨t.val i,t.property.2 i⟩)
  continuous_toFun :=
    (continuous_pi (fun i => Real.continuous_arctan.comp
      ((continuous_apply i).comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact Real.tanOrderIso.toHomeomorph.continuous.comp
      (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)

/-- Each minimal ordering chamber is genuinely a Euclidean open cell of
dimension n. The bounded convex chart is obtained by the proved gauge
rescale homeomorphism, not by an assumed cellular decomposition. -/
def heightChamberEuclidean (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    heightChamber n σ ≃ₜ (Fin n → ℝ) := by
  classical
  let witness := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_boundedHeightChamber n σ)
    (by simpa only [(isOpen_boundedHeightChamber n σ).interior_eq]
      using boundedHeightChamber_nonempty n σ)
    (isBounded_boundedHeightChamber n σ)
  let e := Classical.choose witness
  have he : e '' interior (boundedHeightChamber n σ) = ball 0 1 :=
    (Classical.choose_spec witness).1
  rw [(isOpen_boundedHeightChamber n σ).interior_eq] at he
  exact (boundHeightChamber n σ).trans
    ((e.image (boundedHeightChamber n σ)).trans
      ((Homeomorph.setCongr he).trans Homeomorph.unitBall.symm))

/-- One-point compactification of an actual minimal cell is a sphere of
the precise expected dimension d+n. -/
def verticalCellSphere (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    OnePoint (Space d × heightChamber n σ) ≃ₜ
      sphere (0 : Space (d+n+1)) 1 :=
  ((Homeomorph.refl (Space d)).prodCongr (heightChamberEuclidean n σ)).onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (by simp [Module.finrank_prod]))

end NRR.PrimePowerTopology
