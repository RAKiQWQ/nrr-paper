import NRR.PrimePowerTopologyConvexHomology
import NRR.TopologyPort.RelativeSingularPrism

/-! The genuine radial deformation retract of a punctured normed vector
space onto a positive-radius sphere, and its action on singular homology. -/

noncomputable section
open Set Topology Metric CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

section Radial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sphere_val_ne_zero {r : ℝ} (hr : 0 < r) (v : sphere (0 : E) r) : v.val ≠ 0 := by
  intro hv
  have hn := mem_sphere_zero_iff_norm.mp v.property
  rw [hv,norm_zero] at hn
  exact hr.ne' hn.symm

def spherePuncturedIncl {r : ℝ} (hr : 0 < r) : C(sphere (0 : E) r,{v : E // v ≠ 0}) where
  toFun v := ⟨v.val,sphere_val_ne_zero hr v⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def radialProjection {r : ℝ} (hr : 0 < r) : C({v : E // v ≠ 0},sphere (0 : E) r) where
  toFun v := ⟨(r/‖v.val‖) • v.val,by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,
      abs_of_pos (div_pos hr (norm_pos_iff.mpr v.property)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr v.property)]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.div (continuous_norm.comp continuous_subtype_val)
      (fun v => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val

@[simp] theorem radialProjection_inclusion {r : ℝ} (hr : 0 < r)
    (v : sphere (0 : E) r) : radialProjection hr (spherePuncturedIncl hr v) = v := by
  apply Subtype.ext
  change (r/‖v.val‖) • v.val = v.val
  rw [mem_sphere_zero_iff_norm.mp v.property,div_self hr.ne',one_smul]

private theorem radialCoefficient_pos (t : unitInterval) {a : ℝ} (ha : 0 < a) :
    0 < (1-(t : ℝ))*a+(t : ℝ) := by
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht,sub_zero,one_mul,add_zero] using ha
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) ha.le)
      (lt_of_le_of_ne t.property.1 (Ne.symm ht))

def radialDeformation {r : ℝ} (hr : 0 < r) :
    ((spherePuncturedIncl (E := E) hr).comp (radialProjection hr)).Homotopy
      (ContinuousMap.id {v : E // v ≠ 0}) where
  toFun p := ⟨((1-(p.1 : ℝ))*(r/‖p.2.val‖)+(p.1 : ℝ)) • p.2.val,
    smul_ne_zero (radialCoefficient_pos p.1
      (div_pos hr (norm_pos_iff.mpr p.2.property))).ne' p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have ht : Continuous (fun p : unitInterval × {v : E // v ≠ 0} => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hv : Continuous (fun p : unitInterval × {v : E // v ≠ 0} => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact (((continuous_const.sub ht).mul
      (continuous_const.div hv.norm (fun p => norm_ne_zero_iff.mpr p.2.property))).add ht).smul hv
  map_zero_left v := by
    apply Subtype.ext
    change ((1-0)*(r/‖v.val‖)+0) • v.val = (r/‖v.val‖) • v.val
    simp
  map_one_left v := by apply Subtype.ext; simp

def spherePuncturedHomotopyEquiv {r : ℝ} (hr : 0 < r) :
    ContinuousMap.HomotopyEquiv (sphere (0 : E) r) {v : E // v ≠ 0} where
  toFun := spherePuncturedIncl hr
  invFun := radialProjection hr
  left_inv := by
    have eq : (radialProjection hr).comp (spherePuncturedIncl (E := E) hr) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro v
      exact radialProjection_inclusion hr v
    rw [eq]
  right_inv := ⟨radialDeformation hr⟩

theorem isIso_HabsMap_spherePuncturedIncl (R : Type) [Ring R] (k : ℕ)
    {r : ℝ} (hr : 0 < r) :
    IsIso (HabsMap R k (TopCat.ofHom (spherePuncturedIncl (E := E) hr))) := by
  change IsIso (HabsIsoOfHomotopyEquiv R k (spherePuncturedHomotopyEquiv hr)).hom
  infer_instance

end Radial

set_option maxHeartbeats 800000 in
theorem isIso_standardNormalSphereNonzero (R : Type) [Ring R] (d n k : ℕ) [NeZero n]
    {r : ℝ} (hr : 0 < r) :
    IsIso (HabsMap R k (standardNormalSphereNonzero (d := d) (n := n) hr)) :=
  isIso_HabsMap_spherePuncturedIncl R k hr

set_option maxHeartbeats 800000 in
/-- The standard normal disk represents precisely the local homology of
the vector space at zero: its map to the punctured-vector pair is an
isomorphism in every degree at least two. -/
theorem isIso_standardNormalDiskRelative (R : Type) [Ring R]
    (d n k : ℕ) [NeZero n] {r : ℝ} (hr : 0 < r) :
    IsIso (standardNormalDiskRelative (d := d) (n := n) R (k+2) hr) := by
  let i := normalBoundaryIncl d n r
  let j := subIncl (Y := TopCat.of (ReducedValues (d+1) n)) (reducedNonzeroSet d n)
  letI : IsIso (relδ R (k+1) i) := isIso_normalDisk_relδ R d n k r hr.le
  letI : IsIso (relδ R (k+1) j) :=
    isIso_relδ_of_contractible R (k+1) (by omega) j
  letI : IsIso (HabsMap R (k+1) (standardNormalSphereNonzero (d := d) (n := n) hr)) :=
    isIso_standardNormalSphereNonzero R d n (k+1) hr
  have naturality := relδ_naturality R (k+1) i j
    (standardNormalDisk_pair_comm (d := d) (n := n) hr)
  letI : IsIso (standardNormalDiskRelative (d := d) (n := n) R (k+2) hr ≫
      relδ R (k+1) j) := by
    change IsIso (HrelMap R (k+1+1) i j
      (standardNormalDisk_pair_comm (d := d) (n := n) hr) ≫ relδ R (k+1) j)
    rw [← naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (relδ R (k+1) j)

end NRR.PrimePowerTopology
