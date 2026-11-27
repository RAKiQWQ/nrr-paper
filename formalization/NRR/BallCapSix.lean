import NRR.BallCapGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Convex.Measure
import NRR.Partitions

/-! The direct uniform three-dimensional six-block check in §2 of the
manuscript. All balls and arbitrary-normal halfspaces below live in the
genuine Euclidean `Space 3`. The split-coordinate map is proved to preserve
both the sum-of-squares ball condition and actual Lebesgue volume.

The fixed cylinder lies in the unit ball and contains the concentric
ball of radius `1 / sqrt 2`. Convex sets of at least one sixth of the
unit-ball volume have positive volume inside the cylinder interior.
The five interior horizontal sixth-quantiles lie strictly between its ends.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped RealInnerProductSpace ENNReal

namespace NRR.BallCapSix

abbrev EuclideanThree := Space 3
abbrev SplitThree := BallCapGeometry.Three

def coordinates : EuclideanThree ≃L[ℝ] SplitThree :=
  Coordinates.horizontalHeight 2

@[simp] theorem coordinates_height (x : EuclideanThree) : (coordinates x).2 = x 2 := rfl
@[simp] theorem coordinates_horizontal (x : EuclideanThree) (i : Fin 2) :
    (coordinates x).1 i = x i.castSucc := rfl

/-- The horizontal-height change of coordinates preserves Lebesgue volume,
even though its target is equipped with the supremum product norm. -/
theorem coordinates_measurePreserving : MeasurePreserving coordinates volume volume := by
  have hsplit := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have hswap : MeasurePreserving Prod.swap
      (volume : Measure (ℝ × (Fin 2 → ℝ)))
      (volume : Measure ((Fin 2 → ℝ) × ℝ)) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        ((volume : Measure ℝ).prod volume) ((volume : Measure (Fin 2 → ℝ)).prod volume))
  have hto := (PiLp.volume_preserving_toLp (ι := Fin 2)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  convert hto.comp (hswap.comp (hsplit.comp (PiLp.volume_preserving_ofLp (ι := Fin 3)))) using 1
  funext x
  apply Prod.ext
  · ext i
    change x i.castSucc = x ((2 : Fin 3).succAbove i)
    congr 1
    exact (congrFun Fin.succAbove_last i).symm
  · rfl

theorem coordinates_norm_sq (x : EuclideanThree) :
    ‖(coordinates x).1‖ ^ 2 + (coordinates x).2 ^ 2 = ‖x‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs]
  ring

def unitBall : Set EuclideanThree := closedBall 0 1

def cap (v : EuclideanThree) (s : ℝ) : Set EuclideanThree :=
  {x ∈ unitBall | s ≤ ⟪v,x⟫}

theorem coordinates_preimage_unitBall :
    coordinates ⁻¹' BallCapGeometry.unitBall = unitBall := by
  ext x
  change (‖(coordinates x).1‖ ^ 2 + (coordinates x).2 ^ 2 ≤ 1) ↔ x ∈ closedBall 0 1
  rw [coordinates_norm_sq, mem_closedBall, dist_zero_right]
  rw [sq_le_one_iff_abs_le_one, abs_of_nonneg (norm_nonneg x)]

def vertical : EuclideanThree := EuclideanSpace.single 2 1

@[simp] theorem norm_vertical : ‖vertical‖ = 1 := by simp [vertical]

@[simp] theorem inner_vertical (x : EuclideanThree) : ⟪vertical,x⟫ = x 2 := by
  simp [vertical, EuclideanSpace.inner_single_left]

theorem coordinates_preimage_upperCap (s : ℝ) :
    coordinates ⁻¹' BallCapGeometry.upperCap s = cap vertical s := by
  ext x
  change (coordinates x ∈ BallCapGeometry.unitBall ∧ s ≤ (coordinates x).2) ↔ _
  rw [show coordinates x ∈ BallCapGeometry.unitBall ↔ x ∈ unitBall from
    Set.ext_iff.mp coordinates_preimage_unitBall x]
  simp [cap]

theorem volume_unitBall : volume.real unitBall = Real.pi * (4/3) := by
  have hmeas : MeasurableSet BallCapGeometry.unitBall := by
    apply IsClosed.measurableSet
    exact isClosed_le (continuous_fst.norm.pow 2 |>.add (continuous_snd.pow 2)) continuous_const
  have h := coordinates_measurePreserving.measure_preimage hmeas.nullMeasurableSet
  rw [coordinates_preimage_unitBall] at h
  exact (congrArg ENNReal.toReal h).trans BallCapGeometry.volume_unitBall

theorem cap_vertical_fraction {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    volume.real (cap vertical s) = ((2-3*s+s^3)/4) * volume.real unitBall := by
  have hmeas : MeasurableSet (BallCapGeometry.upperCap s) := by
    apply IsClosed.measurableSet
    exact (isClosed_le (continuous_fst.norm.pow 2 |>.add (continuous_snd.pow 2))
      continuous_const).inter (isClosed_le continuous_const continuous_snd)
  have h := coordinates_measurePreserving.measure_preimage hmeas.nullMeasurableSet
  rw [coordinates_preimage_upperCap] at h
  rw [show volume.real (cap vertical s) = volume.real (BallCapGeometry.upperCap s) from
    congrArg ENNReal.toReal h, BallCapGeometry.unitBall_upperCap_fraction hs hs',
    BallCapGeometry.volume_unitBall, volume_unitBall]

/-- Reflect a unit normal to the vertical unit vector in the genuine
Euclidean metric, before using the split-coordinate cap computation. -/
theorem cap_fraction (v : EuclideanThree) (hv : ‖v‖ = 1)
    {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    volume.real (cap v s) = ((2-3*s+s^3)/4) * volume.real unitBall := by
  let e := (ℝ ∙ (v - vertical))ᗮ.reflection
  have he : e v = vertical := Submodule.reflection_sub (hv.trans norm_vertical.symm)
  have hpre : e ⁻¹' cap vertical s = cap v s := by
    ext x
    have hi : ⟪vertical,e x⟫ = ⟪v,x⟫ := by rw [← he, e.inner_map_map]
    simp only [mem_preimage, cap, mem_setOf_eq, unitBall, mem_closedBall,
      dist_zero_right, e.norm_map, hi]
  have hm : MeasurableSet (cap vertical s) :=
    isClosed_closedBall.measurableSet.inter
      (isClosed_le continuous_const
        (continuous_const.inner (𝕜 := ℝ) continuous_id)).measurableSet
  have h := e.measurePreserving.measure_preimage hm.nullMeasurableSet
  rw [hpre] at h
  exact (congrArg ENNReal.toReal h).trans (cap_vertical_fraction hs hs')

/-- The same formula for a halfspace written with any nonzero normal.
Its signed Euclidean distance from the origin is `t / ‖v‖`. -/
theorem halfspace_cap_fraction (v : EuclideanThree) (hv : v ≠ 0) (t : ℝ)
    (ht : -1 ≤ t / ‖v‖) (ht' : t / ‖v‖ ≤ 1) :
    volume.real {x ∈ unitBall | t ≤ ⟪v,x⟫} =
      ((2-3*(t/‖v‖)+(t/‖v‖)^3)/4) * volume.real unitBall := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hn : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, hpos.ne']
  have hset : {x ∈ unitBall | t ≤ ⟪v,x⟫} = cap (‖v‖⁻¹ • v) (t/‖v‖) := by
    ext x
    simp only [cap, mem_setOf_eq, real_inner_smul_left]
    rw [mul_comm ‖v‖⁻¹, ← div_eq_mul_inv, div_le_div_iff_of_pos_right hpos]
  rw [hset]
  exact cap_fraction _ hn ht ht'

def radius : ℝ := 1 / Real.sqrt 2

theorem radius_pos : 0 < radius := by unfold radius; positivity

theorem radius_sq : radius ^ 2 = 1/2 := by
  unfold radius
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem radius_lt_one : radius < 1 := by
  nlinarith [radius_sq, radius_pos]

/-- The closed cylinder of radius and half-height `1 / sqrt 2`. -/
def cylinder : Set EuclideanThree :=
  coordinates ⁻¹' Localization.solidCylinder radius radius

theorem isClosed_cylinder : IsClosed cylinder :=
  (isClosed_closedBall.prod isClosed_Icc).preimage coordinates.continuous

theorem interior_cylinder : interior cylinder =
    coordinates ⁻¹' (ball 0 radius ×ˢ Ioo (-radius) radius) := by
  change interior (coordinates.toHomeomorph ⁻¹' _) = _
  rw [← coordinates.toHomeomorph.preimage_interior,
    Localization.interior_solidCylinder radius_pos]
  rfl

theorem cylinder_subset_unitBall : cylinder ⊆ unitBall := by
  intro x hx
  have hx' : ‖(coordinates x).1‖ ≤ radius ∧
      -radius ≤ (coordinates x).2 ∧ (coordinates x).2 ≤ radius := by
    simpa [cylinder, Localization.solidCylinder, mem_closedBall, dist_zero_right] using hx
  have hhor := (sq_le_sq₀ (norm_nonneg (coordinates x).1) radius_pos.le).mpr hx'.1
  have hver := (sq_le_sq₀ (abs_nonneg (coordinates x).2) radius_pos.le).mpr
    (abs_le.mpr hx'.2)
  rw [sq_abs] at hver
  have hsq : ‖x‖^2 ≤ 1 := by
    rw [← coordinates_norm_sq]
    nlinarith [radius_sq]
  change x ∈ closedBall 0 1
  rw [mem_closedBall, dist_zero_right]
  exact (le_abs_self ‖x‖).trans ((sq_le_one_iff_abs_le_one ‖x‖).mp hsq)

theorem ball_subset_interior_cylinder : ball (0 : EuclideanThree) radius ⊆ interior cylinder := by
  intro x hx
  rw [mem_ball, dist_zero_right] at hx
  rw [interior_cylinder]
  simp only [mem_preimage, mem_prod, mem_ball, dist_zero_right]
  have hs := coordinates_norm_sq x
  have hx2 : ‖x‖^2 < radius^2 := (sq_lt_sq₀ (norm_nonneg x) radius_pos.le).mpr hx
  have hh : ‖(coordinates x).1‖ < radius := by
    nlinarith [sq_nonneg (coordinates x).2, norm_nonneg (coordinates x).1, radius_pos]
  have hz : |(coordinates x).2| < radius := by
    apply (sq_lt_sq₀ (abs_nonneg _) radius_pos.le).mp
    rw [sq_abs]
    nlinarith [sq_nonneg ‖(coordinates x).1‖]
  exact ⟨hh, abs_lt.mp hz⟩

theorem closedBall_subset_cylinder : closedBall (0 : EuclideanThree) radius ⊆ cylinder := by
  rw [← closure_ball (0 : EuclideanThree) radius_pos.ne']
  exact closure_minimal (ball_subset_interior_cylinder.trans interior_subset) isClosed_cylinder

/-- Weak separation from the inner Euclidean ball places the whole convex
set in a unit-normal halfspace whose distance from the origin is at least
the inner radius.  There is no separation hypothesis in the volume result
below: this lemma supplies it from geometric disjointness. -/
theorem subset_cap_of_avoids_ball {C : Set EuclideanThree}
    (hC : Convex ℝ C) (hne : C.Nonempty) (hCB : C ⊆ unitBall)
    (avoids : Disjoint (ball (0 : EuclideanThree) radius) C) :
    ∃ v : EuclideanThree, ‖v‖ = 1 ∧ C ⊆ cap v radius := by
  obtain ⟨F,c,hA,hS⟩ := geometric_hahn_banach_open
    (convex_ball (0 : EuclideanThree) radius) isOpen_ball hC avoids
  have hF : F ≠ 0 := by
    intro hz
    obtain ⟨x,hx⟩ := hne
    have ha := hA 0 (mem_ball_self radius_pos)
    have hs := hS x hx
    simp [hz] at ha hs
    linarith
  let v : EuclideanThree := (InnerProductSpace.toDual ℝ EuclideanThree).symm F
  have hv (x : EuclideanThree) : ⟪v,x⟫ = F x := InnerProductSpace.toDual_symm_apply
  have hvne : v ≠ 0 := by
    intro hz
    apply hF
    ext x
    rw [← hv x, hz, inner_zero_left]
    rfl
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  let n : EuclideanThree := ‖v‖⁻¹ • v
  have hn : ‖n‖ = 1 := by simp [n, norm_smul, hvpos.ne']
  have hclosed : ∀ x ∈ closedBall (0 : EuclideanThree) radius, F x ≤ c := by
    intro x hx
    apply closure_minimal (fun y hy => (hA y hy).le)
      (isClosed_le F.continuous continuous_const)
    rwa [closure_ball (0 : EuclideanThree) radius_pos.ne']
  have hc : radius * ‖v‖ ≤ c := by
    have hmem : radius • n ∈ closedBall (0 : EuclideanThree) radius := by
      simp [mem_closedBall, dist_zero_right, norm_smul, hn, abs_of_pos radius_pos]
    have H := hclosed _ hmem
    rw [← hv, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at H
    have he : radius * (‖v‖⁻¹ * ‖v‖^2) = radius * ‖v‖ := by
      field_simp
    nlinarith [he]
  refine ⟨n,hn,fun x hx => ⟨hCB hx, ?_⟩⟩
  change radius ≤ ⟪‖v‖⁻¹ • v,x⟫
  rw [real_inner_smul_left, hv]
  have H := hc.trans (hS x hx)
  exact (le_inv_mul_iff₀ hvpos).mpr (by simpa [mul_comm] using H)

theorem cap_volume_lt_sixth (v : EuclideanThree) (hv : ‖v‖ = 1) :
    volume.real (cap v radius) < volume.real unitBall / 6 := by
  rw [cap_fraction v hv (by linarith [radius_pos]) radius_lt_one.le]
  have hfrac : (2-3*radius+radius^3)/4 < 1/6 :=
    lt_trans BallCapGeometry.cap_fraction_at_inv_sqrt_two (by norm_num)
  have hball : 0 < volume.real unitBall := by rw [volume_unitBall]; positivity
  nlinarith

/-- Every convex subset of the genuine Euclidean unit ball with at least
one sixth of its volume meets the interior of the fixed cylinder. -/
theorem sixth_meets_interior {C : Set EuclideanThree} (hC : Convex ℝ C)
    (hCB : C ⊆ unitBall) (hmass : volume.real unitBall / 6 ≤ volume.real C) :
    (C ∩ interior cylinder).Nonempty := by
  have hmasspos : 0 < volume.real C := by
    have hb : 0 < volume.real unitBall := by rw [volume_unitBall]; positivity
    linarith
  by_contra hn
  have hd : Disjoint (ball (0 : EuclideanThree) radius) C := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    exact hn ⟨x,hxc,ball_subset_interior_cylinder hx⟩
  obtain ⟨v,hv,hsub⟩ := subset_cap_of_avoids_ball hC
    (nonempty_of_measureReal_ne_zero hmasspos.ne') hCB hd
  have hf : volume (cap v radius) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono (fun _ hx => hx.1))
      (isCompact_closedBall (0 : EuclideanThree) 1).measure_lt_top)
  have hle := measureReal_mono hsub hf
  have hlt := cap_volume_lt_sixth v hv
  linarith

/-- In fact the cylinder-interior intersection has strictly positive
ordinary Lebesgue volume. -/
theorem sixth_positive_volume_inter_interior {C : Set EuclideanThree}
    (hC : Convex ℝ C) (hCB : C ⊆ unitBall)
    (hmass : volume.real unitBall / 6 ≤ volume.real C) :
    0 < volume.real (C ∩ interior cylinder) := by
  have hint : volume.real (interior C) = volume.real C :=
    congrArg ENNReal.toReal (measure_interior_of_null_frontier (hC.addHaar_frontier volume))
  obtain ⟨x,hx,hxc⟩ := sixth_meets_interior hC.interior (interior_subset.trans hCB)
    (by rwa [hint])
  have hopen : IsOpen (interior C ∩ interior cylinder) := isOpen_interior.inter isOpen_interior
  have hp : 0 < volume (interior C ∩ interior cylinder) := hopen.measure_pos volume ⟨x,hx,hxc⟩
  have hp' : 0 < volume (C ∩ interior cylinder) :=
    lt_of_lt_of_le hp (measure_mono (inter_subset_inter_left _ interior_subset))
  have hf : volume (C ∩ interior cylinder) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono (inter_subset_left.trans hCB))
      (isCompact_closedBall (0 : EuclideanThree) 1).measure_lt_top)
  exact ENNReal.toReal_pos hp'.ne' hf

theorem sixth_positive_volume_inter {C : Set EuclideanThree}
    (hC : Convex ℝ C) (hCB : C ⊆ unitBall)
    (hmass : volume.real unitBall / 6 ≤ volume.real C) :
    0 < volume.real (C ∩ cylinder) := by
  apply lt_of_lt_of_le (sixth_positive_volume_inter_interior hC hCB hmass)
  exact measureReal_mono (inter_subset_inter_right C interior_subset)
    (ne_of_lt (lt_of_le_of_lt (measure_mono (inter_subset_left.trans hCB))
      (isCompact_closedBall (0 : EuclideanThree) 1).measure_lt_top))

/-- The positive intersection statement in the horizontal-height
coordinates used by the cylinder rigidity theorems. -/
theorem split_sixth_positive_volume {C : Set SplitThree} (hC : Convex ℝ C)
    (hCB : C ⊆ BallCapGeometry.unitBall)
    (hmass : volume.real BallCapGeometry.unitBall / 6 ≤ volume.real C) :
    0 < volume.real (C ∩ interior (Localization.solidCylinder radius radius)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure SplitThree) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hpreC := coordinates_measurePreserving.measure_preimage (hC.nullMeasurableSet volume)
  have hcvol : volume.real (coordinates ⁻¹' C) = volume.real C := congrArg ENNReal.toReal hpreC
  have hbvol : volume.real unitBall = volume.real BallCapGeometry.unitBall := by
    rw [volume_unitBall, BallCapGeometry.volume_unitBall]
  have hsub : coordinates ⁻¹' C ⊆ unitBall := by
    rw [← coordinates_preimage_unitBall]
    exact preimage_mono hCB
  have hconv : Convex ℝ (coordinates ⁻¹' C) := hC.linear_preimage coordinates.toLinearMap
  have hp := sixth_positive_volume_inter_interior hconv hsub (by rwa [hcvol,hbvol])
  have hpre : coordinates ⁻¹' (C ∩ interior (Localization.solidCylinder radius radius)) =
      (coordinates ⁻¹' C) ∩ interior cylinder := by
    rw [preimage_inter]
    congr 1
    exact coordinates.toHomeomorph.preimage_interior _
  have hm : NullMeasurableSet
      (C ∩ interior (Localization.solidCylinder (d := 2) radius radius)) volume :=
    (hC.nullMeasurableSet volume).inter isOpen_interior.measurableSet.nullMeasurableSet
  have hvol := coordinates_measurePreserving.measure_preimage hm
  rw [hpre] at hvol
  rwa [show volume.real ((coordinates ⁻¹' C) ∩ interior cylinder) =
    volume.real (C ∩ interior (Localization.solidCylinder radius radius)) from
      congrArg ENNReal.toReal hvol] at hp

/-- The displayed coefficient in the manuscript, with the radical
simplification checked in the field of real numbers. -/
theorem cap_fraction_at_radius :
    (2-3*radius+radius^3)/4 = 1/2 - 5/(8*Real.sqrt 2) := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold radius
  field_simp
  nlinarith [hs]

theorem manuscript_cap_bound : 1/2 - 5/(8*Real.sqrt 2) < (1 : ℝ)/6 := by
  rw [← cap_fraction_at_radius]
  exact lt_trans BallCapGeometry.cap_fraction_at_inv_sqrt_two (by norm_num)

def lowerSlice (s : ℝ) : Set EuclideanThree := {x ∈ unitBall | x 2 ≤ s}

theorem lowerSlice_eq_cap (s : ℝ) : lowerSlice s = cap (-vertical) (-s) := by
  ext x
  simp [lowerSlice, cap]

theorem lowerSlice_mono {s t : ℝ} (hst : s ≤ t) : lowerSlice s ⊆ lowerSlice t := by
  intro x hx
  exact ⟨hx.1,hx.2.trans hst⟩

theorem lowerSlice_finite (s : ℝ) : volume (lowerSlice s) ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono (fun _ hx => hx.1))
    (isCompact_closedBall (0 : EuclideanThree) 1).measure_lt_top)

theorem lowerSlice_fraction {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    volume.real (lowerSlice s) = ((2+3*s-s^3)/4) * volume.real unitBall := by
  rw [lowerSlice_eq_cap, cap_fraction (-vertical) (by simp) (by linarith) (by linarith)]
  ring

/-- Every nontrivial sixth-quantile has height strictly between the two
cylinder ends.  The hypotheses here are actual horizontal sublevel
volumes, with no assumed location of the quantile. -/
theorem horizontal_quantile_between_ends {s : ℝ}
    (hl : volume.real unitBall / 6 ≤ volume.real (lowerSlice s))
    (hu : volume.real (lowerSlice s) ≤ 5 * volume.real unitBall / 6) :
    -radius < s ∧ s < radius := by
  have hsmall : volume.real (lowerSlice (-radius)) < volume.real unitBall / 6 := by
    rw [lowerSlice_eq_cap]
    simpa using cap_volume_lt_sixth (-vertical) (by simp)
  have hlarge : 5 * volume.real unitBall / 6 < volume.real (lowerSlice radius) := by
    have hsmall' := cap_volume_lt_sixth vertical norm_vertical
    rw [lowerSlice_fraction (by linarith [radius_pos]) radius_lt_one.le]
    rw [cap_fraction vertical norm_vertical (by linarith [radius_pos]) radius_lt_one.le] at hsmall'
    nlinarith
  constructor
  · by_contra! h
    have hle := measureReal_mono (lowerSlice_mono h) (lowerSlice_finite (-radius))
    linarith
  · by_contra! h
    have hle := measureReal_mono (lowerSlice_mono h) (lowerSlice_finite s)
    linarith

theorem horizontal_sixth_quantile {i : ℕ} (hi : 1 ≤ i) (hi' : i ≤ 5) {s : ℝ}
    (hs : volume.real (lowerSlice s) = (i : ℝ) / 6 * volume.real unitBall) :
    -radius < s ∧ s < radius := by
  have hb : 0 ≤ volume.real unitBall := ENNReal.toReal_nonneg
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hiR' : (i : ℝ) ≤ 5 := by exact_mod_cast hi'
  apply horizontal_quantile_between_ends <;> rw [hs] <;> nlinarith

/-- The actual unit ball, as a full-dimensional compact convex body. -/
def ballBody : Body 3 :=
  ⟨{ carrier := unitBall
     isCompact' := isCompact_closedBall (0 : EuclideanThree) 1
     nonempty' := ⟨0, by simp [unitBall]⟩ },
    convex_closedBall (0 : EuclideanThree) 1, by
      change (interior (closedBall (0 : EuclideanThree) 1)).Nonempty
      rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact ⟨0, mem_ball_self (by norm_num)⟩⟩

@[simp] theorem ballBody_points : ballBody.points = unitBall := rfl

/-- Direct application to every block of every genuine uniform six-part
convex partition of the three-dimensional Euclidean ball. -/
theorem six_partition_positive_volume {S : Fin 6 → Body 3}
    (hp : BodyPartition ballBody S) (hm : EqualMass volume S) (i : Fin 6) :
    0 < volume.real ((S i).points ∩ interior cylinder) := by
  apply sixth_positive_volume_inter_interior (S i).property.1
  · intro x hx
    rw [← ballBody_points, ← hp.covers]
    exact mem_iUnion.mpr ⟨i,hx⟩
  · have hmass := hp.mass_eq_div (Measure.AbsolutelyContinuous.rfl) hm i
    have hreal := congrArg ENNReal.toReal hmass
    simpa [ENNReal.toReal_div] using hreal.symm.le

end NRR.BallCapSix
