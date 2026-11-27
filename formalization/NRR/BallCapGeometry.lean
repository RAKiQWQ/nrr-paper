import NRR.BrunnMinkowskiBodySlices
import NRR.BodyNormalization
import NRR.CenteredBackground
import NRR.CylinderLocalization
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Actual Euclidean three-dimensional ball caps, computed by horizontal
slicing.  The formulas here concern set volumes and set integrals. -/

noncomputable section
open Set MeasureTheory Metric
open scoped RealInnerProductSpace

namespace NRR.BallCapGeometry

abbrev Plane := Space 2
abbrev Three := Plane × ℝ

/-- The usual Euclidean unit ball in horizontal/vertical coordinates. -/
def unitBall : Set Three := {q | ‖q.1‖ ^ 2 + q.2 ^ 2 ≤ 1}

/-- The portion of the unit ball above height `s`. -/
def upperCap (s : ℝ) : Set Three := {q ∈ unitBall | s ≤ q.2}

/-- The portion of the unit ball below a horizontal cut. -/
def lowerCap (s : ℝ) : Set Three := {q ∈ unitBall | q.2 ≤ s}

private theorem unitBall_closed : IsClosed unitBall := by
  apply isClosed_le
  · exact continuous_fst.norm.pow 2 |>.add (continuous_snd.pow 2)
  · exact continuous_const

private theorem upperCap_compact (s : ℝ) : IsCompact (upperCap s) := by
  have hsub : upperCap s ⊆ closedBall (0 : Plane) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨u,z⟩ ⟨hball,hs⟩
    change ‖u‖ ^ 2 + z ^ 2 ≤ 1 at hball
    have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
    have hu : ‖u‖ ≤ 1 := by
      rw [← abs_of_nonneg (norm_nonneg u)]
      exact (sq_le_one_iff_abs_le_one ‖u‖).mp hu2
    have hz2 : z ^ 2 ≤ 1 := by nlinarith [sq_nonneg (‖u‖)]
    have hz : |z| ≤ 1 := (sq_le_one_iff_abs_le_one z).mp hz2
    exact ⟨mem_closedBall.mpr (by simpa using hu), abs_le.mp hz⟩
  apply ((isCompact_closedBall (0 : Plane) 1).prod isCompact_Icc).of_isClosed_subset
  · exact unitBall_closed.inter (isClosed_le continuous_const continuous_snd)
  · exact hsub

private theorem lowerCap_compact (s : ℝ) : IsCompact (lowerCap s) := by
  have hsub : lowerCap s ⊆ closedBall (0 : Plane) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨u,z⟩ ⟨hball,hs⟩
    change ‖u‖ ^ 2 + z ^ 2 ≤ 1 at hball
    have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
    have hu : ‖u‖ ≤ 1 := by
      rw [← abs_of_nonneg (norm_nonneg u)]
      exact (sq_le_one_iff_abs_le_one ‖u‖).mp hu2
    have hz2 : z ^ 2 ≤ 1 := by nlinarith [sq_nonneg (‖u‖)]
    have hz : |z| ≤ 1 := (sq_le_one_iff_abs_le_one z).mp hz2
    exact ⟨mem_closedBall.mpr (by simpa using hu), abs_le.mp hz⟩
  apply ((isCompact_closedBall (0 : Plane) 1).prod isCompact_Icc).of_isClosed_subset
  · exact unitBall_closed.inter (isClosed_le continuous_snd continuous_const)
  · exact hsub

private theorem fiber_upperCap_eq {s z : ℝ} (hs : -1 ≤ s) (hz : z ∈ Icc s 1) :
    NRR.ConvexSectionContinuity.fiber (upperCap s) z =
      closedBall (0 : Plane) (Real.sqrt (1-z^2)) := by
  ext u
  rw [NRR.ConvexSectionContinuity.fiber, mem_closedBall, dist_zero_right]
  have hzrange : z ∈ Icc (-1 : ℝ) 1 := ⟨le_trans hs hz.1,hz.2⟩
  have hsqrt : Real.sqrt (1-z^2) ^ 2 = 1-z^2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg z, hzrange.1, hzrange.2])
  change (‖u‖ ^ 2 + z ^ 2 ≤ 1 ∧ s ≤ z) ↔ ‖u‖ ≤ Real.sqrt (1-z^2)
  constructor
  · intro h
    have hnorm : ‖u‖ ^ 2 ≤ (Real.sqrt (1-z^2)) ^ 2 := by nlinarith [h.1, hsqrt]
    exact (sq_le_sq₀ (norm_nonneg u) (Real.sqrt_nonneg _)).mp hnorm
  · intro h
    have hnorm := (sq_le_sq₀ (norm_nonneg u) (Real.sqrt_nonneg _)).mpr h
    constructor
    · nlinarith [hsqrt]
    · exact hz.1

private theorem fiber_lowerCap_eq {s z : ℝ} (hs : s ≤ 1) (hz : z ∈ Icc (-1) s) :
    NRR.ConvexSectionContinuity.fiber (lowerCap s) z =
      closedBall (0 : Plane) (Real.sqrt (1-z^2)) := by
  ext u
  rw [NRR.ConvexSectionContinuity.fiber, mem_closedBall, dist_zero_right]
  have hsqrt : Real.sqrt (1-z^2) ^ 2 = 1-z^2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg z, hz.1, hz.2])
  change (‖u‖ ^ 2 + z ^ 2 ≤ 1 ∧ z ≤ s) ↔ ‖u‖ ≤ Real.sqrt (1-z^2)
  constructor
  · intro h
    have hnorm : ‖u‖ ^ 2 ≤ (Real.sqrt (1-z^2)) ^ 2 := by nlinarith [h.1, hsqrt]
    exact (sq_le_sq₀ (norm_nonneg u) (Real.sqrt_nonneg _)).mp hnorm
  · intro h
    have hnorm := (sq_le_sq₀ (norm_nonneg u) (Real.sqrt_nonneg _)).mpr h
    constructor
    · nlinarith [hsqrt]
    · exact hz.2

private theorem fiber_lowerCap_empty {s z : ℝ} (hz : z ∉ Icc (-1) s) :
    NRR.ConvexSectionContinuity.fiber (lowerCap s) z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  apply hz
  constructor
  · have hball : ‖u‖ ^ 2 + z ^ 2 ≤ 1 := hu.1
    have hsq : z^2 ≤ 1 := by nlinarith [hball]
    exact (abs_le.mp ((sq_le_one_iff_abs_le_one z).mp hsq)).1
  · exact hu.2

private theorem sectionMass_lowerCap {s : ℝ} (hs : s ≤ 1) (z : ℝ) :
    NRR.BrunnMinkowskiBodySlices.sectionMass (lowerCap s) z =
      (Icc (-1) s).indicator (fun z => Real.pi * (1-z^2)) z := by
  by_cases hz : z ∈ Icc (-1) s
  · rw [Set.indicator_of_mem hz, NRR.BrunnMinkowskiBodySlices.sectionMass,
      fiber_lowerCap_eq hs hz]
    have hnonneg : 0 ≤ 1-z^2 :=
      sub_nonneg.mpr ((sq_le_one_iff_abs_le_one z).2 (abs_le.mpr ⟨hz.1,hz.2.trans hs⟩))
    change ENNReal.toReal (volume (closedBall (0 : Plane) (Real.sqrt (1-z^2)))) = _
    simp [EuclideanSpace.volume_closedBall_fin_two, Real.sq_sqrt hnonneg,
      ENNReal.toReal_mul, Real.pi_pos.le] <;> ring
  · rw [Set.indicator_of_notMem hz, NRR.BrunnMinkowskiBodySlices.sectionMass]
    have hf := fiber_lowerCap_empty hz
    simp [hf]

private theorem integral_z_one_sub_sq {s : ℝ} (hs : -1 ≤ s) :
    (∫ z in Icc (-1) s, z*(1-z^2) ∂(volume : Measure ℝ)) =
      -((1-s^2)^2)/4 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
  have hderiv (x : ℝ) : HasDerivAt (fun x : ℝ => x^2/2-x^4/4) (x-x^3) x := by
    convert ((hasDerivAt_id x).pow 2 |>.div_const 2).sub
      ((hasDerivAt_id x).pow 4 |>.div_const 4) using 1 <;> norm_num <;> ring
  have hint : IntervalIntegrable (fun x : ℝ => x-x^3) (volume : Measure ℝ) (-1) s :=
    Continuous.intervalIntegrable (μ := (volume : Measure ℝ))
      (continuous_id.sub (continuous_id.pow 3)) (-1) s
  have heq : (fun x : ℝ => x*(1-x^2)) = (fun x => x-x^3) := by funext x; ring
  rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
  <;> ring

/-- The vertical first moment of an actual ball cap. The coefficient is
strictly negative away from the empty/full endpoint cuts. -/
theorem lowerCap_vertical_moment {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    (∫ q in lowerCap s, q.2 ∂volume) = -Real.pi * (1-s^2)^2/4 := by
  have hi : IntegrableOn (fun q : Three => q.2) (lowerCap s) volume :=
    continuous_snd.continuousOn.integrableOn_compact (lowerCap_compact s)
  rw [NRR.BrunnMinkowskiBodySlices.integral_snd (lowerCap_compact s) (fun z => z) hi]
  have hfun : (fun z =>
      NRR.BrunnMinkowskiBodySlices.sectionMass (lowerCap s) z • z) =
      (Icc (-1) s).indicator (fun z => Real.pi * (z*(1-z^2))) := by
    funext z
    rw [sectionMass_lowerCap hs' z]
    by_cases hz : z ∈ Icc (-1) s <;> simp [hz] <;> ring
  rw [hfun]
  rw [integral_indicator (measurableSet_Icc), integral_const_mul,
    integral_z_one_sub_sq hs]
  <;> ring

theorem lowerCap_vertical_moment_strict {s : ℝ} (hs : |s| < 1) :
    0 < Real.pi * (1-s^2)^2/4 := by
  have hs2 : s^2 < 1 := (sq_lt_one_iff_abs_lt_one s).2 hs
  have hpos : 0 < 1-s^2 := by linarith
  positivity

/-- A horizontal reflection fixes every horizontal disk section and negates
its first moment, so each actual horizontal cap has zero horizontal moment. -/
theorem lowerCap_horizontal_moment (s : ℝ) :
    (∫ q in lowerCap s, q.1 ∂volume) = 0 := by
  let e : Three ≃ₜ Three := (Homeomorph.neg Plane).prodCongr (Homeomorph.refl ℝ)
  have pre : (e : Three → Three) ⁻¹' lowerCap s = lowerCap s := by
    ext q
    simp [e, lowerCap, unitBall, norm_neg]
  have mp : MeasurePreserving (e : Three → Three) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure Plane)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  have mpr := mp.restrict_preimage (lowerCap_compact s).measurableSet
  rw [pre] at mpr
  have h := mpr.integral_comp e.measurableEmbedding (fun q : Three => q.1)
  change (∫ q in lowerCap s, (-q.1) ∂volume) =
      ∫ q in lowerCap s, q.1 ∂volume at h
  rw [integral_neg] at h
  have hadd : (∫ q in lowerCap s, q.1 ∂volume) +
      (∫ q in lowerCap s, q.1 ∂volume) = 0 := by
    exact (neg_eq_iff_add_eq_zero).mp h
  have hzero : (2 : ℝ) • (∫ q in lowerCap s, q.1 ∂volume) = 0 := by
    rw [two_smul]
    exact hadd
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- The full first moment of a horizontal halfspace cut of the unit ball is
aligned with its vertical normal, with a strict scalar coefficient. -/
theorem lowerCap_first_moment {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    (∫ q in lowerCap s, q ∂volume) =
      (0, -Real.pi * (1-s^2)^2/4) := by
  have hhor : IntegrableOn (fun q : Three => q.1) (lowerCap s) volume :=
    continuous_fst.continuousOn.integrableOn_compact (lowerCap_compact s)
  have hver : IntegrableOn (fun q : Three => q.2) (lowerCap s) volume :=
    continuous_snd.continuousOn.integrableOn_compact (lowerCap_compact s)
  have hm := (lowerCap_compact s).measurableSet
  have hind : (fun q : Three => (lowerCap s).indicator (fun x => x) q) =
      (fun q => ((lowerCap s).indicator (fun x : Three => x.1) q,
        (lowerCap s).indicator (fun x : Three => x.2) q)) := by
    funext q
    by_cases hq : q ∈ lowerCap s <;> simp [hq] <;> rfl
  have hp : (∫ q in lowerCap s, q ∂volume) =
      (∫ q in lowerCap s, q.1 ∂volume,
       ∫ q in lowerCap s, q.2 ∂volume) := by
    rw [← integral_indicator hm]
    rw [hind]
    rw [integral_pair (hhor.integrable_indicator hm)
      (hver.integrable_indicator hm)]
    rw [integral_indicator hm, integral_indicator hm]
  rw [hp, lowerCap_horizontal_moment, lowerCap_vertical_moment hs hs']

/-- The ball-cap first moment transforms covariantly under any volume
preserving Euclidean isometry. Thus it is a strictly negative multiple of
the outward normal to the cap, independently of its orientation. -/
theorem isometry_lowerCap_first_moment
    (e : Three ≃ₗᵢ[ℝ] Three) (he : MeasurePreserving e volume volume)
    {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    (∫ q in e ⁻¹' lowerCap s, q ∂volume) =
      e.symm (0, -Real.pi * (1-s^2)^2/4) := by
  have hpre : e ⁻¹' lowerCap s = e.symm '' lowerCap s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
  have hcompact : IsCompact (e ⁻¹' lowerCap s) := by
    rw [hpre]
    exact (lowerCap_compact s).image e.symm.continuous
  have hmp := he.restrict_preimage (lowerCap_compact s).measurableSet
  have hchange := hmp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun q : Three => q)
  have hpmeas : MeasurableSet (e ⁻¹' lowerCap s) :=
    e.continuous.measurable (lowerCap_compact s).measurableSet
  have hind : (fun q : Three => e.symm
      ((e ⁻¹' lowerCap s).indicator (fun q => e q) q)) =
      (e ⁻¹' lowerCap s).indicator id := by
    funext q
    by_cases hq : q ∈ e ⁻¹' lowerCap s <;> simp [hq]
  have hcomm := e.symm.toContinuousLinearEquiv.integral_comp_comm
    (μ := (volume : Measure Three))
    (fun q : Three => (e ⁻¹' lowerCap s).indicator (fun q => e q) q)
  change (∫ q : Three, e.symm
      ((e ⁻¹' lowerCap s).indicator (fun q => e q) q) ∂volume) = _ at hcomm
  rw [hind, integral_indicator hpmeas, integral_indicator hpmeas] at hcomm
  calc
    (∫ q in e ⁻¹' lowerCap s, q ∂volume) =
        e.symm (∫ q in e ⁻¹' lowerCap s, e q ∂volume) := by
          exact hcomm
    _ = e.symm (∫ q in lowerCap s, q ∂volume) := by
          exact congrArg e.symm hchange
    _ = e.symm (0, -Real.pi * (1-s^2)^2/4) := by
          rw [lowerCap_first_moment hs hs']

private theorem sectionMass_upperCap {s : ℝ} (hs : -1 ≤ s) (z : ℝ) :
    NRR.BrunnMinkowskiBodySlices.sectionMass (upperCap s) z =
      (Icc s 1).indicator (fun z => Real.pi * (1-z^2)) z := by
  by_cases hz : z ∈ Icc s 1
  · rw [Set.indicator_of_mem hz, NRR.BrunnMinkowskiBodySlices.sectionMass,
      fiber_upperCap_eq hs hz]
    have hzrange : z ∈ Icc (-1 : ℝ) 1 := ⟨le_trans hs hz.1,hz.2⟩
    have hnonneg : 0 ≤ 1-z^2 :=
      sub_nonneg.mpr ((sq_le_one_iff_abs_le_one z).2 (abs_le.mpr ⟨hzrange.1,hzrange.2⟩))
    change ENNReal.toReal (volume (closedBall (0 : Plane) (Real.sqrt (1-z^2)))) = _
    simp [EuclideanSpace.volume_closedBall_fin_two, Real.sq_sqrt hnonneg,
      ENNReal.toReal_mul, Real.pi_pos.le] <;> ring
  · rw [Set.indicator_of_notMem hz]
    rw [NRR.BrunnMinkowskiBodySlices.sectionMass]
    have hf : NRR.ConvexSectionContinuity.fiber (upperCap s) z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      apply hz
      constructor
      · have hball : ‖u‖ ^ 2 + z ^ 2 ≤ 1 := hu.1
        have hsq : z^2 ≤ 1 := by nlinarith [hball]
        exact hu.2
      · have hball : ‖u‖ ^ 2 + z ^ 2 ≤ 1 := hu.1
        have hsq : z^2 ≤ 1 := by nlinarith [hball]
        have hzle : z ≤ 1 := (abs_le.mp ((sq_le_one_iff_abs_le_one z).mp hsq)).2
        exact hzle
    simp [hf]

private theorem integral_one_sub_sq (s : ℝ) (hs : s ≤ 1) :
    (∫ z in Icc s 1, (1-z^2) ∂(volume : Measure ℝ)) = 2/3-s+s^3/3 := by
  rw [integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ))]
  rw [← intervalIntegral.integral_of_le hs]
  have hderiv (x : ℝ) : HasDerivAt (fun x : ℝ => x - x^3/3) (1-x^2) x := by
    convert (hasDerivAt_id x).sub ((hasDerivAt_id x).pow 3 |>.div_const 3) using 1 <;>
      norm_num <;> ring
  have hint : IntervalIntegrable (fun x : ℝ => 1-x^2) (volume : Measure ℝ) s 1 := by
    exact Continuous.intervalIntegrable (μ := (volume : Measure ℝ))
      (continuous_const.sub (continuous_id.pow 2)) s 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
  <;> ring

/-- The actual volume of a 3D unit-ball cap, obtained by integrating the
areas of its horizontal disk sections. -/
theorem volume_upperCap {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    volume.real (upperCap s) = Real.pi * (2/3-s+s^3/3) := by
  rw [← NRR.BrunnMinkowskiBodySlices.integral_sectionMass (upperCap_compact s)]
  rw [show (fun z => NRR.BrunnMinkowskiBodySlices.sectionMass (upperCap s) z) =
      (Icc s 1).indicator (fun z => Real.pi*(1-z^2)) from funext (sectionMass_upperCap hs)]
  rw [integral_indicator (measurableSet_Icc), integral_const_mul, integral_one_sub_sq s hs']

/-- Normalized 3D unit-ball cap volume. -/
theorem unitBall_upperCap_fraction {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    volume.real (upperCap s) =
      ((2-3*s+s^3)/4) * volume.real (unitBall) := by
  have hball : unitBall = upperCap (-1) := by
    ext q
    change (‖q.1‖ ^ 2 + q.2 ^ 2 ≤ 1) ↔
      (‖q.1‖ ^ 2 + q.2 ^ 2 ≤ 1 ∧ -1 ≤ q.2)
    constructor
    · intro h
      have hz : q.2^2 ≤ 1 := by nlinarith [h, sq_nonneg ‖q.1‖]
      have habs : |q.2| ≤ 1 := (sq_le_one_iff_abs_le_one q.2).mp hz
      exact ⟨h, (abs_le.mp habs).1⟩
    · intro h
      exact h.1
  rw [volume_upperCap hs hs', hball,
    volume_upperCap (by norm_num : (-1 : ℝ) ≤ -1) (by norm_num : (-1 : ℝ) ≤ 1)]
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

theorem cap_fraction_at_inv_sqrt_two :
    (2-3*(1/Real.sqrt 2)+(1/Real.sqrt 2)^3)/4 < 1/12 := by
  have hs : Real.sqrt 2 > 0 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsmall : Real.sqrt 2 < 3/2 := by
    by_contra! h
    nlinarith [sq_nonneg (Real.sqrt 2 - 3/2)]
  have hs3 : (1/Real.sqrt 2)^3 = 1/(2*Real.sqrt 2) := by
    field_simp
    nlinarith [hs2]
  rw [hs3]
  field_simp
  nlinarith [hs, hs2, hsmall]

theorem volume_unitBall : volume.real unitBall = Real.pi * (4/3) := by
  have hball : unitBall = upperCap (-1) := by
    ext q
    change (‖q.1‖ ^ 2 + q.2 ^ 2 ≤ 1) ↔
      (‖q.1‖ ^ 2 + q.2 ^ 2 ≤ 1 ∧ -1 ≤ q.2)
    constructor
    · intro h
      have hz2 : q.2^2 ≤ 1 := by nlinarith [h, sq_nonneg ‖q.1‖]
      have habs : |q.2| ≤ 1 := (sq_le_one_iff_abs_le_one q.2).mp hz2
      exact ⟨h, (abs_le.mp habs).1⟩
    · exact And.left
  rw [hball]
  convert volume_upperCap (s := -1) (by norm_num) (by norm_num) using 1 <;> ring

private def planeCoordinates : Plane ≃ᵐ ℝ × ℝ :=
  (EuclideanSpace.measurableEquiv (Fin 2)).trans MeasurableEquiv.finTwoArrow

private theorem planeCoordinates_measurePreserving :
    MeasurePreserving planeCoordinates volume volume :=
  (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)).trans
    (MeasureTheory.volume_preserving_finTwoArrow ℝ)

private def threeCoordinates : Three ≃ᵐ ℝ × ℝ × ℝ :=
  (planeCoordinates.prodCongr (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc

private theorem threeCoordinates_measurePreserving :
    MeasurePreserving threeCoordinates volume volume := by
  exact MeasureTheory.volume_preserving_prodAssoc.comp
    (planeCoordinates_measurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ)))

private def realTripleSwap : ℝ × ℝ × ℝ ≃ᵐ ℝ × ℝ × ℝ :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))).trans
      (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ × ℝ)) |>.trans
        MeasurableEquiv.prodAssoc

private theorem realTripleSwap_measurePreserving :
    MeasurePreserving realTripleSwap volume volume := by
  let h₂ : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))) volume volume := by
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)))
  have h₃ : MeasurePreserving (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ × ℝ))
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))
        ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)))
  exact MeasureTheory.volume_preserving_prodAssoc.comp (h₃.comp h₂)

private def axisSwap : Three ≃ᵐ Three :=
  threeCoordinates.trans (realTripleSwap.trans threeCoordinates.symm)

private theorem axisSwap_measurePreserving : MeasurePreserving axisSwap volume volume :=
  (MeasurePreserving.symm threeCoordinates threeCoordinates_measurePreserving).comp
    (realTripleSwap_measurePreserving.comp threeCoordinates_measurePreserving)

end NRR.BallCapGeometry
