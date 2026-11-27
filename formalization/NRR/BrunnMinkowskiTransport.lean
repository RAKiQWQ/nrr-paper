import NRR.BrunnMinkowskiSlices
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual monotone cumulative-mass transport between positive interval
densities. The density need only be continuous and positive in the open
support interval; it may vanish at the endpoints. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiTransport

structure PositiveDensity (a b : ℝ) where
  density : ℝ → ℝ
  proper : a < b
  integrable : IntervalIntegrable density volume a b
  positive : ∀ x ∈ Ioo a b, 0 < density x
  continuous : ContinuousOn density (Ioo a b)

namespace PositiveDensity

variable {a b : ℝ} (D : PositiveDensity a b)

def cumulative (x : ℝ) : ℝ := ∫ t in a..x, D.density t

def mass : ℝ := ∫ t in a..b, D.density t

@[simp] theorem cumulative_left : D.cumulative a = 0 := by simp [cumulative]
@[simp] theorem cumulative_right : D.cumulative b = D.mass := rfl

theorem mass_pos : 0 < D.mass :=
  intervalIntegral.intervalIntegral_pos_of_pos_on D.integrable D.positive D.proper

theorem strictMonoOn_cumulative : StrictMonoOn D.cumulative (Icc a b) := by
  intro x hx y hy hxy
  have intAX : IntervalIntegrable D.density volume a x :=
    D.integrable.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le D.proper.le]
      exact Icc_subset_Icc le_rfl hx.2)
  have intXY : IntervalIntegrable D.density volume x y :=
    D.integrable.mono_set (by
      rw [uIcc_of_le hxy.le, uIcc_of_le D.proper.le]
      exact Icc_subset_Icc hx.1 hy.2)
  have positive := intervalIntegral.intervalIntegral_pos_of_pos_on intXY
    (fun z hz => D.positive z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩) hxy
  have adjacent := intervalIntegral.integral_add_adjacent_intervals intAX intXY
  change D.cumulative x + (∫ t in x..y, D.density t) = D.cumulative y at adjacent
  linarith

theorem continuousOn_cumulative : ContinuousOn D.cumulative (Icc a b) := by
  simpa only [uIcc_of_le D.proper.le, cumulative] using
    intervalIntegral.continuousOn_primitive_interval' D.integrable left_mem_uIcc

theorem cumulative_mem (x : ℝ) (hx : x ∈ Ioo a b) :
    D.cumulative x ∈ Ioo 0 D.mass := by
  have lo := D.strictMonoOn_cumulative (left_mem_Icc.mpr D.proper.le)
    (Ioo_subset_Icc_self hx) hx.1
  have hi := D.strictMonoOn_cumulative (Ioo_subset_Icc_self hx)
    (right_mem_Icc.mpr D.proper.le) hx.2
  simpa only [D.cumulative_left, D.cumulative_right] using And.intro lo hi

theorem cumulative_image :
    D.cumulative '' Ioo a b = Ioo 0 D.mass := by
  apply Subset.antisymm
  · rintro q ⟨x,hx,rfl⟩
    exact D.cumulative_mem x hx
  · have h := intermediate_value_Ioo D.proper.le D.continuousOn_cumulative
    simpa only [D.cumulative_left, D.cumulative_right] using h

def cumulativeOrderIso : Ioo a b ≃o Ioo 0 D.mass :=
  (StrictMonoOn.orderIso D.cumulative (Ioo a b)
    (D.strictMonoOn_cumulative.mono Ioo_subset_Icc_self)).trans
    (OrderIso.setCongr _ _ D.cumulative_image)

@[simp] theorem cumulativeOrderIso_val (x : Ioo a b) :
    (D.cumulativeOrderIso x).val = D.cumulative x.val := rfl

/-- Extend the genuine inverse cumulative map arbitrarily outside its open
mass interval. All analytic uses below are inside that interval. -/
def inverseCumulative (q : ℝ) : ℝ :=
  if hq : q ∈ Ioo 0 D.mass then
    (D.cumulativeOrderIso.symm ⟨q,hq⟩).val else a

theorem inverseCumulative_mem (q : ℝ) (hq : q ∈ Ioo 0 D.mass) :
    D.inverseCumulative q ∈ Ioo a b := by
  simpa only [inverseCumulative,dif_pos hq] using
    (D.cumulativeOrderIso.symm ⟨q,hq⟩).property

theorem cumulative_inverseCumulative (q : ℝ) (hq : q ∈ Ioo 0 D.mass) :
    D.cumulative (D.inverseCumulative q) = q := by
  have h := congrArg Subtype.val (D.cumulativeOrderIso.apply_symm_apply ⟨q,hq⟩)
  change D.cumulative (D.cumulativeOrderIso.symm ⟨q,hq⟩).val = q at h
  simpa only [inverseCumulative,dif_pos hq] using h

theorem inverseCumulative_cumulative (x : ℝ) (hx : x ∈ Ioo a b) :
    D.inverseCumulative (D.cumulative x) = x := by
  have h := congrArg Subtype.val (D.cumulativeOrderIso.symm_apply_apply ⟨x,hx⟩)
  simpa only [inverseCumulative,dif_pos (D.cumulative_mem x hx)] using h

theorem continuousOn_inverseCumulative :
    ContinuousOn D.inverseCumulative (Ioo 0 D.mass) := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous (fun q : Ioo 0 D.mass =>
      (D.cumulativeOrderIso.symm q).val) :=
    continuous_subtype_val.comp D.cumulativeOrderIso.symm.continuous
  convert h using 1
  funext q
  simp only [Set.restrict_apply,inverseCumulative,dif_pos q.property]

theorem strictMonoOn_inverseCumulative :
    StrictMonoOn D.inverseCumulative (Ioo 0 D.mass) := by
  intro x hx y hy hxy
  have h := D.cumulativeOrderIso.symm.strictMono
    (show (⟨x,hx⟩ : Ioo 0 D.mass) < ⟨y,hy⟩ from hxy)
  simpa only [inverseCumulative,dif_pos hx,dif_pos hy] using h

theorem hasDerivAt_cumulative (x : ℝ) (hx : x ∈ Ioo a b) :
    HasDerivAt D.cumulative (D.density x) x := by
  have hi : IntervalIntegrable D.density volume a x :=
    D.integrable.mono_set (by
      rw [uIcc_of_le hx.1.le,uIcc_of_le D.proper.le]
      exact Icc_subset_Icc le_rfl hx.2.le)
  have hc : ContinuousAt D.density x :=
    D.continuous.continuousAt (isOpen_Ioo.mem_nhds hx)
  exact intervalIntegral.integral_hasDerivAt_right hi
    (D.continuous.stronglyMeasurableAtFilter isOpen_Ioo _ hx) hc

theorem hasDerivAt_inverseCumulative (q : ℝ) (hq : q ∈ Ioo 0 D.mass) :
    HasDerivAt D.inverseCumulative (D.density (D.inverseCumulative q))⁻¹ q := by
  have hm := D.inverseCumulative_mem q hq
  apply HasDerivAt.of_local_left_inverse
    (D.continuousOn_inverseCumulative.continuousAt (isOpen_Ioo.mem_nhds hq))
    (D.hasDerivAt_cumulative _ hm) (D.positive _ hm).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hq] with y hy
  exact D.cumulative_inverseCumulative y hy


theorem integrableOn_Ioo : IntegrableOn D.density (Ioo a b) :=
  (D.integrable.1.mono_set Ioo_subset_Ioc_self)

theorem integral_Ioo : (∫ x in Ioo a b, D.density x) = D.mass := by
  rw [mass, intervalIntegral.integral_of_le D.proper.le, integral_Ioc_eq_integral_Ioo]

end PositiveDensity

variable {a b c d : ℝ}

/-- The mass transport is constructed from the actual inverse cumulative
integral; its existence is not an extra premise. -/
def transport (A : PositiveDensity a b) (B : PositiveDensity c d) (x : ℝ) : ℝ :=
  B.inverseCumulative (A.cumulative x)

theorem transport_mem (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) (x : ℝ) (hx : x ∈ Ioo a b) :
    transport A B x ∈ Ioo c d := by
  apply B.inverseCumulative_mem
  rw [← equal]
  exact A.cumulative_mem x hx

theorem cumulative_transport (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) (x : ℝ) (hx : x ∈ Ioo a b) :
    B.cumulative (transport A B x) = A.cumulative x := by
  apply B.cumulative_inverseCumulative
  rw [← equal]
  exact A.cumulative_mem x hx

theorem strictMonoOn_transport (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) : StrictMonoOn (transport A B) (Ioo a b) := by
  intro x hx y hy hxy
  have hmx : A.cumulative x ∈ Ioo 0 B.mass := by
    rw [← equal]; exact A.cumulative_mem x hx
  have hmy : A.cumulative y ∈ Ioo 0 B.mass := by
    rw [← equal]; exact A.cumulative_mem y hy
  exact B.strictMonoOn_inverseCumulative hmx hmy
    (A.strictMonoOn_cumulative (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy)

theorem hasDerivAt_transport (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) (x : ℝ) (hx : x ∈ Ioo a b) :
    HasDerivAt (transport A B) (A.density x / B.density (transport A B x)) x := by
  have hm : A.cumulative x ∈ Ioo 0 B.mass := by
    rw [← equal]; exact A.cumulative_mem x hx
  have h := (B.hasDerivAt_inverseCumulative _ hm).comp x (A.hasDerivAt_cumulative x hx)
  simpa only [transport,Function.comp_def,div_eq_mul_inv,mul_comm] using h

theorem transport_image (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) :
    transport A B '' Ioo a b = Ioo c d := by
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact transport_mem A B equal x hx
  · intro y hy
    have hq : B.cumulative y ∈ Ioo 0 A.mass := by
      rw [equal]; exact B.cumulative_mem y hy
    refine ⟨A.inverseCumulative (B.cumulative y),
      A.inverseCumulative_mem _ hq, ?_⟩
    unfold transport
    rw [A.cumulative_inverseCumulative _ hq, B.inverseCumulative_cumulative y hy]


open BrunnMinkowskiSlices

/-- The cumulative construction discharges the transport existence and
derivative hypotheses of the slicing integral inequality. -/
theorem mass_le_midpoint_integral (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) (g : ℝ → ℝ)
    (lower : ∀ x ∈ Ioo a b,
      ((Real.sqrt (A.density x) + Real.sqrt (B.density (transport A B x)))/2)^2 ≤
        g (transportMidpoint (transport A B) x))
    (integrableG : IntegrableOn g (transportMidpoint (transport A B) '' Ioo a b)) :
    A.mass ≤ ∫ z in transportMidpoint (transport A B) '' Ioo a b, g z := by
  rw [← A.integral_Ioo]
  apply mass_le_integral_midpoint_transport measurableSet_Ioo A.density B.density g
    (transport A B) (strictMonoOn_transport A B equal).monotoneOn
    (fun x hx => (hasDerivAt_transport A B equal x hx).hasDerivWithinAt)
    (fun x hx => (A.positive x hx).le)
    (fun x hx => B.positive _ (transport_mem A B equal x hx))
    lower A.integrableOn_Ioo integrableG

/-- In an equality case the monotone cumulative transport is a translation,
and the two section densities agree after that same translation. -/
theorem exists_translation_of_midpoint_integral_eq
    (A : PositiveDensity a b) (B : PositiveDensity c d)
    (equal : A.mass = B.mass) (g : ℝ → ℝ)
    (lower : ∀ x ∈ Ioo a b,
      ((Real.sqrt (A.density x) + Real.sqrt (B.density (transport A B x)))/2)^2 ≤
        g (transportMidpoint (transport A B) x))
    (integrableG : IntegrableOn g (transportMidpoint (transport A B) '' Ioo a b))
    (equality : (∫ z in transportMidpoint (transport A B) '' Ioo a b, g z) = A.mass) :
    ∃ v : ℝ, ∀ x ∈ Ioo a b,
      transport A B x = x+v ∧ A.density x = B.density (x+v) := by
  have ae : ∀ᵐ x ∂volume.restrict (Ioo a b),
      A.density x = B.density (transport A B x) :=
    ae_section_masses_eq_of_midpoint_integral_eq measurableSet_Ioo A.density B.density g
      (transport A B) (strictMonoOn_transport A B equal).monotoneOn
      (fun x hx => (hasDerivAt_transport A B equal x hx).hasDerivWithinAt)
      (fun x hx => (A.positive x hx).le)
      (fun x hx => B.positive _ (transport_mem A B equal x hx))
      lower A.integrableOn_Ioo integrableG (equality.trans A.integral_Ioo.symm)
  have continuousT : ContinuousOn (transport A B) (Ioo a b) :=
    fun x hx => (hasDerivAt_transport A B equal x hx).continuousAt.continuousWithinAt
  have same : EqOn A.density (fun x => B.density (transport A B x)) (Ioo a b) :=
    Measure.eqOn_open_of_ae_eq ae isOpen_Ioo A.continuous
      (B.continuous.comp continuousT (fun x hx => transport_mem A B equal x hx))
  have derivativeOne (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (transport A B) 1 x := by
    have h := hasDerivAt_transport A B equal x hx
    rw [same hx, div_self (B.positive _ (transport_mem A B equal x hx)).ne'] at h
    exact h
  obtain ⟨v,hv⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
    (fun x hx => (derivativeOne x hx).differentiableAt.differentiableWithinAt)
    (differentiableOn_id : DifferentiableOn ℝ (fun x : ℝ => x) (Ioo a b))
    (fun x hx => by rw [(derivativeOne x hx).deriv]; simp)
  refine ⟨v,fun x hx => ⟨hv hx, ?_⟩⟩
  exact (same hx).trans (congrArg B.density (hv hx))

end NRR.BrunnMinkowskiTransport
