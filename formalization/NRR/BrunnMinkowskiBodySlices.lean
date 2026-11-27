import NRR.ConvexSectionContinuity
import NRR.BrunnMinkowskiTransport
import Mathlib.MeasureTheory.Integral.Prod

/-! The positive section densities used by cumulative transport are
constructed from actual compact full-dimensional convex bodies. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.BrunnMinkowskiBodySlices

open ConvexSectionContinuity BrunnMinkowskiTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

def projection (C : Set (E × ℝ)) : Set ℝ := Prod.snd '' C

def sectionMass (C : Set (E × ℝ)) (u : ℝ) : ℝ :=
  volume.real (fiber C u)

def lower (C : Set (E × ℝ)) : ℝ := sInf (projection C)
def upper (C : Set (E × ℝ)) : ℝ := sSup (projection C)

theorem projection_eq_interval {C : Set (E × ℝ)}
    (compact : IsCompact C) (convex : Convex ℝ C)
    (full : (interior C).Nonempty) :
    projection C = Icc (lower C) (upper C) := by
  have hp : IsCompact (projection C) := compact.image continuous_snd
  have hv : Convex ℝ (projection C) :=
    convex.linear_image (LinearMap.snd ℝ E ℝ)
  exact eq_Icc_of_connected_compact
    (hv.isConnected ((full.mono interior_subset).image Prod.snd)) hp

theorem projection_interior_nonempty {C : Set (E × ℝ)}
    (full : (interior C).Nonempty) :
    (interior (projection C)).Nonempty :=
  (full.image Prod.snd).mono (isOpenMap_snd.image_interior_subset C)

theorem lower_lt_upper {C : Set (E × ℝ)}
    (compact : IsCompact C) (convex : Convex ℝ C)
    (full : (interior C).Nonempty) : lower C < upper C := by
  have h := projection_interior_nonempty full
  rwa [projection_eq_interval compact convex full, interior_Icc, nonempty_Ioo] at h

theorem full_fiber {C : Set (E × ℝ)} (convex : Convex ℝ C)
    (full : (interior C).Nonempty) {u : ℝ}
    (hu : u ∈ interior (projection C)) :
    (interior (fiber C u)).Nonempty := by
  obtain ⟨x,hx⟩ := exists_interior_over_projection convex full hu
  have hopen : IsOpen ((fun y : E => (y,u)) ⁻¹' interior C) :=
    isOpen_interior.preimage (by fun_prop)
  refine ⟨x, interior_maximal ?_ hopen hx⟩
  exact fun _ h => (show (_,u) ∈ C from interior_subset h)

theorem sectionMass_positive {C : Set (E × ℝ)}
    (compact : IsCompact C) (convex : Convex ℝ C)
    (full : (interior C).Nonempty) {u : ℝ}
    (hu : u ∈ interior (projection C)) :
    0 < sectionMass C u :=
  ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      (full_fiber convex full hu)).ne'
    (compact_fiber compact u).measure_lt_top.ne

theorem sectionMass_zero_outside {C : Set (E × ℝ)} {u : ℝ}
    (hu : u ∉ projection C) : sectionMass C u = 0 := by
  have hf : fiber C u = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hu ⟨(x,u),hx,rfl⟩
  simp only [sectionMass,hf,measureReal_empty]

theorem measurable_sectionMass {C : Set (E × ℝ)}
    (compact : IsCompact C) : Measurable (sectionMass C) :=
  (measurable_measure_prodMk_right (μ := (volume : Measure E))
    compact.measurableSet).ennreal_toReal

/-- Fubini for a passive density on an actual compact body. -/
theorem integral_snd {C : Set (E × ℝ)} (compact : IsCompact C)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (hg : IntegrableOn (fun p : E × ℝ => g p.2) C volume) :
    (∫ p in C,g p.2 ∂volume) =
      ∫ u,sectionMass C u • g u ∂volume := by
  have ms := compact.measurableSet
  rw [← integral_indicator ms,Measure.volume_eq_prod,
    integral_prod_symm _ (hg.integrable_indicator ms)]
  apply integral_congr_ae (Eventually.of_forall ?_)
  intro u
  have eq : (fun x => C.indicator (fun p => g p.2) (x,u)) =
      (fiber C u).indicator (fun _ => g u) := by
    funext x
    by_cases h : (x,u) ∈ C <;> simp [fiber,h]
  rw [eq, integral_indicator (compact_fiber compact u).measurableSet,setIntegral_const]
  rfl

theorem integrable_sectionMass {C : Set (E × ℝ)} (compact : IsCompact C) :
    Integrable (sectionMass C) volume := by
  have ms := compact.measurableSet
  have hg : IntegrableOn (fun _ : E × ℝ => (1 : ℝ)) C volume :=
    integrableOn_const compact.measure_lt_top.ne
  have hint := (hg.integrable_indicator ms).integral_prod_right
  apply hint.congr
  filter_upwards with u
  have eq : (fun x : E => C.indicator (fun _ => (1 : ℝ)) (x,u)) =
      (fiber C u).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases h : (x,u) ∈ C <;> simp [fiber,h]
  rw [eq,integral_indicator (compact_fiber compact u).measurableSet,
    setIntegral_one_eq_measureReal]
  rfl

theorem integral_sectionMass {C : Set (E × ℝ)} (compact : IsCompact C) :
    (∫ u,sectionMass C u ∂volume) = volume.real C := by
  simpa only [smul_eq_mul,mul_one,setIntegral_one_eq_measureReal] using
    (integral_snd compact (fun _ => (1 : ℝ))
      (integrableOn_const compact.measure_lt_top.ne)).symm

/-- The actual section-volume density, with positivity and continuity only
on the open projection interval; no boundary continuity is assumed. -/
def sectionDensity (C : Set (E × ℝ)) (compact : IsCompact C)
    (convex : Convex ℝ C) (full : (interior C).Nonempty) :
    PositiveDensity (lower C) (upper C) where
  density := sectionMass C
  proper := lower_lt_upper compact convex full
  integrable := (integrable_sectionMass compact).intervalIntegrable
  positive u hu := sectionMass_positive compact convex full (by
    change u ∈ interior (projection C)
    rwa [projection_eq_interval compact convex full,interior_Icc])
  continuous := by
    have h := continuousOn_mass compact convex full
    change ContinuousOn (sectionMass C) (interior (projection C)) at h
    simpa only [projection_eq_interval compact convex full,interior_Icc] using h

@[simp] theorem sectionDensity_density (C : Set (E × ℝ)) (compact : IsCompact C)
    (convex : Convex ℝ C) (full : (interior C).Nonempty) :
    (sectionDensity C compact convex full).density = sectionMass C := rfl

/-- The transported mass is precisely the ambient body's true volume. -/
@[simp] theorem sectionDensity_mass (C : Set (E × ℝ)) (compact : IsCompact C)
    (convex : Convex ℝ C) (full : (interior C).Nonempty) :
    (sectionDensity C compact convex full).mass = volume.real C := by
  rw [PositiveDensity.mass,sectionDensity_density,
    intervalIntegral.integral_of_le (lower_lt_upper compact convex full).le,
    ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_sectionMass compact
  · intro u hu
    exact sectionMass_zero_outside (by
      rwa [projection_eq_interval compact convex full])

end NRR.BrunnMinkowskiBodySlices
