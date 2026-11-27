import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Vertical integration over the closed region between continuous graphs. -/

noncomputable section
open Set MeasureTheory

namespace NRR.CubeFourMomentReadout

def squareBase : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

def graphSlab (l u : (ℝ × ℝ) → ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {v | v.1.1 ∈ Icc (-1 : ℝ) 1 ∧ v.1.2 ∈ Icc (-1 : ℝ) 1 ∧ v.2 ∈ Icc (l v.1) (u v.1)}

theorem isCompact_graphSlab (l u : (ℝ × ℝ) → ℝ) (hl : Continuous l) (hu : Continuous u) :
    IsCompact (graphSlab l u) := by
  have hB : IsCompact squareBase := isCompact_Icc.prod isCompact_Icc
  obtain ⟨cl, bl⟩ := (hB.image hl).isBounded.exists_norm_le
  obtain ⟨cu, bu⟩ := (hB.image hu).isBounded.exists_norm_le
  have closed : IsClosed (graphSlab l u) :=
    (isClosed_Icc.preimage continuous_fst.fst).inter
      ((isClosed_Icc.preimage continuous_fst.snd).inter
        ((isClosed_le (hl.comp continuous_fst) continuous_snd).inter
          (isClosed_le continuous_snd (hu.comp continuous_fst))))
  apply (hB.prod (isCompact_Icc (a := -cl) (b := cu))).of_isClosed_subset closed
  rintro ⟨p,z⟩ ⟨hx,hy,hz⟩
  have hp : p ∈ squareBase := ⟨hx,hy⟩
  have h₁ : |l p| ≤ cl := bl _ (mem_image_of_mem l hp)
  have h₂ : |u p| ≤ cu := bu _ (mem_image_of_mem u hp)
  exact ⟨hp, (abs_le.mp h₁).1.trans hz.1, hz.2.trans (abs_le.mp h₂).2⟩

private theorem integral_Icc_eq_interval {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in Icc a b, f x = ∫ x in a..b, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- Fubini for the actual closed slab. The ordering is needed only on the square. -/
theorem integral_graphSlab (l u : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) × ℝ → ℝ)
    (hl : Continuous l) (hu : Continuous u)
    (hlu : ∀ p ∈ squareBase, l p ≤ u p) (hg : Continuous g) :
    (∫ v in graphSlab l u, g v) =
      ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ∫ z in l (x,y)..u (x,y), g ((x,y),z) := by
  classical
  let f := (graphSlab l u).indicator g
  let G (p : ℝ × ℝ) := ∫ z in Icc (l p) (u p), g (p,z)
  have compact := isCompact_graphSlab l u hl hu
  have hf : Integrable f := (hg.continuousOn.integrableOn_compact compact).integrable_indicator
    compact.measurableSet
  have hB : MeasurableSet squareBase := measurableSet_Icc.prod measurableSet_Icc
  have section_eq (p : ℝ × ℝ) : (∫ z, f (p,z)) = squareBase.indicator G p := by
    have mem (z : ℝ) : (p,z) ∈ graphSlab l u ↔ p ∈ squareBase ∧ z ∈ Icc (l p) (u p) :=
      and_assoc.symm
    by_cases hp : p ∈ squareBase
    · rw [indicator_of_mem hp]
      change _ = ∫ z in Icc (l p) (u p), g (p,z)
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with z
      simp only [f, indicator_apply, mem, hp, true_and]
    · rw [indicator_of_notMem hp]
      simp only [f, indicator_apply, mem, hp, false_and, if_false, integral_zero]
  have hG : IntegrableOn G squareBase :=
    (integrable_indicator_iff hB).mp (hf.integral_prod_left.congr (ae_of_all _ section_eq))
  have h1 : (-1 : ℝ) ≤ 1 := by norm_num
  calc
    _ = ∫ v, f v := (integral_indicator compact.measurableSet).symm
    _ = ∫ p, ∫ z, f (p,z) := integral_prod f hf
    _ = ∫ p in squareBase, G p := by simp_rw [section_eq]; exact integral_indicator hB
    _ = ∫ x in Icc (-1 : ℝ) 1, ∫ y in Icc (-1 : ℝ) 1, G (x,y) := setIntegral_prod G hG
    _ = _ := by
      rw [integral_Icc_eq_interval h1]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [integral_Icc_eq_interval h1]
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le h1] at hx hy
      exact integral_Icc_eq_interval (hlu (x,y) ⟨hx,hy⟩) _

end NRR.CubeFourMomentReadout
