import NRR.BrunnMinkowskiSpace
import Mathlib.MeasureTheory.Group.Integral

/-! Weighted three-dimensional Brunn--Minkowski, including degenerate
compact convex bodies, and root-volume concavity of genuine sections. -/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace NRR.BrunnMinkowskiWeighted

open ConvexSectionContinuity BrunnMinkowskiBodySlices
  BrunnMinkowskiGeometry BrunnMinkowskiSpace

abbrev Active := (ℝ × ℝ) × ℝ

instance activeHaar : Measure.IsAddHaarMeasure (volume : Measure Active) := by
  rw [Measure.volume_eq_prod,Measure.volume_eq_prod]
  infer_instance

def weighted (a b : ℝ) (A B : Set Active) : Set Active :=
  (fun p : Active × Active => a • p.1+b • p.2) '' (A ×ˢ B)

theorem compact_weighted (a b : ℝ) {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B) :
    IsCompact (weighted a b A B) :=
  (compactA.prod compactB).image (by fun_prop)

theorem volume_smul (r : ℝ) (hr : 0 ≤ r) (A : Set Active) :
    volume.real (r • A) = r^3*volume.real A := by
  change (volume (r • A)).toReal = _
  rw [Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num [Module.finrank_prod,Module.finrank_self,Measure.real]

theorem root_smul (r : ℝ) (hr : 0 ≤ r) (A : Set Active) :
    (volume.real (r • A))^(1/3 : ℝ) = r*(volume.real A)^(1/3 : ℝ) := by
  rw [volume_smul r hr A,
    Real.mul_rpow (pow_nonneg hr _) measureReal_nonneg]
  have h : (r^3)^(1/3 : ℝ) = r := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast hr (by norm_num : (3 : ℕ) ≠ 0)
  rw [h]

theorem volume_translate (A : Set Active) (v : Active) :
    volume.real ((fun x => x+v) '' A) = volume.real A := by
  simpa only [setIntegral_one_eq_measureReal] using
    (measurePreserving_add_right (volume : Measure Active) v).setIntegral_image_emb
      (MeasurableEquiv.addRight v).measurableEmbedding (fun _ => (1 : ℝ)) A

theorem midpoint_smul (a b : ℝ) (A B : Set Active) :
    minkowskiMidpoint ((2*a) • A) ((2*b) • B) = weighted a b A B := by
  ext z
  constructor
  · rintro ⟨⟨x,y⟩,⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,rfl⟩
    refine ⟨(u,v),⟨hu,hv⟩,?_⟩
    dsimp
    module
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    refine ⟨((2*a) • x,(2*b) • y),⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,?_⟩
    dsimp
    module

theorem full_smul (r : ℝ) (hr : r ≠ 0) {A : Set Active}
    (full : (interior A).Nonempty) : (interior (r • A)).Nonempty :=
  (full.image (fun x => r • x)).mono ((isOpenMap_smul₀ hr).image_interior_subset A)

theorem full_of_volume_pos {A : Set Active} (convex : Convex ℝ A)
    (positive : 0 < volume.real A) : (interior A).Nonempty := by
  by_contra empty
  have he : interior A = ∅ := Set.not_nonempty_iff_eq_empty.mp empty
  have null : volume A = 0 := measure_mono_null (fun x hx => by
    exact ⟨subset_closure hx,by simpa only [he,mem_empty_iff_false,not_false_eq_true]⟩)
      (convex.addHaar_frontier volume)
  simpa only [Measure.real,null,ENNReal.zero_toReal,lt_self_iff_false] using positive

theorem weighted_lower_full {A B : Set Active}
    (compactA : IsCompact A) (convexA : Convex ℝ A)
    (fullA : (interior A).Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B)
    (fullB : (interior B).Nonempty)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a*(volume.real A)^(1/3 : ℝ)+b*(volume.real B)^(1/3 : ℝ))^3 ≤
      volume.real (weighted a b A B) := by
  have h := volume_midpoint_space
    (compactA.smul (2*a)) (convexA.smul (2*a)) (full_smul _ (by positivity) fullA)
    (compactB.smul (2*b)) (convexB.smul (2*b)) (full_smul _ (by positivity) fullB)
  rw [root_smul _ (by positivity),root_smul _ (by positivity),midpoint_smul] at h
  convert h using 1 <;> ring

theorem weighted_lower_right {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B) (nonemptyA : A.Nonempty)
    (a b : ℝ) (hb : 0 ≤ b) :
    b^3*volume.real B ≤ volume.real (weighted a b A B) := by
  obtain ⟨x,hx⟩ := nonemptyA
  have sub : (fun y => y+a • x) '' (b • B) ⊆ weighted a b A B := by
    rintro z ⟨w,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨(x,y),⟨hx,hy⟩,by dsimp; module⟩
  have h : volume.real ((fun y => y+a • x) '' (b • B)) ≤
      volume.real (weighted a b A B) :=
    measureReal_mono sub (compact_weighted a b compactA compactB).measure_lt_top.ne
  rwa [volume_translate,volume_smul b hb B] at h

theorem weighted_lower_left {A B : Set Active}
    (compactA : IsCompact A) (compactB : IsCompact B) (nonemptyB : B.Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) :
    a^3*volume.real A ≤ volume.real (weighted a b A B) := by
  obtain ⟨y,hy⟩ := nonemptyB
  have sub : (fun x => x+b • y) '' (a • A) ⊆ weighted a b A B := by
    rintro z ⟨w,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨(x,y),⟨hx,hy⟩,rfl⟩
  have h : volume.real ((fun x => x+b • y) '' (a • A)) ≤
      volume.real (weighted a b A B) :=
    measureReal_mono sub (compact_weighted a b compactA compactB).measure_lt_top.ne
  rwa [volume_translate,volume_smul a ha A] at h

/-- Weighted Brunn--Minkowski for every pair of nonempty compact convex
three-dimensional sets, including zero-volume and lower-dimensional ones. -/
theorem volume_weighted {A B : Set Active}
    (compactA : IsCompact A) (convexA : Convex ℝ A) (nonemptyA : A.Nonempty)
    (compactB : IsCompact B) (convexB : Convex ℝ B) (nonemptyB : B.Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a*(volume.real A)^(1/3 : ℝ)+b*(volume.real B)^(1/3 : ℝ))^3 ≤
      volume.real (weighted a b A B) := by
  have leftBound := weighted_lower_left compactA compactB nonemptyB a b ha
  have rightBound := weighted_lower_right compactA compactB nonemptyA a b hb
  by_cases ha0 : a = 0
  · simpa only [ha0,zero_mul,zero_add,mul_pow,cube_root _ measureReal_nonneg] using rightBound
  by_cases hb0 : b = 0
  · simpa only [hb0,zero_mul,add_zero,mul_pow,cube_root _ measureReal_nonneg] using leftBound
  by_cases va0 : volume.real A = 0
  · simpa only [va0,Real.zero_rpow (by norm_num : (1/3 : ℝ) ≠ 0),mul_zero,zero_add,
      mul_pow,cube_root _ measureReal_nonneg] using rightBound
  by_cases vb0 : volume.real B = 0
  · simpa only [vb0,Real.zero_rpow (by norm_num : (1/3 : ℝ) ≠ 0),mul_zero,add_zero,
      mul_pow,cube_root _ measureReal_nonneg] using leftBound
  exact weighted_lower_full compactA convexA
    (full_of_volume_pos convexA (lt_of_le_of_ne measureReal_nonneg (Ne.symm va0)))
    compactB convexB
    (full_of_volume_pos convexB (lt_of_le_of_ne measureReal_nonneg (Ne.symm vb0)))
    a b (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0))

/-- Genuine three-dimensional section volumes to the one-third power are
concave on the whole convex projection, including its boundary. -/
theorem section_root_concave
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C : Set (Active × F)} (compact : IsCompact C) (convex : Convex ℝ C) :
    ConcaveOn ℝ (Prod.snd '' C) (fun u : F => (volume.real (fiber C u))^(1/3 : ℝ)) := by
  refine ⟨convex.linear_image (LinearMap.snd ℝ Active F),?_⟩
  intro u hu v hv a b ha hb hab
  have nA : (fiber C u).Nonempty := by
    obtain ⟨⟨x,w⟩,hx,hwu⟩ := hu
    exact ⟨x,(show w = u from hwu) ▸ hx⟩
  have nB : (fiber C v).Nonempty := by
    obtain ⟨⟨x,w⟩,hx,hwv⟩ := hv
    exact ⟨x,(show w = v from hwv) ▸ hx⟩
  have sub : weighted a b (fiber C u) (fiber C v) ⊆ fiber C (a • u+b • v) := by
    rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    exact convex hx hy ha hb hab
  have low := volume_weighted (compact_fiber compact u) (convex_fiber convex u) nA
    (compact_fiber compact v) (convex_fiber convex v) nB a b ha hb
  have upper : volume.real (weighted a b (fiber C u) (fiber C v)) ≤
      volume.real (fiber C (a • u+b • v)) :=
    measureReal_mono sub (compact_fiber compact _).measure_lt_top.ne
  have nonneg : 0 ≤ a*(volume.real (fiber C u))^(1/3 : ℝ)+
      b*(volume.real (fiber C v))^(1/3 : ℝ) := by positivity
  have rpowBound := Real.rpow_le_rpow (pow_nonneg nonneg _) (low.trans upper)
    (by norm_num : (0 : ℝ) ≤ 1/3)
  have rootCube : ((a*(volume.real (fiber C u))^(1/3 : ℝ)+
      b*(volume.real (fiber C v))^(1/3 : ℝ))^3)^(1/3 : ℝ) =
      a*(volume.real (fiber C u))^(1/3 : ℝ)+b*(volume.real (fiber C v))^(1/3 : ℝ) := by
    simpa only [one_div] using
      Real.pow_rpow_inv_natCast nonneg (by norm_num : (3 : ℕ) ≠ 0)
  simpa only [rootCube,smul_eq_mul] using rpowBound

end NRR.BrunnMinkowskiWeighted
