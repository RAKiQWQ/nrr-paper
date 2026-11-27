import NRR.CubeProductMoments
import NRR.PartitionMoments
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The final rigidity steps for product sections: paired translations are
detected by the total second moment, and constant interior sections extend
to a closed convex passive domain. These results do not assume or assert
the missing Brunn--Minkowski equality case. -/

noncomputable section
open Set MeasureTheory

namespace NRR.CubeSectionTranslation

open CubeProductMoments

instance activeHaar : Measure.IsAddHaarMeasure (volume : Measure Active) := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  infer_instance

/-- Translation in the actual three active coordinates. -/
def translate (B : Set Active) (v : Active) : Set Active :=
  (fun x => x + v) '' B

/-- The Euclidean quadratic energy, written in product coordinates. -/
def energy (x : Active) : ℝ := x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2

theorem continuous_energy : Continuous energy := by
  unfold energy
  fun_prop

theorem energy_nonneg (x : Active) : 0 ≤ energy x := by
  unfold energy
  positivity

@[simp] theorem energy_zero : energy 0 = 0 := by norm_num [energy]

theorem energy_eq_zero {x : Active} : energy x = 0 ↔ x = 0 := by
  constructor
  · intro h
    dsimp [energy] at h
    have h1 : x.1.1 = 0 := by nlinarith [sq_nonneg x.1.2, sq_nonneg x.2]
    have h2 : x.1.2 = 0 := by nlinarith [sq_nonneg x.1.1, sq_nonneg x.2]
    have h3 : x.2 = 0 := by nlinarith [sq_nonneg x.1.1, sq_nonneg x.1.2]
    exact Prod.ext (Prod.ext h1 h2) h3
  · rintro rfl
    exact energy_zero

theorem integral_translate (B : Set Active) (v : Active) (f : Active → ℝ) :
    (∫ y in translate B v, f y) = ∫ x in B, f (x + v) :=
  (measurePreserving_add_right (volume : Measure Active) v).setIntegral_image_emb
    (MeasurableEquiv.addRight v).measurableEmbedding f B

/-- Opposite translations cancel every first-moment cross term. -/
theorem energy_translation_pair (B : Set Active) (hB : IsCompact B) (v : Active) :
    (∫ y in translate B v, energy y) +
      (∫ y in translate B (-v), energy y) -
      2 * (∫ x in B, energy x) = 2 * volume.real B * energy v := by
  have hp : IntegrableOn (fun x : Active => energy (x + v)) B :=
    (continuous_energy.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact hB
  have hm : IntegrableOn (fun x : Active => energy (x + -v)) B :=
    (continuous_energy.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact hB
  have hq : IntegrableOn energy B :=
    continuous_energy.continuousOn.integrableOn_compact hB
  rw [integral_translate, integral_translate]
  calc
    _ = ∫ x in B, energy (x + v) + energy (x + -v) - 2 * energy x := by
      symm
      calc
        _ = (∫ x in B, energy (x + v) + energy (x + -v)) -
            ∫ x in B, 2 * energy x := integral_sub (hp.add hm) (hq.const_mul 2)
        _ = _ := by rw [integral_add hp hm, integral_const_mul]
    _ = ∫ _x in B, 2 * energy v := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [energy]
      ring
    _ = _ := by simp [measureReal_def, smul_eq_mul]; ring

/-- Positive masses and unchanged total moments at both translated copies
force every translation to vanish. Equal masses are not needed. -/
theorem translations_eq_zero_of_energy_sums {ι : Type*} [Fintype ι]
    (B : ι → Set Active) (compact : ∀ i, IsCompact (B i))
    (positive : ∀ i, 0 < volume.real (B i)) (v : ι → Active)
    (plus : (∑ i, ∫ x in translate (B i) (v i), energy x) =
      ∑ i, ∫ x in B i, energy x)
    (minus : (∑ i, ∫ x in translate (B i) (-v i), energy x) =
      ∑ i, ∫ x in B i, energy x) :
    ∀ i, v i = 0 := by
  classical
  have total : (∑ i, 2 * volume.real (B i) * energy (v i)) = 0 := by
    calc
      _ = ∑ i, ((∫ x in translate (B i) (v i), energy x) +
        (∫ x in translate (B i) (-v i), energy x) -
        2 * (∫ x in B i, energy x)) :=
        Finset.sum_congr rfl (fun i _ => (energy_translation_pair (B i) (compact i) (v i)).symm)
      _ = (∑ i, ∫ x in translate (B i) (v i), energy x) +
        (∑ i, ∫ x in translate (B i) (-v i), energy x) -
        2 * (∑ i, ∫ x in B i, energy x) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by rw [plus, minus]; ring
  have each := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      mul_nonneg (mul_nonneg (by norm_num) (positive i).le) (energy_nonneg (v i)))).mp total
  intro i
  apply energy_eq_zero.mp
  exact (mul_eq_zero.mp (each i (Finset.mem_univ i))).resolve_left
    (mul_pos (by norm_num : (0 : ℝ) < 2) (positive i)).ne'

/-- The geometric partition hypotheses needed for additivity, permitting
shared null boundaries. -/
structure ConvexFamilyPartition {ι : Type*} (K : Set Active) (B : ι → Set Active) : Prop where
  closed : ∀ i, IsClosed (B i)
  convex : ∀ i, Convex ℝ (B i)
  covers : (⋃ i, B i) = K
  disjoint : Pairwise fun i j => Disjoint (interior (B i)) (interior (B j))

/-- Three genuine partitions, whose cells are paired opposite translations,
have identical corresponding cells. -/
theorem translations_eq_zero_of_partitions {ι : Type*} [Fintype ι]
    (K : Set Active) (hK : IsCompact K)
    (B : ι → Set Active) (compact : ∀ i, IsCompact (B i))
    (positive : ∀ i, 0 < volume.real (B i)) (v : ι → Active)
    (base : ConvexFamilyPartition K B)
    (plus : ConvexFamilyPartition K (fun i => translate (B i) (v i)))
    (minus : ConvexFamilyPartition K (fun i => translate (B i) (-v i))) :
    ∀ i, v i = 0 := by
  have integrable : IntegrableOn energy K :=
    continuous_energy.continuousOn.integrableOn_compact hK
  have total (C : ι → Set Active) (part : ConvexFamilyPartition K C) :
      (∑ i, ∫ x in C i, energy x) = ∫ x in K, energy x :=
    (ConvexLimits.integral_partition volume volume Measure.AbsolutelyContinuous.rfl
      C part.closed part.convex part.disjoint part.covers energy integrable).symm
  exact translations_eq_zero_of_energy_sums B compact positive v
    ((total _ plus).trans (total _ base).symm)
    ((total _ minus).trans (total _ base).symm)

section GeneralGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Equality of all interior passive sections extends to the full closed
passive domain. Convexity rules out extra active spikes over the boundary. -/
theorem eq_prod_of_constant_interior_sections
    (C : Set (E × F)) (closed : IsClosed C) (convex : Convex ℝ C)
    (D : Set F) (closedD : IsClosed D) (convexD : Convex ℝ D)
    (interiorD : (interior D).Nonempty)
    (B : Set E) (nonemptyB : B.Nonempty)
    (subset : C ⊆ univ ×ˢ D)
    (sections : ∀ u ∈ interior D, {x | (x, u) ∈ C} = B) :
    C = B ×ˢ D := by
  obtain ⟨u₀, hu₀⟩ := interiorD
  obtain ⟨b, hb⟩ := nonemptyB
  have closedB : IsClosed B := by
    rw [← sections u₀ hu₀]
    exact closed.preimage (continuous_id.prodMk continuous_const)
  have base : (b, u₀) ∈ C := by
    change b ∈ {x | (x, u₀) ∈ C}
    rw [sections u₀ hu₀]
    exact hb
  apply Subset.antisymm
  · rintro ⟨x,u⟩ hp
    have hu : u ∈ D := (subset hp).2
    refine ⟨?_, hu⟩
    have hseg : openSegment ℝ (b, u₀) (x, u) ⊆ B ×ˢ (univ : Set F) := by
      rintro p ⟨a, c, ha, hc, hac, rfl⟩
      have hin := convexD.combo_interior_self_mem_interior hu₀ hu ha hc.le hac
      have hC := convex base hp ha.le hc.le hac
      have hB : a • b + c • x ∈ B := by
        rw [← sections (a • u₀ + c • u) hin]
        exact hC
      exact ⟨hB, mem_univ _⟩
    have hcl : (x,u) ∈ closure (B ×ˢ (univ : Set F)) :=
      (closure_mono hseg)
        (segment_subset_closure_openSegment (right_mem_segment ℝ (b,u₀) (x,u)))
    exact ((closedB.prod isClosed_univ).closure_subset hcl).1
  · have sub : B ×ˢ interior D ⊆ C := by
      rintro ⟨x,u⟩ ⟨hx,hu⟩
      change x ∈ {x | (x,u) ∈ C}
      rw [sections u hu]
      exact hx
    have dense : closure (B ×ˢ interior D) = B ×ˢ D := by
      rw [closure_prod_eq, closedB.closure_eq,
        convexD.closure_interior_eq_closure_of_nonempty_interior ⟨u₀,hu₀⟩,
        closedD.closure_eq]
    rw [← dense]
    exact closed.closure_subset_iff.mpr sub

end GeneralGeometry

section ProductRigidity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Once equal-volume section rigidity supplies the paired translations,
actual section partitions force the translations to vanish and all original
closed convex cells to be products. The paired-translation hypothesis is
precisely the separate Brunn--Minkowski equality output, not a conclusion
proved by this theorem. -/
theorem eq_prod_of_paired_translated_sections {ι : Type*} [Fintype ι]
    (D : Set F) (closedD : IsClosed D) (convexD : Convex ℝ D)
    (interiorD : (interior D).Nonempty)
    (symmetric : ∀ u ∈ interior D, -u ∈ interior D)
    (K : Set Active) (compactK : IsCompact K)
    (C : ι → Set (Active × F))
    (closed : ∀ i, IsClosed (C i)) (convex : ∀ i, Convex ℝ (C i))
    (subset : ∀ i, C i ⊆ univ ×ˢ D)
    (B : ι → Set Active) (compactB : ∀ i, IsCompact (B i))
    (positiveB : ∀ i, 0 < volume.real (B i))
    (base : ConvexFamilyPartition K B)
    (parts : ∀ u ∈ interior D,
      ConvexFamilyPartition K (fun i => {x | (x,u) ∈ C i}))
    (paired : ∀ u ∈ interior D, ∃ v : ι → Active,
      (∀ i, {x | (x,u) ∈ C i} = translate (B i) (v i)) ∧
      ∀ i, {x | (x,-u) ∈ C i} = translate (B i) (-v i)) :
    ∀ i, C i = B i ×ˢ D := by
  have constant (u : F) (hu : u ∈ interior D) (i : ι) :
      {x | (x,u) ∈ C i} = B i := by
    obtain ⟨v, hp, hm⟩ := paired u hu
    have plus : ConvexFamilyPartition K (fun i => translate (B i) (v i)) := by
      exact Eq.mp (congrArg (ConvexFamilyPartition K) (funext hp)) (parts u hu)
    have minus : ConvexFamilyPartition K (fun i => translate (B i) (-v i)) := by
      exact Eq.mp (congrArg (ConvexFamilyPartition K) (funext hm)) (parts (-u) (symmetric u hu))
    have zero := translations_eq_zero_of_partitions K compactK B compactB positiveB
      v base plus minus
    rw [hp i, zero i]
    simp [translate]
  intro i
  have nonemptyB : (B i).Nonempty := by
    by_contra h
    have he : B i = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simpa [he] using positiveB i
  exact eq_prod_of_constant_interior_sections (C i) (closed i) (convex i)
    D closedD convexD interiorD (B i) nonemptyB (subset i)
    (fun u hu => constant u hu i)

end ProductRigidity

section StrictVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- A closed subset of a full-dimensional closed convex set with the same
finite volume is the entire set. In particular, proper inclusion is strict
for the volume of full-dimensional compact convex bodies. -/
theorem eq_of_subset_of_measure_eq {A B : Set E}
    (closedA : IsClosed A) (closedB : IsClosed B) (convexB : Convex ℝ B)
    (interiorB : (interior B).Nonempty) (subset : A ⊆ B)
    (finite : μ B ≠ ⊤) (equal : μ A = μ B) : A = B := by
  have diff : μ (B \ A) = 0 := by
    rw [measure_diff subset closedA.measurableSet.nullMeasurableSet
      (measure_ne_top_of_subset subset finite), equal, tsub_self]
  have openDiff : IsOpen (interior B \ A) := isOpen_interior.sdiff closedA
  have emptyDiff : interior B \ A = ∅ :=
    openDiff.eq_empty_of_measure_zero (measure_mono_null
      (diff_subset_diff_left interior_subset) diff)
  have contains : interior B ⊆ A := diff_eq_empty.mp emptyDiff
  apply Subset.antisymm subset
  rw [← closedB.closure_eq,
    ← convexB.closure_interior_eq_closure_of_nonempty_interior interiorB]
  exact closedA.closure_subset_iff.mpr contains

end StrictVolume

end NRR.CubeSectionTranslation
