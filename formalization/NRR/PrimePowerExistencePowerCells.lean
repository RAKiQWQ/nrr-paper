import NRR.PrimePowerExistenceConfiguration
import NRR.PrimePowerCuts

/-!
Affine power cells, before choosing their equal-mass weights. Distinct sites
give closed convex cells with disjoint interiors for every weight vector.
Positive prescribed masses then turn these sets into the exact `BodyPartition`
used in the classification statement. Weight existence and continuous choice
of weights are separate obligations and are not asserted here.
-/

noncomputable section
open Set MeasureTheory

namespace NRR.PrimePower

def powerScore {d n : ℕ} (x : Configuration d n) (w : Fin n → ℝ)
    (i : Fin n) (y : Space d) : ℝ := inner ℝ (x.val i) y + w i

def powerCell {d n : ℕ} (K : Body d) (x : Configuration d n) (w : Fin n → ℝ)
    (i : Fin n) : Set (Space d) :=
  K.points ∩ ⋂ j, (innerSL ℝ (x.val j - x.val i)) ⁻¹' Iic (w i - w j)

theorem mem_powerCell_iff {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (i : Fin n) (y : Space d) :
    y ∈ powerCell K x w i ↔ y ∈ K.points ∧ ∀ j, powerScore x w j y ≤ powerScore x w i y := by
  simp only [powerCell, mem_inter_iff, mem_iInter, mem_preimage, mem_Iic,
    innerSL_apply, inner_sub_left]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun j => ?_⟩
    dsimp [powerScore]
    linarith [h j]
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun j => ?_⟩
    have hj := h j
    dsimp [powerScore] at hj
    linarith

theorem isCompact_powerCell {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (i : Fin n) : IsCompact (powerCell K x w i) :=
  K.val.isCompact.inter_right (isClosed_iInter fun j =>
    isClosed_Iic.preimage (innerSL ℝ (x.val j - x.val i)).continuous)

theorem convex_powerCell {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (i : Fin n) : Convex ℝ (powerCell K x w i) :=
  K.property.1.inter (convex_iInter fun j =>
    convex_halfSpace_le (innerSL ℝ (x.val j - x.val i)).toLinearMap.isLinear _)

theorem powerCells_cover {d n : ℕ} (hn : 0 < n) (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) : (⋃ i, powerCell K x w i) = K.points := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
  intro y hy
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i => powerScore x w i y)
  exact mem_iUnion.mpr ⟨i, (mem_powerCell_iff K x w i y).mpr ⟨hy, hi⟩⟩

private theorem inner_surjective {d : ℕ} {a : Space d} (ha : a ≠ 0) :
    Function.Surjective (innerSL ℝ a) := by
  have haa : inner ℝ a a ≠ 0 := (real_inner_self_pos.mpr ha).ne'
  intro r
  refine ⟨(r / inner ℝ a a) • a, ?_⟩
  simp [innerSL_apply, haa]

theorem powerCells_disjoint {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) :
    Pairwise fun i j => Disjoint (interior (powerCell K x w i))
      (interior (powerCell K x w j)) := by
  intro i j hij
  let L := innerSL ℝ (x.val j - x.val i)
  let c := w i - w j
  have surj : Function.Surjective L := inner_surjective (sub_ne_zero.mpr (x.property.ne hij.symm))
  have lower : powerCell K x w i ⊆ L ⁻¹' Iic c := by
    intro y hy
    exact mem_iInter.mp hy.2 j
  have upper : powerCell K x w j ⊆ L ⁻¹' Ici c := by
    intro y hy
    have hi := mem_iInter.mp hy.2 i
    change inner ℝ (x.val i - x.val j) y ≤ w j - w i at hi
    change w i - w j ≤ inner ℝ (x.val j - x.val i) y
    simp only [inner_sub_left] at hi ⊢
    linarith
  have li : interior (powerCell K x w i) ⊆ L ⁻¹' Iio c := by
    rw [← interior_Iic, ← L.interior_preimage surj]
    exact interior_mono lower
  have ui : interior (powerCell K x w j) ⊆ L ⁻¹' Ioi c := by
    rw [← interior_Ici, ← L.interior_preimage surj]
    exact interior_mono upper
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  have hl : L y < c := li hyi
  have hu : c < L y := ui hyj
  exact lt_asymm hl hu

/-- Ties between two distinct sites lie on one null hyperplane. -/
theorem powerCells_overlap_null {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (μ : Measure (Space d)) (hμ : μ ≪ volume)
    {i j : Fin n} (hij : i ≠ j) :
    μ (powerCell K x w i ∩ powerCell K x w j) = 0 := by
  let L := innerSL ℝ (x.val j - x.val i)
  let c := w i - w j
  have surj : Function.Surjective L := inner_surjective (sub_ne_zero.mpr (x.property.ne hij.symm))
  apply measure_mono_null (t := L ⁻¹' {c}) ?_ (ParallelCuts.hyperplane_null μ L hμ surj c)
  intro y hy
  have hi := ((mem_powerCell_iff K x w i y).mp hy.1).2 j
  have hj := ((mem_powerCell_iff K x w j y).mp hy.2).2 i
  change inner ℝ (x.val j - x.val i) y = w i - w j
  simp only [powerScore, inner_sub_left] at hi hj ⊢
  linarith

/-- A common additive normalization of the weights changes no cell. -/
theorem powerCell_add_constant {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    powerCell K x (fun j => w j + c) i = powerCell K x w i := by
  simp only [powerCell, add_sub_add_right_eq_sub]

/-- Relabeling sites and weights gives exactly the relabeled original cells. -/
theorem powerCell_relabel {d n : ℕ} (K : Body d) (σ : Equiv.Perm (Fin n))
    (x : Configuration d n) (w : Fin n → ℝ) (i : Fin n) :
    powerCell K (σ • x) (fun j => w (σ.symm j)) i = powerCell K x w (σ.symm i) := by
  ext y
  rw [mem_powerCell_iff, mem_powerCell_iff]
  change (y ∈ K.points ∧ ∀ j, powerScore x w (σ.symm j) y ≤ powerScore x w (σ.symm i) y) ↔
    y ∈ K.points ∧ ∀ j, powerScore x w j y ≤ powerScore x w (σ.symm i) y
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun j => by simpa only [Equiv.symm_apply_apply] using h (σ j)⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun j => h (σ.symm j)⟩

theorem powerCell_interior_nonempty {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (μ : Measure (Space d)) (hμ : μ ≪ volume) (i : Fin n)
    (hm : 0 < μ (powerCell K x w i)) : (interior (powerCell K x w i)).Nonempty := by
  by_contra! hi
  have hz := hμ ((convex_powerCell K x w i).addHaar_frontier volume)
  rw [frontier, (isCompact_powerCell K x w i).isClosed.closure_eq, hi, diff_empty] at hz
  exact hm.ne' hz

/-- Positive-mass power cells are genuine full-dimensional convex bodies. -/
def powerBody {d n : ℕ} (K : Body d) (x : Configuration d n) (w : Fin n → ℝ)
    (μ : Measure (Space d)) (hμ : μ ≪ volume) (hm : ∀ i, 0 < μ (powerCell K x w i))
    (i : Fin n) : Body d :=
  let hi := powerCell_interior_nonempty K x w μ hμ i (hm i)
  ⟨⟨⟨powerCell K x w i, isCompact_powerCell K x w i⟩, hi.mono interior_subset⟩,
    convex_powerCell K x w i, hi⟩

theorem powerBody_partition {d n : ℕ} (hn : 0 < n) (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (μ : Measure (Space d)) (hμ : μ ≪ volume)
    (hm : ∀ i, 0 < μ (powerCell K x w i)) :
    BodyPartition K (powerBody K x w μ hμ hm) :=
  ⟨powerCells_cover hn K x w, powerCells_disjoint K x w⟩

theorem powerBody_equalMass {d n : ℕ} (K : Body d) (x : Configuration d n)
    (w : Fin n → ℝ) (μ : Measure (Space d)) (hμ : μ ≪ volume)
    (hm : ∀ i, 0 < μ (powerCell K x w i))
    (equal : ∀ i j, μ (powerCell K x w i) = μ (powerCell K x w j)) :
    EqualMass μ (powerBody K x w μ hμ hm) := equal

end NRR.PrimePower
