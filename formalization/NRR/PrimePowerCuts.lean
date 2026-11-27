import NRR.Partitions
import Mathlib.Analysis.Normed.Operator.Banach

/-! Parallel cuts of a prescribed convex body for absolutely continuous mass. -/

noncomputable section
open Set MeasureTheory Topology Filter TopologicalSpace

namespace NRR
namespace ParallelCuts

variable {d : ℕ} (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
  (L : Space d →L[ℝ] ℝ)

/-- Mass below a cut with a fixed normal, clipped to the parent body. -/
def cumulative (t : ℝ) : ℝ := μ.real (K.points ∩ L ⁻¹' Iic t)

omit [IsFiniteMeasure μ] in
theorem hyperplane_null (hμ : μ ≪ volume) (hL : Function.Surjective L) (t : ℝ) :
    μ (L ⁻¹' {t}) = 0 := by
  apply hμ
  have h := (convex_halfSpace_le L.toLinearMap.isLinear t).addHaar_frontier volume
  change volume (frontier (L ⁻¹' Iic t)) = 0 at h
  rwa [L.frontier_preimage hL, frontier_Iic] at h

theorem continuous_cumulative (hμ : μ ≪ volume) (hL : Function.Surjective L) :
    Continuous (cumulative K μ L) := by
  let cap (t : ℝ) := K.points ∩ L ⁻¹' Iic t
  have measurable (t : ℝ) : MeasurableSet (cap t) :=
    K.val.isCompact.isClosed.measurableSet.inter (L.continuous.measurable measurableSet_Iic)
  have repr (t : ℝ) : cumulative K μ L t = ∫ x, (cap t).indicator (fun _ => (1 : ℝ)) x ∂μ := by
    simp only [integral_indicator (measurable _), setIntegral_one_eq_measureReal]
    rfl
  refine continuous_iff_seqContinuous.mpr ?_
  intro s t hs
  simp only [Function.comp_def, repr]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => aestronglyMeasurable_const.indicator (measurable _)) (integrable_const 1)
  · intro n
    exact Eventually.of_forall fun x => by by_cases hx : x ∈ cap (s n) <;> simp [hx]
  · have hn : ∀ᵐ x ∂μ, x ∉ L ⁻¹' {t} := compl_mem_ae_iff.mpr (hyperplane_null μ L hμ hL t)
    filter_upwards [hn] with x hx
    apply tendsto_const_nhds.congr'
    have hne : L x ≠ t := hx
    by_cases hK : x ∈ K.points
    · rcases hne.lt_or_gt with ht | ht
      · filter_upwards [hs.eventually (lt_mem_nhds ht)] with n hn
        simp [cap, hK, ht.le, hn.le]
      · filter_upwards [hs.eventually (gt_mem_nhds ht)] with n hn
        simp [cap, hK, not_le.mpr ht, not_le.mpr hn]
    · exact Eventually.of_forall fun n => by simp [cap, hK]

theorem monotone_cumulative : Monotone (cumulative K μ L) := by
  intro s t h
  exact measureReal_mono (inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.mpr h)))

omit [IsFiniteMeasure μ] in
private theorem bounds :
    ∃ lo hi : ℝ, lo ≤ hi ∧ (∀ x ∈ K.points, lo ≤ L x ∧ L x ≤ hi) ∧
      cumulative K μ L lo = 0 ∧ cumulative K μ L hi = μ.real K.points := by
  obtain ⟨R, hR, hbound⟩ := (K.val.isCompact.image L.continuous).isBounded.exists_pos_norm_le
  have hb (x) (hx : x ∈ K.points) : -R ≤ L x ∧ L x ≤ R :=
    abs_le.mp (hbound _ (mem_image_of_mem _ hx))
  refine ⟨-R-1, R, by linarith, fun x hx => ⟨by linarith [(hb x hx).1], (hb x hx).2⟩, ?_, ?_⟩
  · have e : K.points ∩ L ⁻¹' Iic (-R-1) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, ht⟩
      have : L x ≤ -R-1 := ht
      linarith [(hb x hx).1]
    simp [cumulative, e]
  · have e : K.points ∩ L ⁻¹' Iic R = K.points := inter_eq_self_of_subset_left fun x hx => (hb x hx).2
    simp [cumulative, e]

/-- Includes endpoint masses and allows nontrivial intervals of quantiles. -/
theorem exists_cut (hμ : μ ≪ volume) (hL : Function.Surjective L)
    {q : ℝ} (h₀ : 0 ≤ q) (h₁ : q ≤ μ.real K.points) :
    ∃ t, cumulative K μ L t = q := by
  obtain ⟨lo, hi, hle, _, hl, hh⟩ := bounds K μ L
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hle
    (continuous_cumulative K μ L hμ hL).continuousOn (by simpa [hl, hh] using And.intro h₀ h₁)
  exact ⟨x, hx⟩

/-- Every interior mass level is a closed bounded interval of cut heights.
This permits plateaus of the cumulative mass at the chosen level. -/
theorem quantile_interval (hμ : μ ≪ volume) (hL : Function.Surjective L)
    {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < μ.real K.points) :
    ∃ a b : ℝ, a ≤ b ∧ {s | cumulative K μ L s = q} = Icc a b := by
  let J := {s | cumulative K μ L s = q}
  obtain ⟨lo, hi, _, _, hl, hh⟩ := bounds K μ L
  have hmon := monotone_cumulative K μ L
  have closed : IsClosed J := isClosed_eq (continuous_cumulative K μ L hμ hL) continuous_const
  have compact : IsCompact J := isCompact_Icc.of_isClosed_subset closed (s := Icc lo hi) (by
    intro s hs
    change cumulative K μ L s = q at hs
    constructor
    · exact (hmon.reflect_lt (hl ▸ hs.symm ▸ hq₀)).le
    · exact (hmon.reflect_lt (hh ▸ hs.symm ▸ hq₁)).le)
  have nonempty : J.Nonempty := exists_cut K μ L hμ hL hq₀.le hq₁.le
  obtain ⟨a, ha⟩ := compact.exists_isLeast nonempty
  obtain ⟨b, hb⟩ := compact.exists_isGreatest nonempty
  refine ⟨a, b, ha.2 hb.1, Subset.antisymm (fun _ hx => ⟨ha.2 hx, hb.2 hx⟩) ?_⟩
  intro s hs
  have hqa : cumulative K μ L a = q := ha.1
  have hqb : cumulative K μ L b = q := hb.1
  exact le_antisymm ((hmon hs.2).trans_eq hqb) (hqa.symm ▸ hmon hs.1)

/-- Distinct interior mass levels admit a positive uniform gap between all
choices of their cuts. -/
theorem separated_quantiles (hμ : μ ≪ volume) (hL : Function.Surjective L)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < μ.real K.points) :
    ∃ δ > (0 : ℝ), ∀ s t, cumulative K μ L s = p → cumulative K μ L t = q → δ ≤ t - s := by
  obtain ⟨a, b, hab, J⟩ := quantile_interval K μ L hμ hL hp (hpq.trans hq)
  obtain ⟨c, e, hce, J'⟩ := quantile_interval K μ L hμ hL (hp.trans hpq) hq
  have hb : cumulative K μ L b = p :=
    show b ∈ {s | cumulative K μ L s = p} from J ▸ right_mem_Icc.mpr hab
  have hc : cumulative K μ L c = q :=
    show c ∈ {s | cumulative K μ L s = q} from J' ▸ left_mem_Icc.mpr hce
  refine ⟨c - b, sub_pos.mpr ((monotone_cumulative K μ L).reflect_lt (by rwa [hb, hc])), ?_⟩
  intro s t hs ht
  have hs' : s ∈ Icc a b := J ▸ hs
  have ht' : t ∈ Icc c e := J' ▸ ht
  exact sub_le_sub ht'.1 hs'.2

/-- The first and last cuts enclose the whole parent even when the support of
the mass is strictly smaller. The interior cuts are strictly ordered. -/
theorem exists_quantiles (hμ : μ ≪ volume) (hL : Function.Surjective L)
    (hK : 0 < μ.real K.points) {n : ℕ} (hn : 0 < n) :
    ∃ t : Fin (n + 1) → ℝ, StrictMono t ∧
      (∀ x ∈ K.points, t 0 ≤ L x ∧ L x ≤ t (Fin.last n)) ∧
      ∀ i, cumulative K μ L (t i) = (i.val : ℝ) * (μ.real K.points / n) := by
  obtain ⟨lo, hi, _, hb, hl, hh⟩ := bounds K μ L
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let a := μ.real K.points / n
  have ha : 0 < a := div_pos hK hn'
  have hna : (n : ℝ) * a = μ.real K.points := by dsimp [a]; field_simp
  have cuts (i : Fin (n+1)) : ∃ s, cumulative K μ L s = i.val * a ∧
      (i.val = 0 → s = lo) ∧ (i.val = n → s = hi) := by
    by_cases hi₀ : i.val = 0
    · exact ⟨lo, by simp [hi₀, hl], fun _ => rfl, fun hx => by omega⟩
    by_cases hiₙ : i.val = n
    · exact ⟨hi, by simp [hiₙ, hh, hna], fun hx => (hi₀ hx).elim, fun _ => rfl⟩
    have hi' : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    obtain ⟨s, hs⟩ := exists_cut K μ L hμ hL (mul_nonneg (Nat.cast_nonneg _) ha.le)
      ((mul_le_mul_of_nonneg_right hi' ha.le).trans_eq hna)
    exact ⟨s, hs, fun hx => (hi₀ hx).elim, fun hx => (hiₙ hx).elim⟩
  choose t hmass hfirst hlast using cuts
  refine ⟨t, ?_, ?_, hmass⟩
  · intro i j hij
    apply (monotone_cumulative K μ L).reflect_lt
    rw [hmass, hmass]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) ha
  · intro x hx
    rw [hfirst 0 rfl, hlast (Fin.last n) rfl]
    exact hb x hx

/-- A closed slab has mass equal to the difference of its two cumulative
values, since its lower face has zero mass. -/
theorem slab_mass (hμ : μ ≪ volume) (hL : Function.Surjective L) {s t : ℝ} (hst : s ≤ t) :
    μ.real (K.points ∩ L ⁻¹' Icc s t) = cumulative K μ L t - cumulative K μ L s := by
  let cap (r : ℝ) := K.points ∩ L ⁻¹' Iic r
  let slab := K.points ∩ L ⁻¹' Icc s t
  have ms : MeasurableSet slab := K.val.isCompact.isClosed.measurableSet.inter
    (L.continuous.measurable measurableSet_Icc)
  have cover : cap s ∪ slab = cap t := by
    dsimp only [cap, slab]
    rw [← inter_union_distrib_left, ← preimage_union, Iic_union_Icc_eq_Iic hst]
  have hd : AEDisjoint μ (cap s) slab := by
    apply measure_mono_null _ (hyperplane_null μ L hμ hL s)
    intro x hx
    exact le_antisymm hx.1.2 hx.2.2.1
  have he := measureReal_union₀ ms.nullMeasurableSet hd
  rw [cover] at he
  change μ.real slab = μ.real (cap t) - μ.real (cap s)
  linarith

private theorem intervals_cover {n : ℕ} (hn : 0 < n) (t : Fin (n+1) → ℝ) (ht : Monotone t)
    {y : ℝ} (h₀ : t 0 ≤ y) (hl : y ≤ t (Fin.last n)) :
    ∃ i : Fin n, y ∈ Icc (t i.castSucc) (t i.succ) := by
  suffices h : ∀ j : Fin (n+1), y ≤ t j → ∃ i : Fin n, y ∈ Icc (t i.castSucc) (t i.succ) from
    h _ hl
  intro j
  induction j using Fin.induction with
  | zero =>
    intro hy
    let i : Fin n := ⟨0, hn⟩
    exact ⟨i, h₀, hy.trans (ht (Fin.zero_le _))⟩
  | succ i ih =>
    intro hy
    by_cases h : y ≤ t i.castSucc
    · exact ih h
    · exact ⟨i, (le_of_not_ge h), hy⟩

/-- For every number of pieces and prescribed normal, consecutive quantile
hyperplanes cut K into closed full-dimensional bodies of equal mass. -/
theorem exists_equalMass_slabs (hμ : μ ≪ volume) (hL : Function.Surjective L)
    (hK : 0 < μ.real K.points) {n : ℕ} (hn : 0 < n) :
    ∃ (t : Fin (n + 1) → ℝ) (S : Fin n → Body d), StrictMono t ∧
      (∀ i, (S i).points = K.points ∩ L ⁻¹' Icc (t i.castSucc) (t i.succ)) ∧
      BodyPartition K S ∧ EqualMass μ S := by
  obtain ⟨t, ht, hb, hc⟩ := exists_quantiles K μ L hμ hL hK hn
  let A (i : Fin n) := K.points ∩ L ⁻¹' Icc (t i.castSucc) (t i.succ)
  have hcpt (i : Fin n) : IsCompact (A i) :=
    K.val.isCompact.inter_right (isClosed_Icc.preimage L.continuous)
  have hcvx (i : Fin n) : Convex ℝ (A i) :=
    K.property.1.inter ((convex_Icc _ _).is_linear_preimage L.toLinearMap.isLinear)
  have mass (i : Fin n) : μ.real (A i) = μ.real K.points / n := by
    rw [show μ.real (A i) = _ from slab_mass K μ L hμ hL (ht.monotone i.castSucc_le_succ),
      hc, hc]
    change ((i.val + 1 : ℕ) : ℝ) * _ - (i.val : ℝ) * _ = _
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hint (i : Fin n) : (interior (A i)).Nonempty := by
    by_contra! h
    have hz := hμ ((hcvx i).addHaar_frontier volume)
    rw [frontier, (hcpt i).isClosed.closure_eq, h, diff_empty] at hz
    have pos : 0 < μ.real (A i) := (mass i).symm ▸ div_pos hK (by exact_mod_cast hn)
    have eqzero : μ.real (A i) = 0 := by simp [measureReal_def, hz]
    exact pos.ne' eqzero
  let S (i : Fin n) : Body d :=
    ⟨⟨⟨A i, hcpt i⟩, (hint i).mono interior_subset⟩, hcvx i, hint i⟩
  refine ⟨t, S, ht, fun _ => rfl, ⟨?_, ?_⟩, ?_⟩
  · apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
    intro x hx
    obtain ⟨i, hi⟩ := intervals_cover hn t ht.monotone (hb x hx).1 (hb x hx).2
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  · intro i j hij
    have within (k : Fin n) : interior (S k).points ⊆ L ⁻¹' Ioo (t k.castSucc) (t k.succ) := by
      rw [← interior_Icc, ← L.interior_preimage hL]
      exact interior_mono inter_subset_right
    apply Set.disjoint_left.mpr
    intro x hi hj
    obtain ⟨hil, hiu⟩ := within i hi
    obtain ⟨hjl, hju⟩ := within j hj
    rcases lt_or_gt_of_ne hij with h | h
    · have hor : i.succ ≤ j.castSucc := h
      exact (not_lt_of_ge (ht.monotone hor)) (hjl.trans hiu)
    · have hor : j.succ ≤ i.castSucc := h
      exact (not_lt_of_ge (ht.monotone hor)) (hil.trans hju)
  · intro i j
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      ((mass i).trans (mass j).symm)

end ParallelCuts
end NRR
