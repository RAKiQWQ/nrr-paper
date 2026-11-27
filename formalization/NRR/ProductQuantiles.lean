import NRR.CapMoments

/-! All cut choices at each prescribed interior mass level form compact
intervals. Their strict separation is valid for densities with plateaus. -/

noncomputable section
open Set Topology MeasureTheory Filter

namespace NRR.ProductQuantiles

variable {d : ℕ} (K : Set (Space d × ℝ)) (μ : Measure (Space d × ℝ))
  [IsFiniteMeasure μ]

def cumulative (t : ℝ) : ℝ := μ.real (K ∩ {x | x.2 ≤ t})

theorem continuous_cumulative (hμ : μ ≪ volume) : Continuous (cumulative K μ) := by
  have repr (t : ℝ) : cumulative K μ t =
      InterfaceChart.prefixMoment (μ.restrict K) (fun _ => (1 : ℝ)) (0,t) := by
    have eq : InterfaceChart.belowGraph ((0 : Space d →L[ℝ] ℝ),t) = {x | x.2 ≤ t} := by
      ext x
      simp [InterfaceChart.belowGraph,InterfaceChart.height]
    rw [InterfaceChart.prefixMoment,setIntegral_one_eq_measureReal,Measure.real,eq,
      Measure.restrict_apply (measurableSet_le measurable_snd measurable_const)]
    simp only [cumulative,Measure.real,inter_comm]
  have H := InterfaceChart.continuous_prefixMoment (μ.restrict K)
    (Measure.absolutelyContinuous_restrict.trans hμ) (integrable_const (1 : ℝ))
  have C : Continuous (fun t : ℝ => ((0 : Space d →L[ℝ] ℝ),t)) :=
    continuous_const.prodMk continuous_id
  exact (H.comp C).congr (fun t => (repr t).symm)

theorem monotone_cumulative : Monotone (cumulative K μ) := by
  intro s t h
  exact measureReal_mono (inter_subset_inter_right _ (fun x hx => hx.trans h))
    (measure_ne_top _ _)

theorem endpoint_values (hμ : μ ≪ volume)
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1) :
    cumulative K μ (-1) = 0 ∧ cumulative K μ 1 = μ.real K := by
  constructor
  · have H : μ {x : Space d × ℝ | x.2 = -1} = 0 := by
      simpa [InterfaceChart.height] using
        InterfaceChart.graph_null μ hμ ((0 : Space d →L[ℝ] ℝ),(-1 : ℝ))
    have hz : μ (K ∩ {x | x.2 ≤ (-1 : ℝ)}) = 0 := by
      apply measure_mono_null _ H
      rintro x ⟨hx,ht⟩
      exact le_antisymm ht (strip hx).2.1
    simp only [cumulative,Measure.real,hz,ENNReal.toReal_zero]
  · have eq : K ∩ {x | x.2 ≤ (1 : ℝ)} = K :=
      inter_eq_self_of_subset_left (fun x hx => (strip hx).2.2)
    simp only [cumulative,eq]

theorem quantile_interval (hμ : μ ≪ volume)
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    {q : ℝ} (positive : 0 < q) (below : q < μ.real K) :
    ∃ a b : ℝ, -1 < a ∧ a ≤ b ∧ b < 1 ∧
      {t | cumulative K μ t = q} = Icc a b := by
  let J := {t | cumulative K μ t = q}
  obtain ⟨hlo,hhi⟩ := endpoint_values K μ hμ strip
  have mono := monotone_cumulative K μ
  have inside : J ⊆ Ioo (-1 : ℝ) 1 := by
    intro t ht
    change cumulative K μ t = q at ht
    exact ⟨mono.reflect_lt (by rwa [hlo,ht]),mono.reflect_lt (by rwa [hhi,ht])⟩
  have closed : IsClosed J := isClosed_eq (continuous_cumulative K μ hμ) continuous_const
  have compact : IsCompact J := isCompact_Icc.of_isClosed_subset closed
    (s := Icc (-1 : ℝ) 1) (inside.trans Ioo_subset_Icc_self)
  have nonempty : J.Nonempty := by
    obtain ⟨t,_,ht⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
      (continuous_cumulative K μ hμ).continuousOn
      (by simpa only [hlo,hhi,mem_Icc] using And.intro positive.le below.le)
    exact ⟨t,ht⟩
  obtain ⟨a,ha⟩ := compact.exists_isLeast nonempty
  obtain ⟨b,hb⟩ := compact.exists_isGreatest nonempty
  refine ⟨a,b,(inside ha.1).1,ha.2 hb.1,(inside hb.1).2,
    Subset.antisymm (fun t ht => ⟨ha.2 ht,hb.2 ht⟩) ?_⟩
  intro t ht
  have hqa : cumulative K μ a = q := ha.1
  have hqb : cumulative K μ b = q := hb.1
  exact le_antisymm ((mono ht.2).trans_eq hqb) (hqa.symm ▸ mono ht.1)

theorem ordered_quantile_windows {r : ℕ} (hμ : μ ≪ volume)
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1) (positive : 0 < μ.real K) :
    ∃ a b : Fin (r+1) → ℝ,
      (∀ i, -1 < a i ∧ a i ≤ b i ∧ b i < 1 ∧
        {t | cumulative K μ t = (i.val+1 : ℝ)*(μ.real K/(r+2))} = Icc (a i) (b i)) ∧
      (∀ i j, i < j → b i < a j) := by
  have denom : 0 < (r+2 : ℝ) := by positivity
  have unit : 0 < μ.real K/(r+2) := div_pos positive denom
  have bounds (i : Fin (r+1)) :
      0 < (i.val+1 : ℝ)*(μ.real K/(r+2)) ∧
        (i.val+1 : ℝ)*(μ.real K/(r+2)) < μ.real K := by
    constructor
    · positivity
    · have hi : (i.val+1 : ℝ) < (r+2 : ℝ) := by exact_mod_cast (by omega : i.val+1 < r+2)
      calc
        _ < (r+2 : ℝ)*(μ.real K/(r+2)) := mul_lt_mul_of_pos_right hi unit
        _ = _ := mul_div_cancel₀ _ denom.ne'
  choose a b low order high level using fun i : Fin (r+1) =>
    quantile_interval K μ hμ strip (bounds i).1 (bounds i).2
  refine ⟨a,b,fun i => ⟨low i,order i,high i,level i⟩,?_⟩
  intro i j hij
  have hb : cumulative K μ (b i) = (i.val+1 : ℝ)*(μ.real K/(r+2)) :=
    show b i ∈ {t | cumulative K μ t = _} from (level i).symm ▸ right_mem_Icc.mpr (order i)
  have ha : cumulative K μ (a j) = (j.val+1 : ℝ)*(μ.real K/(r+2)) :=
    show a j ∈ {t | cumulative K μ t = _} from (level j).symm ▸ left_mem_Icc.mpr (order j)
  apply (monotone_cumulative K μ).reflect_lt
  rw [hb,ha]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast (show i.val+1 < j.val+1 by omega)) unit

theorem exists_uniform_positive {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (positive : ∀ i, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < f i := by
  have near : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, ε < f i :=
    eventually_all.mpr (fun i => gt_mem_nhds (positive i))
  obtain ⟨δ,hδ,sub⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨δ/2,by positivity,sub ?_⟩
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]
  linarith

/-- Before choosing a localization cylinder, one can choose a single
height strictly below one that contains every internal mass-quantile
window. This is valid even when any of the windows is a nontrivial interval. -/
theorem ordered_quantile_windows_bounded {r : ℕ} (hμ : μ ≪ volume)
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1) (positive : 0 < μ.real K) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ ∃ a b : Fin (r+1) → ℝ,
      (∀ i, -h < a i ∧ a i ≤ b i ∧ b i < h ∧
        {t | cumulative K μ t = (i.val+1 : ℝ)*(μ.real K/(r+2))} = Icc (a i) (b i)) ∧
      (∀ i j, i < j → b i < a j) := by
  obtain ⟨a,b,windows,gaps⟩ := ordered_quantile_windows (r := r) K μ hμ strip positive
  let f : Option (Fin (r+1)) → ℝ
    | none => 1
    | some i => min (a i+1) (1-b i)
  have pf : ∀ i,0 < f i := by
    rintro (_ | i)
    · exact zero_lt_one
    · exact lt_min (by linarith [(windows i).1]) (by linarith [(windows i).2.2.1])
  obtain ⟨ε,hε,small⟩ := exists_uniform_positive f pf
  have eps : ε < 1 := small none
  refine ⟨1-ε/2,by linarith,by linarith,a,b,?_,gaps⟩
  intro i
  have both := (small (some i)).trans_le (min_le_left (a i+1) (1-b i))
  have both' := (small (some i)).trans_le (min_le_right (a i+1) (1-b i))
  exact ⟨by linarith,(windows i).2.1,by linarith,(windows i).2.2.2⟩

end NRR.ProductQuantiles
