import NRR.Partitions

/-! Removing a positive background mass from a fair-partition theorem. -/

noncomputable section
open Set MeasureTheory Topology Filter
open scoped NNReal ENNReal

namespace NRR

theorem isClosed_equalValues {d n : ℕ} (φ : Fin (d - 1) → C(Body d, ℝ)) :
    IsClosed {S : Fin n → Body d | EqualValues φ S} := by
  simp only [EqualValues, setOf_forall]
  exact isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((φ k).continuous.comp (continuous_apply i))
      ((φ k).continuous.comp (continuous_apply j))

/-- Both mass errors and characteristic errors may tend to zero before taking
a fair Hausdorff limit. A positive limiting mass prevents degenerate cells. -/
theorem fairPartition_of_convergent_errors {d n : ℕ} (K : Body d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (φ : Fin (d - 1) → C(Body d, ℝ)) (A : ℕ → Fin n → Body d)
    (hA : ∀ m, BodyPartition K (A m)) {a : ℝ} (ha : 0 < a)
    (hm : ∀ i, Tendsto (fun m => μ.real (A m i).points) atTop (𝓝 a))
    (hv : ∀ k i j, Tendsto (fun m => φ k (A m i) - φ k (A m j))
      atTop (𝓝 0)) :
    AdmitsFairPartition n K μ φ := by
  let s := {C : Body d | C.points ⊆ K.points ∧ ENNReal.ofReal (a / 2) ≤ μ C.points}
  have compact : IsCompact (univ.pi (fun _ : Fin n => s)) :=
    isCompact_univ_pi fun _ => CompactTests.compact_cells K μ hμ
      (ENNReal.ofReal_pos.mpr (half_pos ha))
  have ev (i : Fin n) : ∀ᶠ m in atTop, A m i ∈ s := by
    filter_upwards [(hm i).eventually (lt_mem_nhds (half_lt_self ha))] with m hm
    refine ⟨?_, (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hm.le⟩
    rw [← (hA m).covers]
    exact subset_iUnion (fun i => (A m i).points) i
  have freq : ∃ᶠ m in atTop, A m ∈ univ.pi (fun _ : Fin n => s) := by
    apply Eventually.frequently
    filter_upwards [Filter.eventually_all.mpr ev] with m hm using fun i _ => hm i
  obtain ⟨S, _, σ, hσ, near⟩ := compact.tendsto_subseq' freq
  have hp := (isClosed_bodyPartitions (n := n) K).mem_of_tendsto near
    (Eventually.of_forall fun m => hA (σ m))
  have hbody : Continuous (Body.toCompactConvex (d := d)) :=
    continuous_subtype_val.subtype_mk _
  have hc : Continuous (fun C : Body d => μ.real C.points) := by
    simpa [Function.comp_def, setIntegral_one_eq_measureReal, Moments.points,
      Body.toCompactConvex, Body.points] using
      (Moments.continuous_integral μ hμ (integrable_const (1 : ℝ))).comp hbody
  have hS (i : Fin n) : μ.real (S i).points = a := tendsto_nhds_unique
    ((hc.tendsto _).comp (tendsto_pi_nhds.mp near i))
    ((hm i).comp hσ.tendsto_atTop)
  refine ⟨S, hp, fun i j => (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _)).mp ((hS i).trans (hS j).symm), ?_⟩
  intro k i j
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique
    ((((φ k).continuous.tendsto _).comp (tendsto_pi_nhds.mp near i)).sub
      (((φ k).continuous.tendsto _).comp (tendsto_pi_nhds.mp near j)))
    ((hv k i j).comp hσ.tendsto_atTop)

/-- If every piece of a sequence of partitions tends to the same positive
mass, one can take a Hausdorff limit while preserving equal characteristics. -/
theorem fairPartition_of_convergent_masses {d n : ℕ} (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (φ : Fin (d - 1) → C(Body d, ℝ))
    (A : ℕ → Fin n → Body d) (hA : ∀ k, BodyPartition K (A k))
    (fair : ∀ k, EqualValues φ (A k)) {a : ℝ} (ha : 0 < a)
    (hm : ∀ i, Tendsto (fun k => μ.real (A k i).points) atTop (𝓝 a)) :
    AdmitsFairPartition n K μ φ := by
  apply fairPartition_of_convergent_errors K μ hμ φ A hA ha hm
  intro k i j
  simpa only [fun m => sub_eq_zero.mpr (fair m k i j)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- It suffices to produce fair partitions after adding an arbitrarily small
multiple of a finite background measure. In particular the background may
be ordinary volume restricted to K, which fills all gaps in the density. -/
theorem fairPartition_of_positive_background {d n : ℕ} (hn : 0 < n)
    (K : Body d) (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ volume) (hν : ν ≪ volume) (hK : 0 < μ.real K.points)
    (φ : Fin (d - 1) → C(Body d, ℝ))
    (fair : ∀ c : ℝ≥0, 0 < c → AdmitsFairPartition n K (μ + c • ν) φ) :
    AdmitsFairPartition n K μ φ := by
  let c (k : ℕ) : ℝ≥0 := ⟨1 / ((k : ℝ) + 1), by positivity⟩
  have hc (k : ℕ) : 0 < c k := by change 0 < 1 / ((k : ℝ) + 1); positivity
  have hc0 : Tendsto (fun k => (c k : ℝ)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose A hA hmass hv using fun k => fair (c k) (hc k)
  apply fairPartition_of_convergent_masses K μ hμ φ A hA hv
    (a := μ.real K.points / n) (div_pos hK (by exact_mod_cast hn))
  intro i
  have exact_mass (k : ℕ) : μ.real (A k i).points =
      (μ.real K.points + (c k : ℝ) * ν.real K.points) / n - (c k : ℝ) * ν.real (A k i).points := by
    have h := congrArg ENNReal.toReal ((hA k).mass_eq_div
      (hμ.add_left (hν.smul_left (c k))) (hmass k) i)
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at h
    change (μ + c k • ν).real (A k i).points = (μ + c k • ν).real K.points / n at h
    rw [measureReal_add_apply, measureReal_add_apply] at h
    simp only [measureReal_nnreal_smul_apply] at h
    linarith
  have hlim : Tendsto (fun k => (c k : ℝ) * ν.real (A k i).points) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (c k).coe_nonneg measureReal_nonneg)
      (fun k => mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)) (c k).coe_nonneg)
    simpa using hc0.mul_const (ν.real univ)
  simp only [exact_mass]
  simpa using (((tendsto_const_nhds (x := μ.real K.points)).add
    (hc0.mul_const (ν.real K.points))).div_const (n : ℝ)).sub hlim

end NRR
