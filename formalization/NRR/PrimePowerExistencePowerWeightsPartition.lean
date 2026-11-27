import NRR.PrimePowerExistencePowerWeightsContinuous

/-! The continuous equivariant family of actual equal-mass convex bodies
obtained from the power weights. -/

noncomputable section
open Set MeasureTheory Filter Topology Metric TopologicalSpace

namespace NRR.PrimePower

variable {d n : ℕ} [NeZero n]

theorem body_eq_of_subset_equal_mass (K A B : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (background : volume.restrict K.points ≪ μ)
    (sub : A.points ⊆ B.points) (inside : B.points ⊆ K.points)
    (same : μ.real A.points = μ.real B.points) : A = B := by
  have sameM : μ A.points = μ B.points :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp same
  have diffNull : μ (B.points \ A.points) = 0 := by
    rw [measure_diff sub A.val.isCompact.isClosed.measurableSet.nullMeasurableSet
      (measure_ne_top _ _),sameM,tsub_self]
  have rev : B.points ⊆ A.points := by
    intro x hx
    by_contra absent
    have hc : x ∈ closure (interior B.points) := by
      change x ∈ closure (interior (B.val : Set (Space d)))
      rwa [B.property.1.closure_interior_eq_closure_of_nonempty_interior B.property.2,
        B.val.isCompact.isClosed.closure_eq]
    obtain ⟨y,hyA,hyB⟩ := mem_closure_iff.mp hc A.pointsᶜ A.val.isCompact.isClosed.isOpen_compl absent
    let U := interior B.points \ A.points
    have openU : IsOpen U := isOpen_interior.sdiff A.val.isCompact.isClosed
    have nonemptyU : U.Nonempty := ⟨y,hyB,hyA⟩
    have nullU : μ U = 0 := measure_mono_null
      (show U ⊆ B.points \ A.points from fun _ hq => ⟨interior_subset hq.1,hq.2⟩) diffNull
    have haarNull := background nullU
    rw [Measure.restrict_apply openU.measurableSet,
      inter_eq_self_of_subset_left (show U ⊆ K.points from
        fun _ hq => inside (interior_subset hq.1))] at haarNull
    exact (openU.measure_pos volume nonemptyU).ne' haarNull
  apply Subtype.ext
  apply NonemptyCompacts.ext
  exact Subset.antisymm sub rev

theorem powerCell_limit_subset (K : Body d) (xs : ℕ → Configuration d n)
    (ws : ℕ → Fin n → ℝ) (D : Body d) (Ds : ℕ → Body d)
    (x : Configuration d n) (w : Fin n → ℝ) (i : Fin n)
    (nearX : Tendsto xs atTop (𝓝 x)) (nearW : Tendsto ws atTop (𝓝 w))
    (nearD : Tendsto Ds atTop (𝓝 D))
    (cells : ∀ k, (Ds k).points = powerCell K (xs k) (ws k) i) :
    D.points ⊆ powerCell K x w i := by
  intro y hy
  have hc : Tendsto (fun k => (Ds k).val) atTop (𝓝 D.val) :=
    (continuous_subtype_val.tendsto D).comp nearD
  obtain ⟨ys,inDs,nearY⟩ := CompactTests.approximate_point hc hy
  have memC (k) : ys k ∈ powerCell K (xs k) (ws k) i := cells k ▸ inDs k
  have inside : y ∈ K.points := K.val.isCompact.isClosed.mem_of_tendsto nearY
    (Eventually.of_forall fun k => (memC k).1)
  have nx : Tendsto (fun k => (xs k).val) atTop (𝓝 x.val) :=
    (continuous_subtype_val.tendsto x).comp nearX
  have scoreLimit (j : Fin n) :
      Tendsto (fun k => powerScore (xs k) (ws k) j (ys k)) atTop (𝓝 (powerScore x w j y)) := by
    exact ((tendsto_pi_nhds.mp nx j).inner nearY).add (tendsto_pi_nhds.mp nearW j)
  apply (mem_powerCell_iff K x w i y).mpr
  refine ⟨inside,fun j => ?_⟩
  exact le_of_tendsto_of_tendsto (scoreLimit j) (scoreLimit i)
    (Eventually.of_forall fun k => ((mem_powerCell_iff K (xs k) (ws k) i (ys k)).mp (memC k)).2 j)

def normalizedPowerBody (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (mass : 0 < μ K.points) (x : Configuration d n) (i : Fin n) : Body d :=
  powerBody K x (normalizedPowerWeights K μ hμ x) μ hμ
    (positive_powerCell_of_equalMass K μ mass x _ (normalizedPowerWeights_mass K μ hμ x)) i

theorem normalizedPowerBody_points (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (mass : 0 < μ K.points) (x : Configuration d n) (i : Fin n) :
    (normalizedPowerBody K μ hμ mass x i).points =
      powerCell K x (normalizedPowerWeights K μ hμ x) i := rfl

theorem normalizedPowerBody_partition (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (mass : 0 < μ K.points) (x : Configuration d n) :
    BodyPartition K (normalizedPowerBody K μ hμ mass x) :=
  powerBody_partition (Nat.pos_of_ne_zero (NeZero.ne n)) K x _ μ hμ
    (positive_powerCell_of_equalMass K μ mass x _ (normalizedPowerWeights_mass K μ hμ x))

theorem normalizedPowerBody_equalMass (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (mass : 0 < μ K.points) (x : Configuration d n) :
    EqualMass μ (normalizedPowerBody K μ hμ mass x) := by
  intro i j
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (normalizedPowerWeights_mass K μ hμ x i).trans (normalizedPowerWeights_mass K μ hμ x j).symm

theorem continuous_body_mass (μ : Measure (Space d)) [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    Continuous (fun D : Body d => μ.real D.points) := by
  have cb : Continuous (Body.toCompactConvex (d := d)) := continuous_subtype_val.subtype_mk _
  simpa only [Function.comp_def,Moments.points,Body.toCompactConvex,Body.points,
    setIntegral_one_eq_measureReal] using
    (Moments.continuous_integral μ hμ (integrable_const (1 : ℝ))).comp cb

theorem continuous_normalizedPowerBody (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (i : Fin n) :
    Continuous (fun x : Configuration d n => normalizedPowerBody K μ hμ mass x i) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro xs x near
  let m : ℝ := μ.real K.points / n
  have hm : 0 < m := div_pos (ENNReal.toReal_pos mass.ne' (measure_ne_top _ _))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  let family := {D : Body d | D.points ⊆ K.points ∧ ENNReal.ofReal m ≤ μ D.points}
  have compact : IsCompact family := CompactTests.compact_cells K μ hμ (ENNReal.ofReal_pos.mpr hm)
  have inside (k) : normalizedPowerBody K μ hμ mass (xs k) i ∈ family := by
    refine ⟨inter_subset_left,?_⟩
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
    exact (normalizedPowerWeights_mass K μ hμ (xs k) i).ge
  apply compact.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall inside)
  intro D _ cluster
  obtain ⟨σ,hσ,limit⟩ := FirstCountableTopology.tendsto_subseq cluster
  have nx := near.comp hσ.tendsto_atTop
  have nw := ((continuous_normalizedPowerWeights K μ hμ background mass).tendsto x).comp nx
  have subset : D.points ⊆ (normalizedPowerBody K μ hμ mass x i).points :=
    powerCell_limit_subset K (xs ∘ σ) (fun k => normalizedPowerWeights K μ hμ (xs (σ k))) D
      (fun k => normalizedPowerBody K μ hμ mass (xs (σ k)) i) x _ i nx nw limit (fun _ => rfl)
  have md : μ.real D.points = m := by
    have hl := ((continuous_body_mass μ hμ).tendsto D).comp limit
    apply tendsto_nhds_unique hl
    simpa only [Function.comp_def,normalizedPowerBody_points,normalizedPowerWeights_mass,m] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => m) atTop (𝓝 m))
  exact body_eq_of_subset_equal_mass K D (normalizedPowerBody K μ hμ mass x i) μ background subset
    inter_subset_left (md.trans (normalizedPowerWeights_mass K μ hμ x i).symm)

theorem normalizedPowerBody_relabel (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (σ : Equiv.Perm (Fin n)) (x : Configuration d n) (i : Fin n) :
    normalizedPowerBody K μ hμ mass (σ • x) i =
      normalizedPowerBody K μ hμ mass x (σ.symm i) := by
  let w := normalizedPowerWeights K μ hμ x
  let v := normalizedPowerWeights K μ hμ (σ • x)
  have equalW (j) : μ.real (powerCell K (σ • x) (fun k => w (σ.symm k)) j) =
      μ.real K.points / n := by
    rw [powerCell_relabel]
    exact normalizedPowerWeights_mass K μ hμ x (σ.symm j)
  have he := powerCell_eq_of_equalMass K μ hμ background mass (σ • x) v
    (fun k => w (σ.symm k)) (normalizedPowerWeights_mass K μ hμ (σ • x)) equalW i
  rw [powerCell_relabel] at he
  apply Subtype.ext
  apply NonemptyCompacts.ext
  exact he

/-- An actual continuous equivariant family of positive equal-mass convex
power cells on every distinct-site configuration. -/
def equalMassPowerFamily (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (i : Fin n) : C(Configuration d n,Body d) :=
  ⟨fun x => normalizedPowerBody K μ hμ mass x i,
    continuous_normalizedPowerBody K μ hμ background mass i⟩

def equalMassPowerTest (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (φ : Fin (d-1) → C(CompactConvex d,ℝ)) :
    C(Configuration d n,ReducedValues d n) :=
  testMap (Nat.pos_of_ne_zero (NeZero.ne n)) φ (equalMassPowerFamily K μ hμ background mass)

theorem equalMassPowerTest_equivariant (K : Body d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (φ : Fin (d-1) → C(CompactConvex d,ℝ))
    (σ : Equiv.Perm (Fin n)) (x : Configuration d n) :
    equalMassPowerTest K μ hμ background mass φ (σ • x) =
      σ • equalMassPowerTest K μ hμ background mass φ x :=
  testMap_equivariant (Nat.pos_of_ne_zero (NeZero.ne n)) φ
    (equalMassPowerFamily K μ hμ background mass)
    (fun σ i x => normalizedPowerBody_relabel K μ hμ background mass σ x i) σ x

theorem fairPartition_of_equalMassPowerTest_zero (K : Body d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (background : volume.restrict K.points ≪ μ)
    (mass : 0 < μ K.points) (φ : Fin (d-1) → C(CompactConvex d,ℝ))
    (x : Configuration d n) (zero : equalMassPowerTest K μ hμ background mass φ x = 0) :
    ∃ S : Fin n → Body d, BodyPartition K S ∧ EqualMass μ S ∧
      ∀ k i j, φ k (S i).toCompactConvex = φ k (S j).toCompactConvex :=
  fairPartition_of_testMap_zero (Nat.pos_of_ne_zero (NeZero.ne n)) K μ φ
    (equalMassPowerFamily K μ hμ background mass) x
    (normalizedPowerBody_partition K μ hμ mass x)
    (normalizedPowerBody_equalMass K μ hμ mass x) zero

end NRR.PrimePower
