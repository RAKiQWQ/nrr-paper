import NRR.ProductQuantiles
import NRR.HorizontalExtension
import NRR.PrefixMoments

/-! Uniform finite layer windows and affine graph neighborhoods. -/

noncomputable section
open Set Topology Filter Metric TopologicalSpace

namespace NRR.InterfaceChart

/-- The two artificial exterior planes enclose the normalized parent. -/
def augmentWindows {r : ℕ} (v : Fin (r+1) → ℝ) : Fin (r+3) → ℝ :=
  Fin.cases (-2) (Fin.lastCases 2 v)

@[simp] theorem augmentWindows_zero {r : ℕ} (v : Fin (r+1) → ℝ) :
    augmentWindows v 0 = -2 := rfl

@[simp] theorem augmentWindows_last {r : ℕ} (v : Fin (r+1) → ℝ) :
    augmentWindows v (Fin.last (r+2)) = 2 := by
  change Fin.lastCases (motive := fun _ : Fin (r+2) => ℝ) 2 v (Fin.last (r+1)) = 2
  rw [Fin.lastCases_last]

@[simp] theorem augmentWindows_internal {r : ℕ} (v : Fin (r+1) → ℝ) (i : Fin (r+1)) :
    augmentWindows v i.castSucc.succ = v i := by simp [augmentWindows]

@[simp] theorem augmentWindows_one {r : ℕ} (v : Fin (r+1) → ℝ) :
    augmentWindows v 1 = v 0 := by
  exact augmentWindows_internal v 0

@[simp] theorem augmentWindows_penultimate {r : ℕ} (v : Fin (r+1) → ℝ) :
    augmentWindows v (Fin.last (r+1)).castSucc = v (Fin.last r) := by
  exact augmentWindows_internal v (Fin.last r)

theorem monotone_augmentWindows {r : ℕ} (v : Fin (r+1) → ℝ)
    (inside : ∀ i,-1 < v i ∧ v i < 1) (mono : Monotone v) :
    Monotone (augmentWindows v) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change augmentWindows v 0 ≤ augmentWindows v 1
    rw [augmentWindows_zero,augmentWindows_one]
    linarith [(inside 0).1]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · change augmentWindows v (Fin.last (r+1)).castSucc ≤ augmentWindows v (Fin.last (r+2))
      rw [augmentWindows_penultimate,augmentWindows_last]
      linarith [(inside (Fin.last r)).2]
    · change augmentWindows v k.castSucc.castSucc.succ ≤ augmentWindows v k.succ.castSucc.succ
      rw [augmentWindows_internal,augmentWindows_internal]
      exact mono (by change k.val ≤ k.val+1; omega)

/-- An axis witness can be chosen in every gap, including the two outside
gaps. Consequently every family is feasible even for the exterior planes. -/
theorem exists_layerWitnesses {d r : ℕ} {K : Set (Space d × ℝ)}
    (axis : ∀ z : ℝ, |z| < 1 → ((0 : Space d),z) ∈ K)
    (a b : Fin (r+1) → ℝ)
    (inside : ∀ i,-1 < a i ∧ a i ≤ b i ∧ b i < 1)
    (gaps : ∀ i j,i < j → b i < a j) :
    ∃ t : Fin (r+2) → ℝ,
      (∀ i,((0 : Space d),t i) ∈ K) ∧
      ∀ i,augmentWindows b i.castSucc < t i ∧ t i < augmentWindows a i.succ := by
  have witness (i : Fin (r+2)) : ∃ t : ℝ, |t| < 1 ∧
      augmentWindows b i.castSucc < t ∧ t < augmentWindows a i.succ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨(-1+a 0)/2,abs_lt.mpr ⟨by linarith [(inside 0).1],
        by linarith [(inside 0).2.1,(inside 0).2.2]⟩,?_,?_⟩
      · change augmentWindows b 0 < _
        rw [augmentWindows_zero]
        linarith [(inside 0).1]
      · change _ < augmentWindows a 1
        rw [augmentWindows_one]
        linarith [(inside 0).1]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · refine ⟨(b (Fin.last r)+1)/2,
          abs_lt.mpr ⟨by linarith [(inside (Fin.last r)).1,(inside (Fin.last r)).2.1],
            by linarith [(inside (Fin.last r)).2.2]⟩,?_,?_⟩
        · change augmentWindows b (Fin.last (r+1)).castSucc < _
          rw [augmentWindows_penultimate]
          linarith [(inside (Fin.last r)).2.2]
        · change _ < augmentWindows a (Fin.last (r+2))
          rw [augmentWindows_last]
          linarith [(inside (Fin.last r)).2.2]
      · have gap := gaps k.castSucc k.succ (by change k.val < k.val+1; omega)
        refine ⟨(b k.castSucc+a k.succ)/2,
          abs_lt.mpr ⟨by linarith [(inside k.castSucc).1,(inside k.castSucc).2.1],
            by linarith [(inside k.succ).2.1,(inside k.succ).2.2]⟩,?_,?_⟩
        · change augmentWindows b k.castSucc.castSucc.succ < _
          rw [augmentWindows_internal]
          linarith
        · change _ < augmentWindows a k.succ.castSucc.succ
          rw [augmentWindows_internal]
          linarith
  choose t tin below above using witness
  exact ⟨t,fun i => axis (t i) (tin i),fun i => ⟨below i,above i⟩⟩

/-- One positive tolerance simultaneously controls every slope, every
intercept window, the cylinder ends, and every gap between layers. -/
theorem exists_windowTolerance {r : ℕ} (a b : Fin (r+1) → ℝ)
    {h₀ h R : ℝ} (larger : h₀ < h) (nonnegR : 0 ≤ R)
    (inside : ∀ i,-h₀ < a i ∧ a i ≤ b i ∧ b i < h₀)
    (gaps : ∀ i j,i < j → b i < a j) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i, -h < a i-ε-ε*R ∧ b i+ε+ε*R < h) ∧
      ∀ i j,i < j → b i+ε+ε*R < a j-ε-ε*R := by
  let f : Option (Fin (r+1) × Fin (r+1)) → ℝ
    | none => (h-h₀)/(2*(R+1))
    | some ij => if ij.1 < ij.2 then (a ij.2-b ij.1)/(4*(R+1)) else 1
  have positive : ∀ x,0 < f x := by
    rintro (_ | ⟨i,j⟩)
    · exact div_pos (sub_pos.mpr larger) (by positivity)
    · dsimp [f]
      split_ifs with hij
      · exact div_pos (sub_pos.mpr (gaps i j hij)) (by positivity)
      · exact zero_lt_one
  obtain ⟨ε,hε,small⟩ := NRR.ProductQuantiles.exists_uniform_positive f positive
  have hsmall : ε*(2*(R+1)) < h-h₀ :=
    (lt_div_iff₀ (by positivity : 0 < 2*(R+1))).mp (small none)
  have productPos : 0 < ε*(R+1) := mul_pos hε (by linarith)
  refine ⟨ε,hε,fun i => ⟨by nlinarith [(inside i).1],by nlinarith [(inside i).2.2]⟩,?_⟩
  intro i j hij
  have sm : ε < (a j-b i)/(4*(R+1)) := by
    simpa only [f,if_pos hij] using small (some (i,j))
  have mul := (lt_div_iff₀ (by positivity : 0 < 4*(R+1))).mp sm
  nlinarith

def augmentParameters {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    Fin (r+3) → Parameters d := Fin.cases (0,-2) (Fin.lastCases (0,2) P)

@[simp] theorem augmentParameters_zero {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    augmentParameters P 0 = (0,-2) := rfl

@[simp] theorem augmentParameters_last {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    augmentParameters P (Fin.last (r+2)) = (0,2) := by
  change Fin.lastCases (motive := fun _ : Fin (r+2) => Parameters d)
    (0,2) P (Fin.last (r+1)) = (0,2)
  rw [Fin.lastCases_last]

@[simp] theorem augmentParameters_internal {d r : ℕ} (P : Fin (r+1) → Parameters d)
    (i : Fin (r+1)) : augmentParameters P i.castSucc.succ = P i := by
  simp [augmentParameters]

@[simp] theorem augmentParameters_one {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    augmentParameters P 1 = P 0 := augmentParameters_internal P 0

@[simp] theorem augmentParameters_penultimate {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    augmentParameters P (Fin.last (r+1)).castSucc = P (Fin.last r) :=
  augmentParameters_internal P (Fin.last r)

theorem augmentParameters_mem_boxes {d r : ℕ} (P : Fin (r+1) → Parameters d)
    (a b : Fin (r+1) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (boxes : ∀ i,P i ∈ parameterBox d ε (a i) (b i)) :
    ∀ i,augmentParameters P i ∈ parameterBox d ε (augmentWindows a i) (augmentWindows b i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [augmentParameters_zero,augmentWindows_zero,augmentWindows_zero]
    exact ⟨by simpa using hε,le_rfl,le_rfl⟩
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · change augmentParameters P (Fin.last (r+2)) ∈ parameterBox d ε
        (augmentWindows a (Fin.last (r+2))) (augmentWindows b (Fin.last (r+2)))
      rw [augmentParameters_last,augmentWindows_last,augmentWindows_last]
      exact ⟨by simpa using hε,le_rfl,le_rfl⟩
    · rw [augmentParameters_internal,augmentWindows_internal,augmentWindows_internal]
      exact boxes k

theorem suffixCells_last {d r : ℕ}
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)) :
    suffixCells S (Fin.last (r+1)) = (S (Fin.last (r+1)) : Set (Space d × ℝ)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have eq : j.val = Fin.last (r+1) := le_antisymm (Fin.le_last _) j.property
    simpa only [eq] using hj
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨Fin.last (r+1),le_rfl⟩,hx⟩

/-- The first and last cells are recovered using exterior sentinel planes;
the same exact slab formula now holds for every cell in the chain. -/
theorem cell_eq_extended_clippedSlab {d r : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)} (part : ChainPartition K S)
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1) (P : Fin (r+1) → Parameters d)
    (caps : ∀ i,prefixCells S i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
      suffixCells S i.succ = K ∩ {x | height (P i) x.1 ≤ x.2}) :
    ∀ i,(S i : Set (Space d × ℝ)) =
      clippedSlab K (augmentParameters P i.castSucc) (augmentParameters P i.succ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have cap := (caps 0).1
    change prefixCells S 0 = _ at cap
    rw [prefixCells_zero] at cap
    change (S 0 : Set (Space d × ℝ)) = clippedSlab K (augmentParameters P 0) (augmentParameters P 1)
    rw [augmentParameters_zero,augmentParameters_one,cap]
    ext x
    change (x ∈ K ∧ x.2 ≤ height (P 0) x.1) ↔
      x ∈ K ∧ (0 : Space d →L[ℝ] ℝ) x.1+(-2) ≤ x.2 ∧ x.2 ≤ height (P 0) x.1
    constructor
    · rintro ⟨hx,ht⟩
      exact ⟨hx,by simp only [ContinuousLinearMap.zero_apply,zero_add]; linarith [(strip hx).2.1],ht⟩
    · exact fun hx => ⟨hx.1,hx.2.2⟩
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · have cap := (caps (Fin.last r)).2
      change suffixCells S (Fin.last (r+1)) = _ at cap
      rw [suffixCells_last] at cap
      change (S (Fin.last (r+1)) : Set (Space d × ℝ)) =
        clippedSlab K (augmentParameters P (Fin.last (r+1)).castSucc)
          (augmentParameters P (Fin.last (r+2)))
      rw [augmentParameters_penultimate,augmentParameters_last,cap]
      ext x
      change (x ∈ K ∧ height (P (Fin.last r)) x.1 ≤ x.2) ↔
        x ∈ K ∧ height (P (Fin.last r)) x.1 ≤ x.2 ∧ x.2 ≤ (0 : Space d →L[ℝ] ℝ) x.1+2
      constructor
      · rintro ⟨hx,ht⟩
        exact ⟨hx,ht,by simp only [ContinuousLinearMap.zero_apply,zero_add]; linarith [(strip hx).2.2]⟩
      · exact fun hx => ⟨hx.1,hx.2.1⟩
    · change (S k.castSucc.succ : Set (Space d × ℝ)) =
        clippedSlab K (augmentParameters P k.castSucc.castSucc.succ)
          (augmentParameters P k.succ.castSucc.succ)
      rw [augmentParameters_internal,augmentParameters_internal]
      exact cell_eq_clippedSlab_of_graph_caps part P caps k.castSucc k.succ rfl

theorem mem_slabFamily_of_representation {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K)
    (C : ConvexLimits.ConvexCompact (Space d × ℝ)) (p q : Parameters d)
    {ε a b c e t : ℝ} (axis : ((0 : Space d),t) ∈ K) (lower : b < t) (upper : t < c)
    (hp : p ∈ parameterBox d ε a b) (hq : q ∈ parameterBox d ε c e)
    (repr : ConvexLimits.points C = clippedSlab K p q) :
    C ∈ slabFamily compact convex ε a b c e := by
  have feasible : ∃ y ∈ K,height p y.1 < y.2 ∧ y.2 < height q y.1 := by
    refine ⟨(0,t),axis,?_,?_⟩
    · simpa only [height,map_zero,zero_add] using hp.2.2.trans_lt lower
    · simpa only [height,map_zero,zero_add] using upper.trans_le hq.2.1
  refine ⟨⟨(p,q),feasible⟩,⟨hp,hq⟩,?_⟩
  exact Subtype.ext (NonemptyCompacts.ext repr.symm)

theorem cells_mem_slabFamilies {d r : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K)
    (S : Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ))
    (part : ChainPartition K (fun i => (S i).val))
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    (P : Fin (r+1) → Parameters d) (a b : Fin (r+1) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (boxes : ∀ i,P i ∈ parameterBox d ε (a i) (b i))
    (caps : ∀ i,prefixCells (fun j => (S j).val) i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
      suffixCells (fun j => (S j).val) i.succ = K ∩ {x | height (P i) x.1 ≤ x.2})
    (t : Fin (r+2) → ℝ) (axis : ∀ i,((0 : Space d),t i) ∈ K)
    (between : ∀ i,augmentWindows b i.castSucc < t i ∧ t i < augmentWindows a i.succ) :
    ∀ i,S i ∈ slabFamily compact convex ε
      (augmentWindows a i.castSucc) (augmentWindows b i.castSucc)
      (augmentWindows a i.succ) (augmentWindows b i.succ) := by
  intro i
  exact mem_slabFamily_of_representation compact convex (S i)
    (augmentParameters P i.castSucc) (augmentParameters P i.succ)
    (axis i) (between i).1 (between i).2
    (augmentParameters_mem_boxes P a b hε boxes i.castSucc)
    (augmentParameters_mem_boxes P a b hε boxes i.succ)
    (cell_eq_extended_clippedSlab part strip P caps i)

theorem mem_parameterBox_of_near_horizontal {d : ℕ} {p : Parameters d}
    {a b t ε : ℝ} (ht : t ∈ Icc a b) (near : dist p (0,t) < ε) :
    p ∈ parameterBox d ε (a-ε) (b+ε) := by
  have slope : ‖p.1‖ < ε := by
    have H := (le_max_left (dist p.1 0) (dist p.2 t)).trans_lt near
    simpa only [dist_zero_right] using H
  have intercept : |p.2-t| < ε := by
    exact (le_max_right (dist p.1 0) (dist p.2 t)).trans_lt near
  refine ⟨by simpa only [mem_closedBall,dist_zero_right] using slope.le,?_⟩
  obtain ⟨lower,upper⟩ := abs_lt.mp intercept
  exact ⟨by linarith [ht.1],by linarith [ht.2]⟩

def WindowedChain {d r : ℕ} (K : Set (Space d × ℝ))
    (a b : Fin (r+1) → ℝ) (ε : ℝ)
    (S : Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ)) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (r+2))) (P : Fin (r+1) → Parameters d),
    ChainPartition K (fun i => (S (σ i)).val) ∧
      (∀ i,P i ∈ parameterBox d ε (a i-ε) (b i+ε)) ∧
      ∀ i,prefixCells (fun j => (S (σ j)).val) i.castSucc =
          K ∩ {x | x.2 ≤ height (P i) x.1} ∧
        suffixCells (fun j => (S (σ j)).val) i.succ =
          K ∩ {x | height (P i) x.1 ≤ x.2}

/-- A single open neighborhood works for every horizontal equal-mass
reference configuration. The only mass input identifies the exact
horizontal prefix cuts with their already constructed quantile windows. -/
theorem exists_open_windowedChains {d r : ℕ} {K : Set (Space d × ℝ)}
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {L H : ℝ}
    (inner : D ×ˢ Icc L H ⊆ K)
    (s : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ)))
    (parts : ∀ S ∈ s,ConvexPartition K (fun i => (S i).val))
    (a b : Fin (r+1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (quantiles : ∀ S ∈ s,∀ (σ : Equiv.Perm (Fin (r+2))) (t : Fin (r+1) → ℝ),
      (∀ i,prefixCells (fun j => (S (σ j)).val) i.castSucc = K ∩ {x | x.2 ≤ t i}) →
      ∀ i,t i ∈ Icc (a i) (b i)) :
    ∃ U : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ)),
      IsOpen U ∧
      (∀ S ∈ s,(∀ i,∃ lo hi : ℝ,lo < hi ∧
        ConvexLimits.points (S i) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc lo hi) → S ∈ U) ∧
      ∀ S ∈ U,ConvexPartition K (fun i => (S i).val) → WindowedChain K a b ε S := by
  classical
  let refs := {S ∈ s | ∀ i,∃ lo hi : ℝ,lo < hi ∧
    ConvexLimits.points (S i) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc lo hi}
  let forget := fun S : Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ) =>
    fun i => (S i).val
  have continuousForget : Continuous forget :=
    continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
  have localChart (S : refs) :
      ∃ V : Set (Fin (r+2) → ConvexLimits.ConvexCompact (Space d × ℝ)),
        IsOpen V ∧ S.val ∈ V ∧
        ∀ T ∈ V,ConvexPartition K (forget T) → WindowedChain K a b ε T := by
    choose lo hi positive clips using S.property.2
    obtain ⟨σ,V,hV,memV,caps,chart⟩ :=
      NRR.HorizontalExtension.slab_partition_has_unlabelled_chart_with_caps hD
        (forget S.val) (parts S.val S.property.1) lo hi positive clips inner hε
    have levels := quantiles S.val S.property.1 σ (fun i => hi (σ i.castSucc)) caps
    refine ⟨forget ⁻¹' V,hV.preimage continuousForget,memV,?_⟩
    intro T hT part
    obtain ⟨P,chain,near,capsT⟩ := chart (forget T) hT part
    exact ⟨σ,P,chain,fun i => mem_parameterBox_of_near_horizontal (levels i) (near i),capsT⟩
  choose V hV inV charts using localChart
  let U := ⋃ S : refs,V S
  refine ⟨U,isOpen_iUnion hV,?_,?_⟩
  · intro S hS slabs
    exact mem_iUnion.mpr ⟨⟨S,hS,slabs⟩,inV ⟨S,hS,slabs⟩⟩
  · intro S hS part
    obtain ⟨R,hR⟩ := mem_iUnion.mp hS
    exact charts R S hR part

end NRR.InterfaceChart
