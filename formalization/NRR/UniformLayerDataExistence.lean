import NRR.LayerCounterexample

/-! Construction of the complete geometric layer data from the actual
quantile intervals and a sufficiently long inner localization cylinder. -/

noncomputable section
open Set Topology MeasureTheory Metric TopologicalSpace
open NRR.Coordinates NRR.InterfaceChart

namespace NRR.Localization

theorem exists_uniformLayerData_of_windows {d r : ℕ} (hr : 0 < r)
    (K : ConvexBody (Space d × ℝ)) (μ : Measure (Space d × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (strip : bodyPoints K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    (axisK : ∀ z : ℝ,|z| < 1 → ((0 : Space d),z) ∈ bodyPoints K)
    (A : MomentCylinder K μ (r+2)) {h₀ : ℝ} (larger : h₀ < A.h)
    (a₀ b₀ : Fin (r+1) → ℝ)
    (inside : ∀ i,-h₀ < a₀ i ∧ a₀ i ≤ b₀ i ∧ b₀ i < h₀)
    (gaps : ∀ i j,i < j → b₀ i < a₀ j)
    (levels : ∀ i,{t | ProductQuantiles.cumulative (bodyPoints K) μ t =
      (i.val+1 : ℝ)*(μ.real (bodyPoints K)/(r+2))} = Icc (a₀ i) (b₀ i)) :
    Nonempty (UniformLayerData K μ A) := by
  obtain ⟨ε,hε,ends,gapBounds⟩ := exists_windowTolerance a₀ b₀ larger A.radius_pos.le inside gaps
  let α : Fin (r+1) → ℝ := fun i => a₀ i-ε
  let β : Fin (r+1) → ℝ := fun i => b₀ i+ε
  have nonneg : 0 ≤ ε*A.a := mul_nonneg hε.le A.radius_pos.le
  have expandedInside : ∀ i,-1 < α i ∧ α i ≤ β i ∧ β i < 1 := by
    intro i
    dsimp [α,β]
    exact ⟨by linarith [(ends i).1,A.height_lt_one],by linarith [(inside i).2.1],
      by linarith [(ends i).2,A.height_lt_one]⟩
  have expandedGaps : ∀ i j,i < j → β i < α j := by
    intro i j hij
    dsimp [α,β]
    linarith [gapBounds i j hij]
  have mono : Monotone α := by
    intro i j hij
    by_cases he : i = j
    · exact he ▸ le_rfl
    · have lt : i < j := lt_of_le_of_ne hij he
      have H := expandedGaps i j lt
      exact (expandedInside i).2.1.trans H.le
  have ordered := monotone_augmentWindows α
    (fun i => ⟨(expandedInside i).1,((expandedInside i).2.1.trans_lt (expandedInside i).2.2)⟩) mono
  obtain ⟨t,axis,between⟩ := exists_layerWitnesses axisK α β expandedInside expandedGaps
  let i₁ : Fin (r+1) := ⟨1,by omega⟩
  have zlt : (0 : Fin (r+1)) < i₁ := by change (0 : ℕ) < 1; omega
  have two (v : Fin (r+1) → ℝ) : augmentWindows v 2 = v i₁ :=
    augmentWindows_internal v i₁
  have twoP (P : Fin (r+1) → Parameters d) : augmentParameters P 2 = P i₁ :=
    augmentParameters_internal P i₁
  have bounds : ∀ p ∈ admissibleBox (bodyPoints K) ε
      (augmentWindows α 1) (augmentWindows β 1) (augmentWindows α 2) (augmentWindows β 2),
      ∀ u ∈ closedBall (0 : Space d) A.a,
        -A.h ≤ height p.val.1 u ∧ height p.val.1 u ≤ height p.val.2 u ∧
          height p.val.2 u ≤ A.h := by
    intro p hp u hu
    rw [augmentWindows_one,augmentWindows_one,two,two] at hp
    have normu : ‖u‖ ≤ A.a := by simpa only [mem_closedBall,dist_zero_right] using hu
    have lower := height_bounds_of_parameterBox hε.le hp.1 normu
    have upper := height_bounds_of_parameterBox hε.le hp.2 normu
    have E₀ := ends 0
    have E₁ := ends i₁
    have G := gapBounds 0 i₁ zlt
    dsimp [α,β] at lower upper
    exact ⟨by linarith,by linarith,by linarith⟩
  have hD : (0 : Space d) ∈ interior (closedBall (0 : Space d) A.a) :=
    ball_subset_interior_closedBall (mem_ball_self A.radius_pos)
  have inner : closedBall (0 : Space d) A.a ×ˢ Icc (-A.h) A.h ⊆ bodyPoints K :=
    A.inner.trans interior_subset
  obtain ⟨U,hU,slabs,chains⟩ := exists_equalMass_windowed_neighborhood K μ hμ hD inner
    a₀ b₀ levels hε
  refine ⟨⟨ε,augmentWindows α,augmentWindows β,t,ordered,axis,between,bounds,
    U,hU,slabs,?_⟩⟩
  intro S hS hSU
  obtain ⟨σ,P,chain,boxes,caps⟩ := chains S hS hSU
  have members := cells_mem_slabFamilies K.val.isCompact K.property.1
    (fun i => bodyToConvexCompact (S (σ i))) chain strip P α β hε.le boxes caps t axis between
  have feasible : ∃ y ∈ bodyPoints K,height (P 0) y.1 < y.2 ∧ height (P i₁) y.1 > y.2 := by
    refine ⟨(0,t 1),axis 1,?_,?_⟩
    · have B := (boxes 0).2.2
      have T := (between 1).1
      change augmentWindows β 1 < t 1 at T
      rw [augmentWindows_one] at T
      simpa only [height,map_zero,zero_add] using B.trans_lt T
    · have B := (boxes i₁).2.1
      have T := (between 1).2
      change t 1 < augmentWindows α 2 at T
      rw [two] at T
      simpa only [height,map_zero,zero_add] using T.trans_le B
  let p : FeasibleParameters (bodyPoints K) := ⟨(P 0,P i₁),feasible⟩
  have hp : p ∈ admissibleBox (bodyPoints K) ε
      (augmentWindows α 1) (augmentWindows β 1) (augmentWindows α 2) (augmentWindows β 2) := by
    rw [augmentWindows_one,augmentWindows_one,two,two]
    exact ⟨boxes 0,boxes i₁⟩
  refine ⟨σ,members,p,hp,?_,?_,?_⟩
  · apply Subtype.ext
    apply NonemptyCompacts.ext
    have H := cell_eq_extended_clippedSlab chain strip P caps (1 : Fin (r+2))
    change bodyPoints (S (σ 1)) = clippedSlab (bodyPoints K)
      (augmentParameters P 1) (augmentParameters P 2) at H
    rw [augmentParameters_one,twoP] at H
    exact H
  · have H := (caps 0).1
    change prefixCells (fun i => (S (σ i)).val) 0 = bodyPoints K ∩ belowGraph (P 0) at H
    exact H
  · have H := (caps i₁).1
    change prefixCells (fun i => (S (σ i)).val) 1 = bodyPoints K ∩ belowGraph (P i₁) at H
    exact H

/-- Every normalized prescribed body and absolutely continuous positive
mass admits a localization cylinder and complete uniform layer data. -/
theorem exists_momentCylinder_uniformLayerData {d r : ℕ} (hr : 0 < r)
    (K : ConvexBody (Space d × ℝ)) (μ : Measure (Space d × ℝ))
    [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (strip : bodyPoints K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    (axis : ∀ z : ℝ,|z| < 1 → ((0 : Space d),z) ∈ interior (bodyPoints K)) :
    ∃ A : MomentCylinder K μ (r+2),Nonempty (UniformLayerData K μ A) := by
  have realMass : 0 < μ.real (bodyPoints K) := ENNReal.toReal_pos hK.ne' (measure_ne_top _ _)
  obtain ⟨hmin,_,hminlt,a,b,windows,gaps⟩ :=
    ProductQuantiles.ordered_quantile_windows_bounded (r := r) (bodyPoints K) μ hμ strip realMass
  obtain ⟨A,larger⟩ := exists_momentCylinder_above (n := r+2) K μ hμ hK strip axis hminlt
  exact ⟨A,exists_uniformLayerData_of_windows hr K μ hμ strip
    (fun z hz => interior_subset (axis z hz)) A larger a b
    (fun i => ⟨(windows i).1,(windows i).2.1,(windows i).2.2.1⟩) gaps
    (fun i => (windows i).2.2.2)⟩

end NRR.Localization
