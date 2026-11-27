import NRR.PrimePowerTopologyCompactification

/-! The actual lowest Fuks skeleton consists of closed Euclidean strata.
Their one-point compactifications embed as spheres in the compactified
configuration space and meet one another only at the common point at infinity. -/

noncomputable section
open Set Topology Filter
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

def verticalCellSet (d n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Configuration (d+1) n) :=
  {x | x ∈ verticalSet d n ∧ Monotone (fun i => (horizontalHeight d (x.val (σ i))).2)}

theorem isClosed_verticalCellSet (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsClosed (verticalCellSet d n σ) := by
  have repr : verticalCellSet d n σ = verticalSet d n ∩ ⋂ i : Fin n,⋂ j : Fin n,
      {x : Configuration (d+1) n | i ≤ j →
        (horizontalHeight d (x.val (σ i))).2 ≤ (horizontalHeight d (x.val (σ j))).2} := by
    ext x
    simp only [verticalCellSet,mem_setOf_eq,mem_inter_iff,mem_iInter,Monotone]
  rw [repr]
  apply (isClosed_verticalSet d n).inter
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  by_cases hij : i ≤ j
  · simpa only [hij,true_implies] using isClosed_le
      (continuous_snd.comp ((horizontalHeight d).continuous.comp
        ((continuous_apply (σ i)).comp continuous_subtype_val)))
      (continuous_snd.comp ((horizontalHeight d).continuous.comp
        ((continuous_apply (σ j)).comp continuous_subtype_val)))
  · simp only [hij,false_implies,setOf_true,isClosed_univ]

theorem verticalCell_strictOrder {d n : ℕ} {σ : Equiv.Perm (Fin n)}
    {x : Configuration (d+1) n} (hx : x ∈ verticalCellSet d n σ) :
    (fun i => (horizontalHeight d (x.val i)).2) ∈ heightChamber n σ := by
  apply hx.2.strictMono_of_injective
  intro i j he
  apply σ.injective
  apply x.property
  apply (horizontalHeight d).injective
  exact Prod.ext (hx.1 (σ i) (σ j)) he

theorem verticalCellSets_pairwise_disjoint (d n : ℕ) :
    Pairwise fun σ τ : Equiv.Perm (Fin n) =>
      Disjoint (verticalCellSet d n σ) (verticalCellSet d n τ) := by
  intro σ τ hne
  apply Set.disjoint_left.mpr
  intro x hs ht
  exact hne (heightChamber_unique (verticalCell_strictOrder hs) (verticalCell_strictOrder ht))

theorem verticalSet_eq_iUnion_cells {d n : ℕ} (i₀ : Fin n) :
    verticalSet d n = ⋃ σ : Equiv.Perm (Fin n),verticalCellSet d n σ := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ,sorted,_⟩ := exists_unique_heightChamber ((verticalCoordinates i₀ ⟨x,hx⟩).2)
    exact mem_iUnion.mpr ⟨σ,hx,sorted.monotone⟩
  · intro hx
    obtain ⟨σ,hσ⟩ := mem_iUnion.mp hx
    exact hσ.1

def verticalCellCoordinates {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    verticalCellSet d n σ ≃ₜ Space d × heightChamber n σ where
  toFun x := ((horizontalHeight d (x.val.val i₀)).1,
    ⟨fun i => (horizontalHeight d (x.val.val i)).2,verticalCell_strictOrder x.property⟩)
  invFun p := ⟨⟨fun i => (horizontalHeight d).symm (p.1,p.2.val i),by
    intro i j he
    apply heightChamber_injective p.2.property
    have H := congrArg (fun z => (horizontalHeight d z).2) he
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using H⟩,
    (by intro i j; simp only [ContinuousLinearEquiv.apply_symm_apply]),
    by simpa only [ContinuousLinearEquiv.apply_symm_apply] using p.2.property.monotone⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply (horizontalHeight d).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (x.property.1 i₀ i) rfl
  right_inv p := by
    apply Prod.ext
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
    · apply Subtype.ext
      funext i
      simp only [ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := by
    have cont (i : Fin n) : Continuous (fun x : verticalCellSet d n σ =>
        horizontalHeight d (x.val.val i)) :=
      (horizontalHeight d).continuous.comp
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
    exact (continuous_fst.comp (cont i₀)).prodMk
      ((continuous_pi fun i => continuous_snd.comp (cont i)).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (horizontalHeight d).symm.continuous.comp
      (continuous_fst.prodMk ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

def verticalCellEmbedding {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    C(Space d × heightChamber n σ,Configuration (d+1) n) :=
  ⟨fun p => ((verticalCellCoordinates i₀ σ).symm p).val,
    continuous_subtype_val.comp (verticalCellCoordinates i₀ σ).symm.continuous⟩

theorem isClosedEmbedding_verticalCell {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    IsClosedEmbedding (verticalCellEmbedding (d := d) i₀ σ) :=
  (isClosed_verticalCellSet d n σ).isClosedEmbedding_subtypeVal.comp
    (verticalCellCoordinates i₀ σ).symm.isClosedEmbedding

def compactifiedVerticalCell {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    C(OnePoint (Space d × heightChamber n σ),OnePoint (Configuration (d+1) n)) := by
  refine ⟨OnePoint.map (verticalCellEmbedding i₀ σ),OnePoint.continuous_map
    (verticalCellEmbedding i₀ σ).continuous ?_⟩
  rw [coclosedCompact_eq_cocompact,coclosedCompact_eq_cocompact]
  exact (isClosedEmbedding_verticalCell i₀ σ).tendsto_cocompact

theorem isClosedEmbedding_compactifiedVerticalCell {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    IsClosedEmbedding (compactifiedVerticalCell (d := d) i₀ σ) :=
  (compactifiedVerticalCell i₀ σ).continuous.isClosedEmbedding
    (Option.map_injective (isClosedEmbedding_verticalCell i₀ σ).injective)

def minimalSkeleton (d n : ℕ) : Set (OnePoint (Configuration (d+1) n)) :=
  {∞} ∪ ((↑) '' verticalSet d n)

theorem compactifiedVerticalCell_range {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    range (compactifiedVerticalCell (d := d) i₀ σ) =
      {∞} ∪ ((↑) '' verticalCellSet d n σ) := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    induction p using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe p => exact Or.inr ⟨(verticalCellEmbedding i₀ σ) p,
        ((verticalCellCoordinates i₀ σ).symm p).property,rfl⟩
  · rintro (hx | ⟨y,hy,rfl⟩)
    · exact ⟨∞,hx.symm⟩
    · exact ⟨↑(verticalCellCoordinates i₀ σ ⟨y,hy⟩),by
        change (((verticalCellCoordinates i₀ σ).symm
          (verticalCellCoordinates i₀ σ ⟨y,hy⟩)).val : OnePoint (Configuration (d+1) n)) = y
        rw [Homeomorph.symm_apply_apply]⟩

theorem minimalSkeleton_eq_iUnion_cellRanges {d n : ℕ} (i₀ : Fin n) :
    minimalSkeleton d n = ⋃ σ : Equiv.Perm (Fin n),range (compactifiedVerticalCell i₀ σ) := by
  ext x
  simp only [compactifiedVerticalCell_range,minimalSkeleton,verticalSet_eq_iUnion_cells i₀,
    mem_union,mem_singleton_iff,mem_image,mem_iUnion]
  constructor
  · rintro (rfl | ⟨y,⟨σ,hy⟩,rfl⟩)
    · exact ⟨Equiv.refl _,Or.inl rfl⟩
    · exact ⟨σ,Or.inr ⟨y,hy,rfl⟩⟩
  · rintro ⟨σ,hx | ⟨y,hy,rfl⟩⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y,⟨σ,hy⟩,rfl⟩

theorem isClosed_minimalSkeleton {d n : ℕ} (i₀ : Fin n) : IsClosed (minimalSkeleton d n) := by
  rw [minimalSkeleton_eq_iUnion_cellRanges i₀]
  exact isClosed_iUnion_of_finite (fun σ => (isClosedEmbedding_compactifiedVerticalCell i₀ σ).isClosed_range)

end NRR.PrimePowerTopology
