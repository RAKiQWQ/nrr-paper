import NRR.CapMoments
import Mathlib.Order.Interval.Finset.Fin

/-! Additivity identifies the two cap readings of the distinguished second
cell with the exact pair used by the planar correction theorem. -/

noncomputable section
open Set Topology MeasureTheory Metric TopologicalSpace

namespace NRR.InterfaceChart

theorem integral_prefixCells {d n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    (S : Fin n → NonemptyCompacts (Space d × ℝ))
    (convex : ∀ i,Convex ℝ (S i : Set (Space d × ℝ)))
    (disjoint : Pairwise fun i j => Disjoint
      (interior (S i : Set (Space d × ℝ))) (interior (S j : Set (Space d × ℝ))))
    (f : (Space d × ℝ) → F) (hf : Integrable f μ) (k : Fin n) :
    (∫ x in prefixCells S k, f x ∂μ) =
      ∑ j : {j : Fin n // j ≤ k},∫ x in (S j.val : Set (Space d × ℝ)),f x ∂μ := by
  exact ConvexLimits.integral_partition
    ((volume : Measure (Space d)).prod (volume : Measure ℝ)) μ hμ
    (fun j : {j : Fin n // j ≤ k} => (S j.val : Set (Space d × ℝ)))
    (fun j => (S j.val).isCompact.isClosed) (fun j => convex j.val)
    (fun _ _ hij => disjoint (fun he => hij (Subtype.ext he))) rfl f hf.integrableOn

theorem prefixCells_zero {d r : ℕ}
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)) :
    prefixCells S 0 = (S 0 : Set (Space d × ℝ)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have eq : j.val = 0 := le_antisymm j.property (Fin.zero_le _)
    simpa only [eq] using hj
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨0,le_rfl⟩,hx⟩

theorem prefixCells_one {d r : ℕ}
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)) :
    prefixCells S 1 = (S 0 : Set (Space d × ℝ)) ∪ S 1 := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have eq : j.val = 0 ∨ j.val = 1 := by
      have h := j.property
      have hv : j.val.val ≤ 1 := h
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases eq with h | h
    · exact Or.inl (h ▸ hj)
    · exact Or.inr (h ▸ hj)
  · intro x hx
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨⟨0,by change (0 : ℕ) ≤ 1; omega⟩,hx⟩
    · exact mem_iUnion.mpr ⟨⟨1,le_rfl⟩,hx⟩

theorem integral_prefix_one {d r : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure (Space d × ℝ)) (hμ : μ ≪ volume)
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ))
    (convex : ∀ i,Convex ℝ (S i : Set (Space d × ℝ)))
    (disjoint : Pairwise fun i j => Disjoint
      (interior (S i : Set (Space d × ℝ))) (interior (S j : Set (Space d × ℝ))))
    (f : (Space d × ℝ) → F) (hf : Integrable f μ) :
    (∫ x in prefixCells S 1, f x ∂μ) =
      (∫ x in (S 0 : Set (Space d × ℝ)),f x ∂μ) +
      (∫ x in (S 1 : Set (Space d × ℝ)),f x ∂μ) := by
  rw [prefixCells_one]
  exact integral_union_ae (ConvexLimits.aedisjoint_of_disjoint_interiors
    ((volume : Measure (Space d)).prod (volume : Measure ℝ)) μ hμ
    (convex 0) (convex 1) (disjoint (by intro h; have hv := congrArg Fin.val h; simp at hv)))
    (S 1).isCompact.isClosed.measurableSet.nullMeasurableSet hf.integrableOn hf.integrableOn

theorem prefixMoment_eq_integral_of_cap {d n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure (Space d × ℝ))
    (f : (Space d × ℝ) → F) (K : Set (Space d × ℝ))
    (support : ∀ᵐ x ∂μ,x ∈ K) (S : Fin n → NonemptyCompacts (Space d × ℝ))
    (k : Fin n) (p : Parameters d) (cap : prefixCells S k = K ∩ belowGraph p) :
    prefixMoment μ f p = ∫ x in prefixCells S k,f x ∂μ := by
  rw [cap]
  apply setIntegral_congr_set
  filter_upwards [support] with x hx
  exact propext ⟨fun hb => ⟨hx,hb⟩,fun hb => hb.2⟩

theorem measureReal_prefixCells_of_mass {d n : ℕ}
    (μ : Measure (Space d × ℝ)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (S : Fin n → NonemptyCompacts (Space d × ℝ))
    (convex : ∀ i,Convex ℝ (S i : Set (Space d × ℝ)))
    (disjoint : Pairwise fun i j => Disjoint
      (interior (S i : Set (Space d × ℝ))) (interior (S j : Set (Space d × ℝ))))
    {m : ℝ} (mass : ∀ i,μ.real (S i : Set (Space d × ℝ)) = m) (k : Fin n) :
    μ.real (prefixCells S k) = ((k.val : ℝ)+1)*m := by
  have h := integral_prefixCells μ hμ S convex disjoint (fun _ => (1 : ℝ))
    (integrable_const 1) k
  simp only [setIntegral_one_eq_measureReal] at h
  rw [h]
  simp_rw [mass]
  have card : Fintype.card {j : Fin n // j ≤ k} = k.val+1 := by
    let e : {j : Fin n // j ≤ k} ≃ Fin (k.val+1) :=
      { toFun := fun j => ⟨j.val.val,Nat.lt_succ_of_le j.property⟩
        invFun := fun j => ⟨⟨j.val,j.isLt.trans_le (Nat.succ_le_of_lt k.isLt)⟩,
          Nat.le_of_lt_succ j.isLt⟩
        left_inv := fun j => by apply Subtype.ext; apply Fin.ext; rfl
        right_inv := fun j => by apply Fin.ext; rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_fin _)
  simp only [Finset.sum_const,Finset.card_univ,card,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

theorem ConvexPartition.mass_real_eq_div {d n : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin n → NonemptyCompacts (Space d × ℝ)} (part : ConvexPartition K S)
    (μ : Measure (Space d × ℝ)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (mass : ∀ i j,μ (S i : Set (Space d × ℝ)) = μ (S j : Set (Space d × ℝ))) (j : Fin n) :
    μ.real (S j : Set (Space d × ℝ)) = μ.real K / n := by
  have sum := ConvexLimits.integral_partition
    ((volume : Measure (Space d)).prod (volume : Measure ℝ)) μ hμ
    (fun i => (S i : Set (Space d × ℝ))) (fun i => (S i).isCompact.isClosed)
    part.cellConvex part.disjoint part.covers (fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  simp only [setIntegral_one_eq_measureReal] at sum
  have hreal (i) : μ.real (S i : Set (Space d × ℝ)) = μ.real (S j : Set (Space d × ℝ)) :=
    congrArg ENNReal.toReal (mass i j)
  simp_rw [hreal] at sum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  have hn : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt ((Nat.zero_le j.val).trans_lt j.isLt))
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using sum.symm

theorem ConvexPartition.prefix_mass_real {d n : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin n → NonemptyCompacts (Space d × ℝ)} (part : ConvexPartition K S)
    (μ : Measure (Space d × ℝ)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (mass : ∀ i j,μ (S i : Set (Space d × ℝ)) = μ (S j : Set (Space d × ℝ))) (k : Fin n) :
    μ.real (prefixCells S k) = ((k.val : ℝ)+1)*(μ.real K/n) :=
  measureReal_prefixCells_of_mass μ hμ S part.cellConvex part.disjoint
    (fun i => part.mass_real_eq_div μ hμ mass i) k

end NRR.InterfaceChart

namespace NRR.GlobalAssembly

def secondCellLabels (r : ℕ) : Option (Fin (r+1)) ≃ Fin (r+2) :=
  (finSuccEquiv' (1 : Fin (r+2))).symm

@[simp] theorem secondCellLabels_none (r : ℕ) : secondCellLabels r none = 1 :=
  finSuccEquiv'_symm_none _

@[simp] theorem secondCellLabels_some_zero (r : ℕ) : secondCellLabels r (some 0) = 0 := by
  exact finSuccEquiv'_symm_some_below (by change (0 : ℕ) < 1; omega)

theorem secondCellLabels_reading {r : ℕ} (v : Fin (r+2) → ℂ)
    (balanced : ∑ i,v i = 0) :
    (v 0,-(v 0+v 1)) = (v (secondCellLabels r (some 0)),
      (∑ i : Fin (r+1),v (secondCellLabels r (some i))) - v (secondCellLabels r (some 0))) := by
  have sum := (secondCellLabels r).sum_comp v
  rw [balanced,Fintype.sum_option,secondCellLabels_none] at sum
  rw [secondCellLabels_some_zero]
  apply Prod.ext
  · rfl
  · linear_combination -sum

/-- Once the second cell reads the first two actual prefix moments, its
geometric labeling is exactly the labeling expected by the global model. -/
theorem models_of_sorted_reading {r : ℕ} {B X : Type*}
    [TopologicalSpace B] [TopologicalSpace X]
    (chart : TwoInterfaceChart (r+1) B) (cell : Fin (r+2) → C(X,B)) (w : C(B,ℂ))
    (x : X) (σ : Equiv.Perm (Fin (r+2)))
    (mem : ∀ i,cell (σ (secondCellLabels r i)) x ∈ chart.family i)
    (balanced : ∑ i,w (cell i x) = 0)
    (reading : chart.reading ⟨cell (σ (secondCellLabels r none)) x,mem none⟩ =
      (w (cell (σ 0) x),-(w (cell (σ 0) x)+w (cell (σ 1) x)))) :
    chart.Models cell w x := by
  let e : Option (Fin (r+1)) ≃ Fin (r+2) := (secondCellLabels r).trans σ
  have hs : ∑ i,w (cell (σ i) x) = 0 := by
    rw [Equiv.sum_comp σ (fun i => w (cell i x)),balanced]
  refine ⟨e,mem,?_⟩
  exact reading.trans (secondCellLabels_reading (fun i => w (cell (σ i) x)) hs)

end NRR.GlobalAssembly
