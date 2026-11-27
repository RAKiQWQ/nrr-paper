import NRR.CylinderExtension
import NRR.CutContinuity
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Interval.Set.Disjoint

/-! Horizontal clips inside a cylinder determine the whole convex partition. -/

noncomputable section
open Set Topology Filter Metric TopologicalSpace
set_option maxHeartbeats 800000

namespace NRR.HorizontalExtension
open InterfaceChart

theorem interval_order {ι : Type*} (a b : ι → ℝ) (positive : ∀ i, a i < b i)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    {i j : ι} (hne : i ≠ j) : b i ≤ a j ∨ b j ≤ a i := by
  have h := Ioo_disjoint_Ioo.mp (disjoint hne)
  rcases le_total (a i) (a j) with ha | ha
  · rw [max_eq_right ha,min_le_iff] at h
    exact h.elim Or.inl (fun hb => False.elim ((not_le_of_gt (positive j)) hb))
  · rw [max_eq_left ha,min_le_iff] at h
    exact h.elim (fun hb => False.elim ((not_le_of_gt (positive i)) hb)) Or.inr

/-- Each internal left endpoint has a predecessor ending at precisely that
endpoint. This uses closedness of the finite union and does not choose a sort. -/
theorem exists_left_neighbor {n : ℕ} (a b : Fin n → ℝ) (positive : ∀ i, a i < b i)
    {L H : ℝ} (bounds : ∀ i, L ≤ a i ∧ b i ≤ H)
    (cover : (⋃ i, Icc (a i) (b i)) = Icc L H)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (i : Fin n) (inside : L < a i) : ∃ j, b j = a i ∧ j ≠ i := by
  let F := ⋃ j : {j : Fin n // b j ≤ a i}, Icc (a j.val) (b j.val)
  have closed : IsClosed F := isClosed_iUnion_of_finite fun _ => isClosed_Icc
  have sub : Ioo L (a i) ⊆ F := by
    intro x hx
    have inAll : x ∈ ⋃ j, Icc (a j) (b j) :=
      cover.symm ▸ ⟨hx.1.le,(hx.2.trans (positive i)).le.trans (bounds i).2⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp inAll
    have hne : j ≠ i := by intro he; subst j; linarith [hj.1,hx.2]
    have ending : b j ≤ a i := by
      rcases interval_order a b positive disjoint hne with h | h
      · exact h
      · linarith [hj.1,positive i,hx.2]
    exact mem_iUnion.mpr ⟨⟨j,ending⟩,hj⟩
  have hend : a i ∈ F := closed.closure_subset (closure_mono sub (by
    rw [closure_Ioo inside.ne]
    exact right_mem_Icc.mpr inside.le))
  obtain ⟨⟨j,hj⟩,memj⟩ := mem_iUnion.mp hend
  have eq : b j = a i := le_antisymm hj memj.2
  exact ⟨j,eq,by intro he; subst j; linarith [positive i]⟩

theorem exists_right_neighbor {n : ℕ} (a b : Fin n → ℝ) (positive : ∀ i, a i < b i)
    {L H : ℝ} (bounds : ∀ i, L ≤ a i ∧ b i ≤ H)
    (cover : (⋃ i, Icc (a i) (b i)) = Icc L H)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (i : Fin n) (inside : b i < H) : ∃ j, a j = b i ∧ j ≠ i := by
  let F := ⋃ j : {j : Fin n // b i ≤ a j}, Icc (a j.val) (b j.val)
  have closed : IsClosed F := isClosed_iUnion_of_finite fun _ => isClosed_Icc
  have sub : Ioo (b i) H ⊆ F := by
    intro x hx
    have inAll : x ∈ ⋃ j, Icc (a j) (b j) :=
      cover.symm ▸ ⟨(bounds i).1.trans ((positive i).le.trans hx.1.le),hx.2.le⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp inAll
    have hne : i ≠ j := by intro he; subst j; linarith [hj.2,hx.1]
    have starting : b i ≤ a j := by
      rcases interval_order a b positive disjoint hne with h | h
      · exact h
      · linarith [hj.2,positive i,hx.1]
    exact mem_iUnion.mpr ⟨⟨j,starting⟩,hj⟩
  have hend : b i ∈ F := closed.closure_subset (closure_mono sub (by
    rw [closure_Ioo inside.ne]
    exact left_mem_Icc.mpr inside.le))
  obtain ⟨⟨j,hj⟩,memj⟩ := mem_iUnion.mp hend
  have eq : a j = b i := le_antisymm memj.1 hj
  exact ⟨j,eq,by intro he; subst j; linarith [positive i]⟩

section Clips
variable {d n : ℕ} {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
  {L H : ℝ} (C : Fin n → Set (Space d × ℝ)) (a b : Fin n → ℝ)
  (positive : ∀ i, a i < b i)
  (clips : ∀ i, C i ∩ (D ×ˢ Icc L H) = D ×ˢ Icc (a i) (b i))
include clips

theorem slab_subset (i : Fin n) : D ×ˢ Icc (a i) (b i) ⊆ C i := by
  intro x hx
  exact ((clips i).symm ▸ hx : x ∈ C i ∩ (D ×ˢ Icc L H)).1

include hD positive in
theorem endpoint_bounds : ∀ i, L ≤ a i ∧ b i ≤ H := by
  intro i
  have lo : ((0,a i) : Space d × ℝ) ∈ C i ∩ (D ×ˢ Icc L H) :=
    (clips i).symm ▸ ⟨interior_subset hD,le_rfl,(positive i).le⟩
  have hi : ((0,b i) : Space d × ℝ) ∈ C i ∩ (D ×ˢ Icc L H) :=
    (clips i).symm ▸ ⟨interior_subset hD,(positive i).le,le_rfl⟩
  exact ⟨lo.2.2.1,hi.2.2.2⟩

include hD in
theorem interval_cover (covers : D ×ˢ Icc L H ⊆ ⋃ i, C i) :
    (⋃ i, Icc (a i) (b i)) = Icc L H := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hp : ((0,z) : Space d × ℝ) ∈ C i ∩ (D ×ˢ Icc L H) :=
      (clips i).symm ▸ ⟨interior_subset hD,hi⟩
    exact hp.2.2
  · intro hz
    have axisIn : ((0,z) : Space d × ℝ) ∈ ⋃ i, C i :=
      covers ⟨interior_subset hD,hz⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp axisIn
    have hp := (clips i) ▸ (show ((0,z) : Space d × ℝ) ∈ C i ∩ (D ×ˢ Icc L H) from
      ⟨hi,interior_subset hD,hz⟩)
    exact mem_iUnion.mpr ⟨i,hp.2⟩

include hD in
theorem interval_disjoint
    (disjoint : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j))) :
    Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hi hj
  have inti : ((0,z) : Space d × ℝ) ∈ interior (C i) := by
    apply interior_mono (slab_subset C a b clips i)
    rw [interior_prod_eq,interior_Icc]
    exact ⟨hD,hi⟩
  have intj : ((0,z) : Space d × ℝ) ∈ interior (C j) := by
    apply interior_mono (slab_subset C a b clips j)
    rw [interior_prod_eq,interior_Icc]
    exact ⟨hD,hj⟩
  exact disjoint_left.mp (disjoint hij) inti intj

include hD positive in
/-- Every internal endpoint of a cylinder clip bounds the entire convex
piece globally. Outer cylinder endpoints impose no artificial bound. -/
theorem global_height_bounds (closed : ∀ i, IsClosed (C i)) (convex : ∀ i, Convex ℝ (C i))
    (covers : D ×ˢ Icc L H ⊆ ⋃ i, C i)
    (disjoint : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j))) :
    ∀ i, (L < a i → ∀ x ∈ C i, a i ≤ x.2) ∧ (b i < H → ∀ x ∈ C i, x.2 ≤ b i) := by
  have bounds := endpoint_bounds hD C a b positive clips
  have cover := interval_cover hD C a b clips covers
  have disj := interval_disjoint hD C a b clips disjoint
  intro i
  constructor
  · intro hlow
    obtain ⟨j,edge,hne⟩ := exists_left_neighbor a b positive bounds cover disj i hlow
    have lower : D ×ˢ Icc (a j) (a i) ⊆ C j := by
      simpa only [edge] using slab_subset C a b clips j
    exact (Cylinder.separated_by_adjacent_horizontal_slabs (closed j) (closed i)
      (convex j) (convex i) (disjoint hne) hD (by simpa only [edge] using positive j)
      (positive i) lower (slab_subset C a b clips i)).2
  · intro hhigh
    obtain ⟨j,edge,hne⟩ := exists_right_neighbor a b positive bounds cover disj i hhigh
    have upper : D ×ˢ Icc (b i) (b j) ⊆ C j := by
      simpa only [edge] using slab_subset C a b clips j
    exact (Cylinder.separated_by_adjacent_horizontal_slabs (closed i) (closed j)
      (convex i) (convex j) (disjoint hne.symm) hD (positive i)
      (by simpa only [edge] using positive j) (slab_subset C a b clips i) upper).1

include hD positive in
/-- Horizontal cylinder clips determine the complete horizontal partition
of any convex parent, including all plane boundaries and the two end caps. -/
theorem cell_eq_horizontal_caps {K : Set (Space d × ℝ)} (parentConvex : Convex ℝ K)
    (closed : ∀ i, IsClosed (C i)) (convex : ∀ i, Convex ℝ (C i))
    (covers : (⋃ i, C i) = K) (inner : D ×ˢ Icc L H ⊆ K)
    (disjoint : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j))) :
    ∀ i, C i = K ∩ {x | (L < a i → a i ≤ x.2) ∧ (b i < H → x.2 ≤ b i)} := by
  have coverCylinder : D ×ˢ Icc L H ⊆ ⋃ i, C i := covers.symm ▸ inner
  have bounds := endpoint_bounds hD C a b positive clips
  have disj := interval_disjoint hD C a b clips disjoint
  have global := global_height_bounds hD C a b positive clips closed convex coverCylinder disjoint
  have subK (i) : C i ⊆ K := covers ▸ subset_iUnion C i
  have strictIn (i) (x : Space d × ℝ) (hx : x ∈ K)
      (hl : L < a i → a i < x.2) (hu : b i < H → x.2 < b i) : x ∈ C i := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp (covers.symm ▸ hx)
    by_cases he : j = i
    · simpa only [he] using hj
    rcases interval_order a b positive disj he with below | above
    · have internalI : L < a i := (bounds j).1.trans_lt ((positive j).trans_le below)
      have internalJ : b j < H := (below.trans_lt (positive i)).trans_le (bounds i).2
      have hz := (global j).2 internalJ x hj
      linarith [hl internalI]
    · have internalI : b i < H := (above.trans_lt (positive j)).trans_le (bounds j).2
      have internalJ : L < a j := (bounds i).1.trans_lt ((positive i).trans_le above)
      have hz := (global j).1 internalJ x hj
      linarith [hu internalI]
  intro i
  apply Subset.antisymm
  · intro x hx
    exact ⟨subK i hx,fun h => (global i).1 h x hx,fun h => (global i).2 h x hx⟩
  · rintro x ⟨hx,hl,hu⟩
    let y : Space d × ℝ := (0,(a i+b i)/2)
    have hy : y ∈ C i := slab_subset C a b clips i ⟨interior_subset hD,by
      constructor <;> dsimp [y] <;> linarith [positive i]⟩
    have seg : openSegment ℝ y x ⊆ C i := by
      rintro _ ⟨s,t,hs,ht,hst,rfl⟩
      apply strictIn i _ (parentConvex (subK i hy) hx hs.le ht.le hst)
      · intro hi
        have hxlo := hl hi
        have hylo : a i < y.2 := by dsimp [y]; linarith [positive i]
        change a i < s*y.2+t*x.2
        calc
          a i = s*a i+t*a i := by rw [← add_mul,hst,one_mul]
          _ < s*y.2+t*x.2 := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hylo hs)
            (mul_le_mul_of_nonneg_left hxlo ht.le)
      · intro hi
        have hxhi := hu hi
        have hyhi : y.2 < b i := by dsimp [y]; linarith [positive i]
        change s*y.2+t*x.2 < b i
        calc
          s*y.2+t*x.2 < s*b i+t*b i := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hyhi hs)
            (mul_le_mul_of_nonneg_left hxhi ht.le)
          _ = b i := by rw [← add_mul,hst,one_mul]
    exact (closed i).closure_subset
      (closure_mono seg (segment_subset_closure_openSegment (right_mem_segment ..)))

end Clips

theorem lower_injective {n : ℕ} (a b : Fin n → ℝ) (positive : ∀ i, a i < b i)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) :
    Function.Injective a := by
  intro i j he
  by_contra hne
  rcases interval_order a b positive disjoint hne with h | h
  · linarith [positive i]
  · linarith [positive j]

theorem upper_strictMono_of_lower {n : ℕ} (a b : Fin n → ℝ)
    (positive : ∀ i, a i < b i)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (sorted : StrictMono a) : StrictMono b := by
  intro i j hij
  have ha := sorted hij
  rcases interval_order a b positive disjoint hij.ne with h | h
  · exact h.trans_lt (positive j)
  · linarith [positive j]

private structure SortIndex (n : ℕ) where
  val : Fin n

private def sortIndexEquiv (n : ℕ) : SortIndex n ≃ Fin n where
  toFun := SortIndex.val
  invFun := SortIndex.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The vertical order of the clips gives an actual permutation of the
original cell labels, independent of any preexisting label order. -/
theorem exists_sorted_intervals {n : ℕ} (a b : Fin n → ℝ) (positive : ∀ i, a i < b i)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) :
    ∃ σ : Equiv.Perm (Fin n), StrictMono (fun i => a (σ i)) ∧ StrictMono (fun i => b (σ i)) := by
  classical
  have inj := lower_injective a b positive disjoint
  letI : Fintype (SortIndex n) := Fintype.ofEquiv (Fin n) (sortIndexEquiv n).symm
  letI : LinearOrder (SortIndex n) := LinearOrder.lift' (fun i => a i.val) (by
    intro i j he
    cases i with | mk i => cases j with | mk j => exact congrArg SortIndex.mk (inj he))
  let e : Fin n ≃o SortIndex n := monoEquivOfFin (SortIndex n) (k := n)
    ((Fintype.card_congr (sortIndexEquiv n)).trans (Fintype.card_fin n))
  let σ : Equiv.Perm (Fin n) := e.toEquiv.trans (sortIndexEquiv n)
  have sorted : StrictMono (fun i => a (σ i)) := by
    intro i j hij
    change a (e i).val < a (e j).val
    exact e.strictMono hij
  refine ⟨σ,sorted,upper_strictMono_of_lower _ _ (fun i => positive (σ i)) ?_ sorted⟩
  intro i j hij
  exact disjoint (σ.injective.ne hij)

theorem adjacent_endpoints_of_sorted {n : ℕ} (a b : Fin n → ℝ)
    (positive : ∀ i, a i < b i) {L H : ℝ} (bounds : ∀ i, L ≤ a i ∧ b i ≤ H)
    (cover : (⋃ i, Icc (a i) (b i)) = Icc L H)
    (disjoint : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (sorted : StrictMono a) (i j : Fin n) (adjacent : j.val = i.val+1) : b i = a j := by
  have hij : i < j := by omega
  have upperSorted := upper_strictMono_of_lower a b positive disjoint sorted
  have le : b i ≤ a j := by
    rcases interval_order a b positive disjoint hij.ne with h | h
    · exact h
    · linarith [sorted hij,positive j]
  apply le_antisymm le
  by_contra! gap
  let x := (b i+a j)/2
  have hx : x ∈ Icc L H := by
    constructor <;> dsimp [x] <;> linarith [(bounds i).1,(bounds j).2,positive i,positive j]
  obtain ⟨k,hk⟩ := mem_iUnion.mp (cover.symm ▸ hx)
  by_cases hki : k ≤ i
  · have hb := upperSorted.monotone hki
    dsimp [x] at hk
    linarith [hk.2]
  · have hjk : j ≤ k := by omega
    have ha := sorted.monotone hjk
    dsimp [x] at hk
    linarith [hk.1]

/-- Once the clips are in vertical order, nonneighboring whole pieces are
disjoint, not merely interior-disjoint. Their positive separating gap is
inherited from the intervening cylinder slab. -/
theorem nonadjacent_whole_cells {d n : ℕ} {D : Set (Space d)}
    (hD : (0 : Space d) ∈ interior D) {L H : ℝ}
    (C : Fin n → Set (Space d × ℝ)) (a b : Fin n → ℝ)
    (positive : ∀ i, a i < b i)
    (clips : ∀ i, C i ∩ (D ×ˢ Icc L H) = D ×ˢ Icc (a i) (b i))
    (closed : ∀ i, IsClosed (C i)) (convex : ∀ i, Convex ℝ (C i))
    (covers : D ×ˢ Icc L H ⊆ ⋃ i, C i)
    (disjoint : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (sorted : StrictMono a) :
    ∀ i j, i.val+1 < j.val → Disjoint (C i) (C j) := by
  have bounds := endpoint_bounds hD C a b positive clips
  have cover := interval_cover hD C a b clips covers
  have disj := interval_disjoint hD C a b clips disjoint
  have global := global_height_bounds hD C a b positive clips closed convex covers disjoint
  intro i j hij
  let k : Fin n := ⟨i.val+1,by omega⟩
  have edge : b i = a k := adjacent_endpoints_of_sorted a b positive bounds cover disj sorted i k rfl
  have hkj : k < j := hij
  have gap : b i < a j := edge ▸ sorted hkj
  have bi : b i < H := (gap.trans (positive j)).trans_le (bounds j).2
  have aj : L < a j := (bounds i).1.trans_lt ((positive i).trans gap)
  apply disjoint_left.mpr
  intro x hi hj
  have lo := (global j).1 aj x hj
  have hi := (global i).2 bi x hi
  linarith

/-- The actual output of cylinder rigidity, with arbitrary original cell
labels, supplies a sorted horizontal reference chain and a genuine open
affine chart for every nearby convex partition of the parent. -/
theorem slab_partition_has_chain_chart {d r : ℕ} {D : Set (Space d)}
    (hD : (0 : Space d) ∈ interior D) {L H : ℝ} {K : Set (Space d × ℝ)}
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ))
    (a b : Fin (r+2) → ℝ) (positive : ∀ i, a i < b i)
    (clips : ∀ i, (S i : Set (Space d × ℝ)) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc (a i) (b i))
    (convex : ∀ i, Convex ℝ (S i : Set (Space d × ℝ)))
    (covers : (⋃ i, (S i : Set (Space d × ℝ))) = K) (inner : D ×ˢ Icc L H ⊆ K)
    (disjoint : Pairwise fun i j => Disjoint
      (interior (S i : Set (Space d × ℝ))) (interior (S j : Set (Space d × ℝ))))
    {η : ℝ} (hη : 0 < η) :
    ∃ σ : Equiv.Perm (Fin (r+2)),
      ∃ U : Set (Fin (r+2) → NonemptyCompacts (Space d × ℝ)),
        StrictMono (fun i => a (σ i)) ∧ StrictMono (fun i => b (σ i)) ∧
        IsOpen U ∧ (fun i => S (σ i)) ∈ U ∧
        ∀ T ∈ U, ConvexPartition K T →
          ∃ P : Fin (r+1) → Parameters d, ChainPartition K T ∧
            (∀ i, dist (P i) (0,b (σ i.castSucc)) < η) ∧
            ∀ i, prefixCells T i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
              suffixCells T i.succ = K ∩ {x | height (P i) x.1 ≤ x.2} := by
  have disjInt := interval_disjoint hD (fun i => (S i : Set (Space d × ℝ))) a b clips disjoint
  obtain ⟨σ,sortA,sortB⟩ := exists_sorted_intervals a b positive disjInt
  let R : Fin (r+2) → NonemptyCompacts (Space d × ℝ) := fun i => S (σ i)
  have clipsR (i) : (R i : Set (Space d × ℝ)) ∩ (D ×ˢ Icc L H) =
      D ×ˢ Icc (a (σ i)) (b (σ i)) := clips (σ i)
  have disjR : Pairwise fun i j => Disjoint
      (interior (R i : Set (Space d × ℝ))) (interior (R j : Set (Space d × ℝ))) :=
    fun _ _ hij => disjoint (σ.injective.ne hij)
  have coverR : (⋃ i, (R i : Set (Space d × ℝ))) = K := by
    rw [← covers]
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨σ i,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨σ.symm i,by simpa only [R,σ.apply_symm_apply] using hi⟩
  have cylinderCover : D ×ˢ Icc L H ⊆ ⋃ i, (R i : Set (Space d × ℝ)) := coverR.symm ▸ inner
  have nonadjR := nonadjacent_whole_cells hD (fun i => (R i : Set (Space d × ℝ)))
    (fun i => a (σ i)) (fun i => b (σ i)) (fun i => positive (σ i)) clipsR
    (fun i => (R i).isCompact.isClosed) (fun i => convex (σ i)) cylinderCover disjR sortA
  have bounds := endpoint_bounds hD (fun i => (R i : Set (Space d × ℝ)))
    (fun i => a (σ i)) (fun i => b (σ i)) (fun i => positive (σ i)) clipsR
  have coverInt := interval_cover hD (fun i => (R i : Set (Space d × ℝ)))
    (fun i => a (σ i)) (fun i => b (σ i)) clipsR cylinderCover
  have disjIntR := interval_disjoint hD (fun i => (R i : Set (Space d × ℝ)))
    (fun i => a (σ i)) (fun i => b (σ i)) clipsR disjR
  have edge (i : Fin (r+1)) : b (σ i.castSucc) = a (σ i.succ) :=
    adjacent_endpoints_of_sorted _ _ (fun i => positive (σ i)) bounds coverInt disjIntR sortA
      i.castSucc i.succ rfl
  have below (i : Fin (r+1)) :
      (0,(a (σ i.castSucc)+b (σ i.castSucc))/2) ∈ R i.castSucc := by
    apply slab_subset (fun i => (R i : Set (Space d × ℝ))) _ _ clipsR i.castSucc
    exact ⟨interior_subset hD,by constructor <;> linarith [positive (σ i.castSucc)]⟩
  have lower (i : Fin (r+1)) (u : Space d) (hu : u ∈ D) : (u,b (σ i.castSucc)) ∈ R i.castSucc :=
    slab_subset (fun i => (R i : Set (Space d × ℝ))) _ _ clipsR i.castSucc
      ⟨hu,(positive (σ i.castSucc)).le,le_rfl⟩
  have upper (i : Fin (r+1)) (u : Space d) (hu : u ∈ D) : (u,b (σ i.castSucc)) ∈ R i.succ := by
    apply slab_subset (fun i => (R i : Set (Space d × ℝ))) _ _ clipsR i.succ
    rw [edge i]
    exact ⟨hu,le_rfl,(positive (σ i.succ)).le⟩
  obtain ⟨U,hU,memU,chart⟩ := exists_chain_graph_neighborhood R nonadjR hD
    (fun i => (a (σ i.castSucc)+b (σ i.castSucc))/2) (fun i => b (σ i.castSucc))
    (fun i => by dsimp; linarith [positive (σ i.castSucc)]) below lower upper hη
  exact ⟨σ,U,sortA,sortB,hU,memU,fun T hT part => chart T hT K part⟩

theorem convexPartition_reindex {d n : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin n → NonemptyCompacts (Space d × ℝ)} (part : ConvexPartition K S)
    (σ : Equiv.Perm (Fin n)) : ConvexPartition K (fun i => S (σ i)) := by
  refine ⟨part.parentConvex,fun i => part.cellConvex (σ i),
    fun i => part.cellInterior (σ i),?_,fun _ _ hij => part.disjoint (σ.injective.ne hij)⟩
  rw [← part.covers]
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨σ i,hi⟩
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨σ.symm i,by simpa only [σ.apply_symm_apply] using hi⟩

/-- The graph-chart neighborhood can be pulled back to the original cell
labels. It therefore supplies an open neighborhood for compact localization
without requiring the limiting partitions to have a predetermined ordering. -/
theorem slab_partition_has_unlabelled_chart {d r : ℕ} {D : Set (Space d)}
    (hD : (0 : Space d) ∈ interior D) {L H : ℝ} {K : Set (Space d × ℝ)}
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ))
    (a b : Fin (r+2) → ℝ) (positive : ∀ i, a i < b i)
    (clips : ∀ i, (S i : Set (Space d × ℝ)) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc (a i) (b i))
    (convex : ∀ i, Convex ℝ (S i : Set (Space d × ℝ)))
    (covers : (⋃ i, (S i : Set (Space d × ℝ))) = K) (inner : D ×ˢ Icc L H ⊆ K)
    (disjoint : Pairwise fun i j => Disjoint
      (interior (S i : Set (Space d × ℝ))) (interior (S j : Set (Space d × ℝ))))
    {η : ℝ} (hη : 0 < η) :
    ∃ σ : Equiv.Perm (Fin (r+2)),
      ∃ U : Set (Fin (r+2) → NonemptyCompacts (Space d × ℝ)),
        StrictMono (fun i => a (σ i)) ∧ StrictMono (fun i => b (σ i)) ∧ IsOpen U ∧ S ∈ U ∧
        ∀ T ∈ U, ConvexPartition K T →
          ∃ P : Fin (r+1) → Parameters d, ChainPartition K (fun i => T (σ i)) ∧
            (∀ i, dist (P i) (0,b (σ i.castSucc)) < η) ∧
            ∀ i, prefixCells (fun j => T (σ j)) i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
              suffixCells (fun j => T (σ j)) i.succ = K ∩ {x | height (P i) x.1 ≤ x.2} := by
  obtain ⟨σ,V,sortedA,sortedB,hV,memV,chart⟩ :=
    slab_partition_has_chain_chart hD S a b positive clips convex covers inner disjoint hη
  let reorder := fun T : Fin (r+2) → NonemptyCompacts (Space d × ℝ) => fun i => T (σ i)
  have continuousReorder : Continuous reorder := continuous_pi fun i => continuous_apply (σ i)
  refine ⟨σ,reorder ⁻¹' V,sortedA,sortedB,hV.preimage continuousReorder,memV,?_⟩
  intro T hT part
  exact chart (reorder T) hT (convexPartition_reindex part σ)

theorem horizontal_caps_of_face {d n : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin n → NonemptyCompacts (Space d × ℝ)} (part : ChainPartition K S)
    (i j : Fin n) (adjacent : j.val = i.val+1)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {a t : ℝ}
    (hat : a < t) (below : (0,a) ∈ S i)
    (faceLower : ∀ u ∈ D,(u,t) ∈ S i) (faceUpper : ∀ u ∈ D,(u,t) ∈ S j) :
    prefixCells S i = K ∩ {x | x.2 ≤ t} ∧ suffixCells S j = K ∩ {x | t ≤ x.2} := by
  obtain ⟨F,c,hne,sep,lower,upper⟩ := part.exists_caps i j adjacent
  have face (u : Space d) (hu : u ∈ D) : F (u,t) = c :=
    le_antisymm (sep.1 _ (faceLower u hu)) (sep.2 _ (faceUpper u hu))
  obtain ⟨positive,offset,vertical⟩ := separator_eq_vertical hD F hne hat (sep.1 _ below) face
  have graph := graphParameters_of_vertical F positive.ne' offset vertical
  constructor
  · rw [lower]
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,le_separator_iff_graph F c positive,graph,height,
      ContinuousLinearMap.zero_apply,zero_add]
  · rw [upper]
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,ge_separator_iff_graph F c positive,graph,height,
      ContinuousLinearMap.zero_apply,zero_add]

theorem horizontal_caps_of_sorted_clips {d r : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)} (part : ChainPartition K S)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {L H : ℝ}
    (a b : Fin (r+2) → ℝ) (positive : ∀ i,a i < b i)
    (clips : ∀ i,(S i : Set (Space d × ℝ)) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc (a i) (b i))
    (inner : D ×ˢ Icc L H ⊆ K) (sorted : StrictMono a) :
    ∀ i : Fin (r+1),prefixCells S i.castSucc = K ∩ {x | x.2 ≤ b i.castSucc} ∧
      suffixCells S i.succ = K ∩ {x | b i.castSucc ≤ x.2} := by
  have cover : D ×ˢ Icc L H ⊆ ⋃ i,(S i : Set (Space d × ℝ)) := part.covers.symm ▸ inner
  have bounds := endpoint_bounds hD (fun i => (S i : Set (Space d × ℝ))) a b positive clips
  have covered := interval_cover hD (fun i => (S i : Set (Space d × ℝ))) a b clips cover
  have disj := interval_disjoint hD (fun i => (S i : Set (Space d × ℝ))) a b clips part.disjoint
  intro i
  have edge := adjacent_endpoints_of_sorted a b positive bounds covered disj sorted
    i.castSucc i.succ rfl
  apply horizontal_caps_of_face part i.castSucc i.succ rfl hD
    (a := (a i.castSucc+b i.castSucc)/2) (by linarith [positive i.castSucc])
  · apply slab_subset (fun i => (S i : Set (Space d × ℝ))) a b clips i.castSucc
    exact ⟨interior_subset hD,by constructor <;> linarith [positive i.castSucc]⟩
  · intro u hu
    exact slab_subset (fun i => (S i : Set (Space d × ℝ))) a b clips i.castSucc
      ⟨hu,(positive i.castSucc).le,le_rfl⟩
  · intro u hu
    apply slab_subset (fun i => (S i : Set (Space d × ℝ))) a b clips i.succ
    rw [edge]
    exact ⟨hu,le_rfl,(positive i.succ).le⟩

/-- The unlabelled local graph chart also supplies the exact horizontal
prefix caps of its reference partition, needed to identify mass quantiles. -/
theorem slab_partition_has_unlabelled_chart_with_caps {d r : ℕ} {D : Set (Space d)}
    (hD : (0 : Space d) ∈ interior D) {L H : ℝ} {K : Set (Space d × ℝ)}
    (S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)) (part : ConvexPartition K S)
    (a b : Fin (r+2) → ℝ) (positive : ∀ i,a i < b i)
    (clips : ∀ i,(S i : Set (Space d × ℝ)) ∩ (D ×ˢ Icc L H) = D ×ˢ Icc (a i) (b i))
    (inner : D ×ˢ Icc L H ⊆ K) {η : ℝ} (hη : 0 < η) :
    ∃ σ : Equiv.Perm (Fin (r+2)),
      ∃ U : Set (Fin (r+2) → NonemptyCompacts (Space d × ℝ)),
        IsOpen U ∧ S ∈ U ∧
        (∀ i : Fin (r+1),prefixCells (fun j => S (σ j)) i.castSucc =
          K ∩ {x | x.2 ≤ b (σ i.castSucc)}) ∧
        ∀ T ∈ U,ConvexPartition K T →
          ∃ P : Fin (r+1) → Parameters d,ChainPartition K (fun i => T (σ i)) ∧
            (∀ i,dist (P i) (0,b (σ i.castSucc)) < η) ∧
            ∀ i,prefixCells (fun j => T (σ j)) i.castSucc =
                K ∩ {x | x.2 ≤ height (P i) x.1} ∧
              suffixCells (fun j => T (σ j)) i.succ =
                K ∩ {x | height (P i) x.1 ≤ x.2} := by
  obtain ⟨σ,U,sa,_,hU,memU,chart⟩ := slab_partition_has_unlabelled_chart hD S a b
    positive clips part.cellConvex part.covers inner part.disjoint hη
  obtain ⟨_,chain,_,_⟩ := chart S memU part
  have caps := horizontal_caps_of_sorted_clips chain hD (fun i => a (σ i))
    (fun i => b (σ i)) (fun i => positive (σ i)) (fun i => clips (σ i)) inner sa
  exact ⟨σ,U,hU,memU,fun i => (caps i).1,chart⟩

end NRR.HorizontalExtension
