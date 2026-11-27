import NRR.PrimePowerTopologyMinimalSkeleton
import Mathlib.Data.Finset.Card

/-! A finite closed filtration of the actual configuration space by
Fox--Neuwirth coordinate complexity. Each initial horizontal-coordinate
projection is allowed only finitely many different values. A finite union
of linear equality loci proves closedness directly; no cellular homology
identification is assumed here. -/

noncomputable section
open Set Topology Finset
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

abbrev FuksPattern (d n : ℕ) := Fin d → Fin n → Fin n

def fuksPatternCost {d n : ℕ} (P : FuksPattern d n) : ℕ :=
  ∑ k : Fin d,(Finset.univ.image (P k)).card

/-- Equal pattern labels require equality of the entire corresponding
initial horizontal-coordinate projection. -/
def fuksPatternSet {d n : ℕ} (P : FuksPattern d n) :
    Set (Configuration (d+1) n) :=
  {x | ∀ k i j,P k i = P k j → ∀ l : Fin d,l ≤ k →
    (horizontalHeight d (x.val i)).1 l = (horizontalHeight d (x.val j)).1 l}

theorem isClosed_fuksPatternSet {d n : ℕ} (P : FuksPattern d n) :
    IsClosed (fuksPatternSet P) := by
  have repr : fuksPatternSet P = ⋂ k : Fin d,⋂ i : Fin n,⋂ j : Fin n,
      ⋂ l : Fin d,{x : Configuration (d+1) n | P k i = P k j ∧ l ≤ k →
        (horizontalHeight d (x.val i)).1 l = (horizontalHeight d (x.val j)).1 l} := by
    ext x
    simp only [fuksPatternSet,mem_setOf_eq,mem_iInter,and_imp]
    aesop
  rw [repr]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro l
  have cont (a : Fin n) : Continuous (fun x : Configuration (d+1) n =>
      (horizontalHeight d (x.val a)).1 l) :=
    (EuclideanSpace.proj l).continuous.comp
      (continuous_fst.comp ((horizontalHeight d).continuous.comp
        ((continuous_apply a).comp continuous_subtype_val)))
  by_cases h : P k i = P k j ∧ l ≤ k
  · simpa [h] using isClosed_eq
      (cont i) (cont j)
  · simp only [h,false_implies,setOf_true,isClosed_univ]

/-- The index records the sum of the numbers of distinct initial
horizontal projections. The geometric cell dimension is this index plus n. -/
def fuksLevel (d n k : ℕ) : Set (Configuration (d+1) n) :=
  ⋃ P : FuksPattern d n,⋃ (_ : fuksPatternCost P ≤ k),fuksPatternSet P

theorem mem_fuksLevel_iff {d n k : ℕ} {x : Configuration (d+1) n} :
    x ∈ fuksLevel d n k ↔
      ∃ P : FuksPattern d n,fuksPatternCost P ≤ k ∧ x ∈ fuksPatternSet P := by
  simp only [fuksLevel,mem_iUnion,exists_prop]

theorem isClosed_fuksLevel (d n k : ℕ) : IsClosed (fuksLevel d n k) := by
  apply isClosed_iUnion_of_finite
  intro P
  apply isClosed_iUnion_of_finite
  intro _
  exact isClosed_fuksPatternSet P

theorem fuksLevel_mono (d n : ℕ) : Monotone (fuksLevel d n) := by
  intro k l hkl x hx
  obtain ⟨P,hP,hx⟩ := mem_fuksLevel_iff.mp hx
  exact mem_fuksLevel_iff.mpr ⟨P,hP.trans hkl,hx⟩

theorem fuksLevel_top (d n : ℕ) : fuksLevel d n (d*n) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine mem_fuksLevel_iff.mpr ⟨fun _ => id,?_,?_⟩
  · simp [fuksPatternCost]
  · intro k i j hij l _
    exact congrArg (fun i => (horizontalHeight d (x.val i)).1 l) hij

theorem fuksPatternCost_lower {d n : ℕ} [NeZero n] (P : FuksPattern d n) :
    d ≤ fuksPatternCost P := by
  have bound (k : Fin d) : 1 ≤ (Finset.univ.image (P k)).card := by
    exact card_pos.mpr ⟨P k 0,mem_image.mpr ⟨0,mem_univ _,rfl⟩⟩
  have h := sum_le_sum (s := (univ : Finset (Fin d))) (fun k _ => bound k)
  simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using h

theorem fuksLevel_eq_empty_of_lt {d n k : ℕ} [NeZero n] (hk : k < d) :
    fuksLevel d n k = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨P,hP,_⟩ := mem_fuksLevel_iff.mp hx
  exact (not_le_of_gt hk) ((fuksPatternCost_lower P).trans hP)

private theorem pattern_card_one_of_minimal {d n : ℕ} [NeZero n]
    (P : FuksPattern d n) (minimal : fuksPatternCost P ≤ d) (k : Fin d) :
    (Finset.univ.image (P k)).card = 1 := by
  have bound (j : Fin d) : 1 ≤ (Finset.univ.image (P j)).card := by
    exact card_pos.mpr ⟨P j 0,mem_image.mpr ⟨0,mem_univ _,rfl⟩⟩
  have eq : (∑ j : Fin d,(Finset.univ.image (P j)).card) = ∑ _j : Fin d,1 := by
    have := fuksPatternCost_lower P
    simpa only [fuksPatternCost,sum_const,card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one] using Nat.le_antisymm minimal this
  exact (sum_eq_sum_iff_of_le (fun j _ => bound j)).mp eq.symm k (mem_univ k) |>.symm

theorem fuksLevel_minimal {d n : ℕ} [NeZero n] :
    fuksLevel d n d = verticalSet d n := by
  ext x
  constructor
  · intro hx
    obtain ⟨P,hP,hx⟩ := mem_fuksLevel_iff.mp hx
    intro i j
    ext l
    have card := pattern_card_one_of_minimal P hP l
    obtain ⟨a,ha⟩ := card_eq_one.mp card
    have same : P l i = P l j := by
      have hi : P l i ∈ ({a} : Finset (Fin n)) := by
        rw [← ha]
        exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
      have hj : P l j ∈ ({a} : Finset (Fin n)) := by
        rw [← ha]
        exact mem_image.mpr ⟨j,mem_univ _,rfl⟩
      exact (mem_singleton.mp hi).trans (mem_singleton.mp hj).symm
    exact hx l i j same l le_rfl
  · intro hx
    refine mem_fuksLevel_iff.mpr ⟨fun _ _ => 0,?_,?_⟩
    · have hconst : (Finset.univ.image (fun _ : Fin n => (0 : Fin n))) = {0} := by
        ext a
        simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
        exact ⟨by rintro ⟨_,rfl⟩; rfl,fun h => ⟨0,h.symm⟩⟩
      simp only [fuksPatternCost,hconst,Finset.card_singleton,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,le_refl]
    · intro k i j _ l _
      exact congrArg (fun u : Space d => u l) (hx i j)

/-- The compactified closed filtration includes the common point at infinity. -/
def compactifiedFuksLevel (d n k : ℕ) : Set (OnePoint (Configuration (d+1) n)) :=
  {∞} ∪ ((↑) '' fuksLevel d n k)

theorem compactifiedFuksLevel_mono (d n : ℕ) :
    Monotone (compactifiedFuksLevel d n) := by
  intro k l hkl
  exact union_subset_union_right _ (Set.image_mono (fuksLevel_mono d n hkl))

theorem compactifiedFuksLevel_minimal {d n : ℕ} [NeZero n] :
    compactifiedFuksLevel d n d = minimalSkeleton d n := by
  rw [compactifiedFuksLevel,fuksLevel_minimal,minimalSkeleton]

theorem compactifiedFuksLevel_top (d n : ℕ) :
    compactifiedFuksLevel d n (d*n) = univ := by
  rw [compactifiedFuksLevel,fuksLevel_top]
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe x => simp

theorem isClosed_compactifiedFuksLevel (d n k : ℕ) :
    IsClosed (compactifiedFuksLevel d n k) := by
  apply (OnePoint.isClosed_iff_of_mem (show (∞ : OnePoint (Configuration (d+1) n)) ∈
    compactifiedFuksLevel d n k from Or.inl rfl)).mpr
  have preimage : ((↑) : Configuration (d+1) n → OnePoint (Configuration (d+1) n)) ⁻¹'
      compactifiedFuksLevel d n k = fuksLevel d n k := by
    ext x
    simp [compactifiedFuksLevel]
  rw [preimage]
  exact isClosed_fuksLevel d n k

/-- A projection to the first k+1 horizontal coordinates, padded with zero.
The padding keeps all projections in one fixed finite-dimensional space. -/
def fuksProjection {d n : ℕ} (x : Configuration (d+1) n) (k : Fin d)
    (i : Fin n) : Fin d → ℝ :=
  fun l => if l ≤ k then (horizontalHeight d (x.val i)).1 l else 0

def fuksComplexity {d n : ℕ} (x : Configuration (d+1) n) : ℕ :=
  ∑ k : Fin d,(Finset.univ.image (fuksProjection x k)).card

private theorem card_image_le_of_fibers {n : ℕ} [NeZero n]
    {α β : Type*} [DecidableEq α] [DecidableEq β] (P : Fin n → α) (Q : Fin n → β)
    (fibers : ∀ i j,P i = P j → Q i = Q j) :
    (Finset.univ.image Q).card ≤ (Finset.univ.image P).card := by
  let f : α → β := fun a => Q (Function.invFun P a)
  have repr (i : Fin n) : f (P i) = Q i := by
    apply fibers
    exact Function.invFun_eq ⟨i,rfl⟩
  have image : (Finset.univ.image P).image f = Finset.univ.image Q := by
    rw [Finset.image_image]
    congr 1
    funext i
    exact repr i
  rw [← image]
  exact Finset.card_image_le

/-- The finite-pattern definition equals the actual coordinate-cardinality
definition of Fox--Neuwirth complexity, rather than a merely formal filtration. -/
theorem mem_fuksLevel_iff_complexity {d n k : ℕ} [NeZero n]
    (x : Configuration (d+1) n) :
    x ∈ fuksLevel d n k ↔ fuksComplexity x ≤ k := by
  classical
  constructor
  · intro hx
    obtain ⟨P,hP,hx⟩ := mem_fuksLevel_iff.mp hx
    apply le_trans _ hP
    apply Finset.sum_le_sum
    intro a _
    apply card_image_le_of_fibers (P a) (fuksProjection x a)
    intro i j he
    funext l
    by_cases hl : l ≤ a
    · simpa only [fuksProjection,hl,if_true] using hx a i j he l hl
    · simp only [fuksProjection,hl,if_false]
  · intro hc
    let P : FuksPattern d n := fun a i =>
      Function.invFun (fuksProjection x a) (fuksProjection x a i)
    have repr (a : Fin d) (i : Fin n) :
        fuksProjection x a (P a i) = fuksProjection x a i :=
      Function.invFun_eq ⟨i,rfl⟩
    refine mem_fuksLevel_iff.mpr ⟨P,le_trans ?_ hc,?_⟩
    · apply Finset.sum_le_sum
      intro a _
      have image : Finset.univ.image (P a) =
          (Finset.univ.image (fuksProjection x a)).image (Function.invFun (fuksProjection x a)) := by
        rw [Finset.image_image]
        rfl
      rw [image]
      exact Finset.card_image_le
    · intro a i j he l hl
      have eq := (repr a i).symm.trans ((congrArg (fuksProjection x a) he).trans (repr a j))
      have h := congrFun eq l
      simpa only [fuksProjection,hl,if_true] using h

theorem fuksProjection_card_mono {d n : ℕ} [NeZero n]
    (x : Configuration (d+1) n) :
    Monotone (fun k : Fin d => (Finset.univ.image (fuksProjection x k)).card) := by
  intro k l hkl
  apply card_image_le_of_fibers (fuksProjection x l) (fuksProjection x k)
  intro i j he
  funext a
  by_cases hak : a ≤ k
  · have hal := hak.trans hkl
    have h := congrFun he a
    simpa only [fuksProjection,hak,hal,if_true] using h
  · simp only [fuksProjection,hak,if_false]

theorem fuksComplexity_relabel {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Configuration (d+1) n) : fuksComplexity (σ • x) = fuksComplexity x := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨σ.symm i,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨σ i,?_⟩
    change fuksProjection x k (σ.symm (σ i)) = fuksProjection x k i
    rw [σ.symm_apply_apply]

theorem smul_mem_fuksLevel_iff {d n k : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) (x : Configuration (d+1) n) :
    σ • x ∈ fuksLevel d n k ↔ x ∈ fuksLevel d n k := by
  rw [mem_fuksLevel_iff_complexity,mem_fuksLevel_iff_complexity,fuksComplexity_relabel]

/-- Every level is preserved by the genuine permutation homeomorphism
of configuration space, with its actual induced subspace topology. -/
def fuksLevelRelabel {d n k : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    fuksLevel d n k ≃ₜ fuksLevel d n k :=
  (relabelConfiguration σ).subtype (fun x => (smul_mem_fuksLevel_iff σ x).symm)

theorem isCompact_compactifiedFuksLevel (d n k : ℕ) :
    IsCompact (compactifiedFuksLevel d n k) :=
  (isClosed_compactifiedFuksLevel d n k).isCompact

end NRR.PrimePowerTopology
