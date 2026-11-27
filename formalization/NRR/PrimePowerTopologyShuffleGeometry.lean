import NRR.PrimePowerTopologyTwoColumns
import NRR.PrimePowerTopologyTransfer
import Mathlib.Data.Finset.Sort

/-! The actual order-preserving permutations of the two-column boundary.
Their labels are in bijection with subsets of positions, not merely an
abstract family chosen to have the desired binomial cardinality. -/

noncomputable section
open Set Finset

namespace NRR.PrimePowerTopology

local instance shuffleGeometryPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private def finsetSumComplEquiv {n : ℕ} (S : Finset (Fin n)) :
    (S ⊕ ↥(Sᶜ : Finset (Fin n))) ≃ Fin n := by
  classical
  exact
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun i => if h : i ∈ S then Sum.inl ⟨i, h⟩
        else Sum.inr ⟨i, Finset.mem_compl.mpr h⟩
      left_inv := by
        intro i
        cases i with
        | inl i => simp [i.property]
        | inr i => simp [Finset.mem_compl.mp i.property]
      right_inv := by intro i; by_cases hi : i ∈ S <;> simp [hi] }

private def subsetOrderIso {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    S ≃o T :=
  (S.orderIsoOfFin rfl).symm.trans (T.orderIsoOfFin h.symm)

/-- The unique permutation taking a prescribed position subset to the left
column and preserving the internal order in both columns. -/
def columnShufflePerm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    Equiv.Perm (Fin n) := by
  classical
  have hc : (Tᶜ : Finset (Fin n)).card = (Sᶜ : Finset (Fin n)).card := by
    simp only [Finset.card_compl, Fintype.card_fin]
    omega
  exact (finsetSumComplEquiv T).symm.trans
    ((Equiv.sumCongr (subsetOrderIso T S h.symm).toEquiv
      (subsetOrderIso Tᶜ Sᶜ hc).toEquiv).trans (finsetSumComplEquiv S))

theorem columnShufflePerm_apply_of_mem {n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) {i : Fin n} (hi : i ∈ T) :
    columnShufflePerm S T h i = (subsetOrderIso T S h.symm ⟨i, hi⟩).val := by
  classical
  simp [columnShufflePerm, finsetSumComplEquiv, hi]

theorem columnShufflePerm_apply_of_notMem {n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) {i : Fin n} (hi : i ∉ T) :
    columnShufflePerm S T h i =
      (subsetOrderIso Tᶜ Sᶜ (by simp only [Finset.card_compl, Fintype.card_fin]; omega)
        ⟨i, Finset.mem_compl.mpr hi⟩).val := by
  classical
  simp [columnShufflePerm, finsetSumComplEquiv, hi]

theorem columnShufflePerm_mem_iff {n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) (i : Fin n) :
    columnShufflePerm S T h i ∈ S ↔ i ∈ T := by
  classical
  by_cases hi : i ∈ T
  · rw [columnShufflePerm_apply_of_mem S T h hi]
    exact iff_of_true (Subtype.property _) hi
  · rw [columnShufflePerm_apply_of_notMem S T h hi]
    exact iff_of_false (Finset.mem_compl.mp (Subtype.property _)) hi

theorem isColumnShuffle_columnShufflePerm {n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) : IsColumnShuffle S (columnShufflePerm S T h) := by
  classical
  intro i j hij hmem
  have same : i ∈ T ↔ j ∈ T := by
    simpa only [columnShufflePerm_mem_iff] using hmem
  by_cases hi : i ∈ T
  · have hj := same.mp hi
    rw [columnShufflePerm_apply_of_mem S T h hi, columnShufflePerm_apply_of_mem S T h hj]
    exact (subsetOrderIso T S h.symm).strictMono hij
  · have hj : j ∉ T := fun hj => hi (same.mpr hj)
    rw [columnShufflePerm_apply_of_notMem S T h hi,
      columnShufflePerm_apply_of_notMem S T h hj]
    exact (subsetOrderIso Tᶜ Sᶜ _).strictMono hij

/-- The positions occupied by labels of the left column. -/
def columnShufflePositions {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => σ i ∈ S)

@[simp] theorem mem_columnShufflePositions {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∈ columnShufflePositions S σ ↔ σ i ∈ S := by
  classical
  simp [columnShufflePositions]

theorem card_columnShufflePositions {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) : (columnShufflePositions S σ).card = S.card := by
  classical
  have he : (columnShufflePositions S σ).image σ = S := by
    ext i
    simp only [Finset.mem_image, mem_columnShufflePositions]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      exact ⟨σ.symm i, by simpa using hi, σ.apply_symm_apply i⟩
  calc
    _ = ((columnShufflePositions S σ).image σ).card :=
      (Finset.card_image_of_injective _ σ.injective).symm
    _ = S.card := congrArg Finset.card he

private theorem shuffle_orderEmb_eq {n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle S σ) (hm : ∀ i, σ i ∈ S ↔ i ∈ T) :
    (fun j => σ (T.orderEmbOfFin rfl j)) = S.orderEmbOfFin h := by
  apply Finset.orderEmbOfFin_unique h
  · intro j
    exact (hm _).mpr (T.orderEmbOfFin_mem rfl j)
  · intro i j hij
    apply hs _ _ ((T.orderEmbOfFin rfl).strictMono hij)
    exact iff_of_true ((hm _).mpr (T.orderEmbOfFin_mem rfl i))
      ((hm _).mpr (T.orderEmbOfFin_mem rfl j))

theorem columnShuffle_unique_of_positions {n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) (σ τ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle S σ) (ht : IsColumnShuffle S τ)
    (hmσ : ∀ i, σ i ∈ S ↔ i ∈ T) (hmτ : ∀ i, τ i ∈ S ↔ i ∈ T) : σ = τ := by
  classical
  have positive := (shuffle_orderEmb_eq S T h σ hs hmσ).trans
    (shuffle_orderEmb_eq S T h τ ht hmτ).symm
  have hcomp : (Sᶜ : Finset (Fin n)).card = (Tᶜ : Finset (Fin n)).card := by
    simp only [Finset.card_compl, Fintype.card_fin]
    omega
  have hscomp : IsColumnShuffle Sᶜ σ := by
    intro i j hij hmem
    apply hs i j hij
    simpa only [Finset.mem_compl, not_iff_not] using hmem
  have htcomp : IsColumnShuffle Sᶜ τ := by
    intro i j hij hmem
    apply ht i j hij
    simpa only [Finset.mem_compl, not_iff_not] using hmem
  have hmσcomp : ∀ i, σ i ∈ Sᶜ ↔ i ∈ Tᶜ := by
    intro i
    simpa only [Finset.mem_compl] using not_congr (hmσ i)
  have hmτcomp : ∀ i, τ i ∈ Sᶜ ↔ i ∈ Tᶜ := by
    intro i
    simpa only [Finset.mem_compl] using not_congr (hmτ i)
  have negative := (shuffle_orderEmb_eq Sᶜ Tᶜ hcomp σ hscomp hmσcomp).trans
    (shuffle_orderEmb_eq Sᶜ Tᶜ hcomp τ htcomp hmτcomp).symm
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ T
  · obtain ⟨j, hj⟩ := (T.orderIsoOfFin rfl).surjective ⟨i, hi⟩
    have hv : T.orderEmbOfFin rfl j = i := congrArg Subtype.val hj
    simpa only [hv] using congrFun positive j
  · obtain ⟨j, hj⟩ := (Tᶜ.orderIsoOfFin rfl).surjective ⟨i, Finset.mem_compl.mpr hi⟩
    have hv : Tᶜ.orderEmbOfFin rfl j = i := congrArg Subtype.val hj
    simpa only [hv] using congrFun negative j

/-- Actual order-preserving two-column boundary permutations are in bijection
with the subsets of positions of the precise left-column cardinality. -/
def columnShuffleEquiv {n : ℕ} (S : Finset (Fin n)) :
    {σ : Equiv.Perm (Fin n) // IsColumnShuffle S σ} ≃ ShuffleIndex n S.card where
  toFun σ := ⟨columnShufflePositions S σ.val, card_columnShufflePositions S σ.val⟩
  invFun T := ⟨columnShufflePerm S T.val T.property.symm,
    isColumnShuffle_columnShufflePerm S T.val T.property.symm⟩
  left_inv σ := by
    apply Subtype.ext
    change columnShufflePerm S (columnShufflePositions S σ.val)
      (card_columnShufflePositions S σ.val).symm = σ.val
    apply columnShuffle_unique_of_positions S (columnShufflePositions S σ.val)
      (card_columnShufflePositions S σ.val).symm
      (columnShufflePerm S (columnShufflePositions S σ.val)
        (card_columnShufflePositions S σ.val).symm) σ.val
      (isColumnShuffle_columnShufflePerm S (columnShufflePositions S σ.val)
        (card_columnShufflePositions S σ.val).symm) σ.property
    · exact columnShufflePerm_mem_iff S _ _
    · intro i
      exact (mem_columnShufflePositions S σ.val i).symm
  right_inv T := by
    apply Subtype.ext
    ext i
    rw [mem_columnShufflePositions, columnShufflePerm_mem_iff]

theorem card_actualColumnShuffles {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card {σ : Equiv.Perm (Fin n) // IsColumnShuffle S σ} = n.choose S.card := by
  classical
  exact (Fintype.card_congr (columnShuffleEquiv S)).trans (card_shuffleIndex n S.card)

/-- The already proved signed transfer formula, now indexed by exactly the
actual order-preserving boundary chambers of the two-column chart. This is
the combinatorial coefficient; its local homological degrees are separate. -/
theorem transfer_actualColumnShuffles {n : ℕ} (S : Finset (Fin n)) :
    signedTransfer (permutationOrientation n)
        (∑ σ : {σ : Equiv.Perm (Fin n) // IsColumnShuffle S σ},
          orientedCell (permutationOrientation n) σ.val) =
      n.choose S.card • orbitChain (permutationOrientation n) := by
  classical
  simpa only [Finset.card_univ, card_actualColumnShuffles] using
    signedTransfer_sum_orientedCell (permutationOrientation n)
      (Finset.univ : Finset {σ : Equiv.Perm (Fin n) // IsColumnShuffle S σ}) Subtype.val

end NRR.PrimePowerTopology
