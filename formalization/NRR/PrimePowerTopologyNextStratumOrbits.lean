import NRR.PrimePowerTopologyNextStratum
import NRR.PrimePowerTopologyShuffleGeometry
import Mathlib.Order.Interval.Finset.Fin

/-! The genuine first nonminimal Fuks stratum has exactly the nontrivial
split sizes as its two-column orbit types. -/

noncomputable section
open Set Topology Finset
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

theorem twoColumnChart_reindex {d n : ℕ} (S T : Finset (Fin n))
    (h : S.card = T.card) (p : twoColumnDomain (d := d) S) :
    ∃ q : twoColumnDomain (d := d) T,
      twoColumnMap S p = columnShufflePerm S T h • twoColumnMap T q := by
  classical
  let τ := columnShufflePerm S T h
  let q : TwoColumnAmbientParameters d n :=
    ((p.val.1.1, fun i => p.val.1.2 (τ i)), p.val.2)
  have hq : q ∈ twoColumnDomain T := by
    refine ⟨p.property.1, ?_⟩
    intro i j hij hmem
    have same : τ i ∈ S ↔ τ j ∈ S := by
      simpa only [τ, columnShufflePerm_mem_iff] using hmem
    exact p.property.2 (τ i) (τ j)
      (isColumnShuffle_columnShufflePerm S T h i j hij same) same
  have he : twoColumnMap T ⟨q, hq⟩ = τ.symm • twoColumnMap S p := by
    apply Subtype.ext
    funext i
    change (horizontalHeight (d+1)).symm
        ((horizontalHeight d).symm
          (p.val.1.1.1, if i ∈ T then p.val.1.1.2 else p.val.1.1.2+p.val.2),
          p.val.1.2 (τ i)) =
      (horizontalHeight (d+1)).symm
        ((horizontalHeight d).symm
          (p.val.1.1.1, if τ.symm.symm i ∈ S then p.val.1.1.2 else p.val.1.1.2+p.val.2),
          p.val.1.2 (τ.symm.symm i))
    simp only [Equiv.symm_symm, τ, columnShufflePerm_mem_iff]
  refine ⟨⟨q, hq⟩, ?_⟩
  change twoColumnMap S p = τ • twoColumnMap T ⟨q, hq⟩
  rw [he, smul_smul]
  rw [show τ * τ.symm = 1 from mul_inv_cancel τ, one_smul]

/-- The canonical left block for a nontrivial split of n labels. -/
def firstColumnLabels (n k : ℕ) (hk : k < n) : Finset (Fin n) :=
  Finset.Iio ⟨k, hk⟩

@[simp] theorem card_firstColumnLabels (n k : ℕ) (hk : k < n) :
    (firstColumnLabels n k hk).card = k := by
  exact Fin.card_Iio _

@[simp] theorem mem_firstColumnLabels (n k : ℕ) (hk : k < n) (i : Fin n) :
    i ∈ firstColumnLabels n k hk ↔ i.val < k := by
  exact Finset.mem_Iio

theorem nonempty_firstColumnLabels (n k : ℕ) (hk : k < n) (hk0 : 0 < k) :
    (firstColumnLabels n k hk).Nonempty := by
  rw [← Finset.card_pos, card_firstColumnLabels]
  exact hk0

theorem proper_firstColumnLabels (n k : ℕ) (hk : k < n) :
    firstColumnLabels n k hk ≠ Finset.univ := by
  intro he
  have hv := congrArg Finset.card he
  simp only [card_firstColumnLabels, Finset.card_univ, Fintype.card_fin] at hv
  omega

/-- Every actual first-nonminimal point is a relabeling of one of the
canonical charts with k left labels, where 1 ≤ k < n. -/
theorem nextFuks_exists_splitSize_chart {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2))
    (hnv : x ∉ verticalSet (d+1) n) :
    ∃ (k : ℕ) (hk : k < n) (σ : Equiv.Perm (Fin n))
      (p : twoColumnDomain (d := d) (firstColumnLabels n k hk)),
      0 < k ∧ x = σ • twoColumnMap (firstColumnLabels n k hk) p := by
  classical
  obtain ⟨σ, S, p, hne, hproper, he⟩ := nextFuks_exists_twoColumnChart x hx hnv
  have hk : S.card < n := by
    have hs : S ⊂ (Finset.univ : Finset (Fin n)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hproper⟩
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hs
  let T := firstColumnLabels n S.card hk
  have hcard : S.card = T.card := (card_firstColumnLabels n S.card hk).symm
  obtain ⟨q, hq⟩ := twoColumnChart_reindex S T hcard p
  refine ⟨S.card, hk, σ * columnShufflePerm S T hcard, q,
    Finset.card_pos.mpr hne, ?_⟩
  rw [he, hq, smul_smul]

theorem mem_nextFuks_diff_vertical_iff_splitSize {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n) :
    x ∈ fuksLevel (d+1) n (d+2) ∧ x ∉ verticalSet (d+1) n ↔
      ∃ (k : ℕ) (hk : k < n) (σ : Equiv.Perm (Fin n))
        (p : twoColumnDomain (d := d) (firstColumnLabels n k hk)),
        0 < k ∧ x = σ • twoColumnMap (firstColumnLabels n k hk) p := by
  constructor
  · rintro ⟨hx, hnv⟩
    exact nextFuks_exists_splitSize_chart x hx hnv
  · rintro ⟨k, hk, σ, p, hk0, he⟩
    exact (mem_nextFuks_diff_vertical_iff x).mpr
      ⟨σ, firstColumnLabels n k hk, p,
        nonempty_firstColumnLabels n k hk hk0, proper_firstColumnLabels n k hk, he⟩

end NRR.PrimePowerTopology
