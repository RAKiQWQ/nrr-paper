import NRR.PrimePowerExistenceConfiguration
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup

/-! The regular finite-group action used when restricting the symmetric-group
configuration problem to a prime-power subgroup. -/

noncomputable section
open Finset

namespace NRR.PrimePower

/-- Transport left multiplication by a group to a permutation of the cell
labels. This applies in particular to elementary abelian p-groups. -/
def regularPermutation {G : Type*} [Group G] {n : ℕ} (e : G ≃ Fin n) :
    G →* Equiv.Perm (Fin n) where
  toFun g := (e.symm.trans (Equiv.mulLeft g)).trans e
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp

@[simp]
theorem regularPermutation_apply {G : Type*} [Group G] {n : ℕ} (e : G ≃ Fin n)
    (g : G) (i : Fin n) : regularPermutation e g i = e (g * e.symm i) := rfl

theorem regularPermutation_injective {G : Type*} [Group G] {n : ℕ} (e : G ≃ Fin n) :
    Function.Injective (regularPermutation e) := by
  intro g h he
  have hv := congrArg (fun σ : Equiv.Perm (Fin n) => σ (e 1)) he
  apply e.injective
  simpa only [regularPermutation_apply, Equiv.symm_apply_apply, mul_one] using hv

/-- The regular action is transitive on labels, with an explicit translator. -/
theorem regularPermutation_transitive {G : Type*} [Group G] {n : ℕ} (e : G ≃ Fin n)
    (i j : Fin n) : ∃ g : G, regularPermutation e g i = j := by
  refine ⟨e.symm j * (e.symm i)⁻¹, ?_⟩
  change e ((e.symm j * (e.symm i)⁻¹) * e.symm i) = j
  simp only [mul_assoc, inv_mul_cancel, mul_one, Equiv.apply_symm_apply]

/-- Restricting the configuration action to the regular subgroup remains free. -/
theorem regular_configuration_action_free {G : Type*} [Group G] {d n : ℕ}
    (e : G ≃ Fin n) (g : G) (x : Configuration d n)
    (h : regularPermutation e g • x = x) : g = 1 := by
  apply regularPermutation_injective e
  simpa only [map_one] using configuration_action_free (regularPermutation e g) x h

/-- The reduced representation has no vector fixed by the entire regular
subgroup except zero. This does not claim that each nonidentity element acts
freely on its sphere. -/
theorem regular_invariant_values_zero {G : Type*} [Group G] {d n : ℕ}
    (e : G ≃ Fin n) (hn : 0 < n) (v : ReducedValues d n)
    (fixed : ∀ g : G, regularPermutation e g • v = v) : v = 0 := by
  have same (k : Fin (d - 1)) (i j : Fin n) : v.val k i = v.val k j := by
    obtain ⟨g, hg⟩ := regularPermutation_transitive e i j
    have hv := congrArg (fun w : ReducedValues d n => w.val k (regularPermutation e g i)) (fixed g)
    change v.val k ((regularPermutation e g).symm (regularPermutation e g i)) =
      v.val k (regularPermutation e g i) at hv
    rw [Equiv.symm_apply_apply, hg] at hv
    exact hv
  apply Subtype.ext
  funext k i
  have hs : (∑ j, v.val k j) = (n : ℝ) * v.val k i := by
    calc
      _ = ∑ _j : Fin n, v.val k i := sum_congr rfl (fun j _ => same k j i)
      _ = _ := by simp
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : (n : ℝ) * v.val k i = 0 := hs.symm.trans (v.property k)
  exact (mul_eq_zero.mp hz).resolve_left hnr

/-- The elementary abelian group providing the regular prime-power subgroup. -/
abbrev ElementaryGroup (p k : ℕ) := Multiplicative (Fin k → ZMod p)

def primePowerLabels (p k : ℕ) [NeZero p] : ElementaryGroup p k ≃ Fin (p ^ k) :=
  Fintype.equivFinOfCardEq (by simp [ElementaryGroup])

theorem elementaryGroup_isPGroup (p k : ℕ) [NeZero p] : IsPGroup p (ElementaryGroup p k) := by
  apply IsPGroup.of_card (n := k)
  simp [Nat.card_eq_fintype_card, ElementaryGroup]

theorem primePower_configuration_action_free (p k d : ℕ) [NeZero p]
    (g : ElementaryGroup p k) (x : Configuration d (p ^ k))
    (h : regularPermutation (primePowerLabels p k) g • x = x) : g = 1 :=
  regular_configuration_action_free (primePowerLabels p k) g x h

theorem primePower_invariant_values_zero (p k d : ℕ) [NeZero p]
    (v : ReducedValues d (p ^ k))
    (fixed : ∀ g : ElementaryGroup p k, regularPermutation (primePowerLabels p k) g • v = v) :
    v = 0 :=
  regular_invariant_values_zero (primePowerLabels p k)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) k) v fixed

end NRR.PrimePower
