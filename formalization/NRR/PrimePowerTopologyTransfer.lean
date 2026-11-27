import NRR.Binomial
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Powerset

/-!
The signed transfer calculation used in the Fuks cellular obstruction.

This file proves a chain-algebra computation, not the configuration-space
zero theorem.  The later geometric bridge must identify the actual cellular
boundary with these signed sums; that identification is not assumed here.
The calculation follows Karasev--Hubard--Aronov, arXiv:1306.2741v2, §2.4.
-/

noncomputable section
open Finset

namespace NRR.PrimePowerTopology

section Transfer

variable {G R : Type*} [Group G] [Fintype G] [DecidableEq G] [CommRing R]

/-- The oriented elementary chain supported at one group-labelled cell. -/
def orientedCell (χ : G →* Rˣ) (g : G) : G → R :=
  fun h => if h = g then (χ g : R) else 0

/-- Translation of the cell labels. -/
def translateChain (g : G) (c : G → R) : G → R := fun h => c (g⁻¹*h)

/-- Transfer with the orientation character. In the configuration-space
application the character is the sign of the label permutation. -/
def signedTransfer (χ : G →* Rˣ) : (G → R) →ₗ[R] (G → R) where
  toFun c h := ∑ g : G,(χ g : R)*translateChain g c h
  map_add' c d := by
    ext h
    simp only [translateChain,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' r c := by
    ext h
    simp only [translateChain,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring

/-- The basic oriented orbit chain. Its coefficient at the identity is one. -/
def orbitChain (χ : G →* Rˣ) : G → R := fun g => χ g

omit [Fintype G] [DecidableEq G] in
@[simp] theorem orbitChain_one (χ : G →* Rˣ) : orbitChain χ 1 = 1 := by
  simp [orbitChain]

omit [Fintype G] [DecidableEq G] in
theorem orbitChain_ne_zero [Nontrivial R] (χ : G →* Rˣ) : orbitChain χ ≠ 0 := by
  intro he
  have h := congrFun he 1
  simpa only [orbitChain_one,Pi.zero_apply,one_ne_zero] using h

/-- Every signed oriented elementary cell has the same transfer. The two
orientation signs cancel exactly, so all shuffle contributions add. -/
theorem signedTransfer_orientedCell (χ : G →* Rˣ) (g : G) :
    signedTransfer χ (orientedCell χ g) = orbitChain χ := by
  ext h
  change (∑ a : G,(χ a : R)*orientedCell χ g (a⁻¹*h)) = (χ h : R)
  rw [Finset.sum_eq_single (h*g⁻¹)]
  · have he : (h*g⁻¹)⁻¹*h = g := by group
    rw [orientedCell,if_pos he,map_mul,map_inv,Units.val_mul,mul_assoc,
      ← Units.val_mul,inv_mul_cancel,Units.val_one,mul_one]
  · intro a _ hne
    have different : a⁻¹*h ≠ g := by
      intro he
      apply hne
      have hh : h = a*g := (inv_mul_eq_iff_eq_mul).mp he
      rw [hh]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
    simp only [orientedCell,if_neg different,mul_zero]
  · simp

/-- A finite family of signed boundary faces has transfer equal to its
cardinality times the oriented orbit generator. -/
theorem signedTransfer_sum_orientedCell {ι : Type*} (χ : G →* Rˣ)
    (s : Finset ι) (face : ι → G) :
    signedTransfer χ (∑ i ∈ s,orientedCell χ (face i)) = s.card • orbitChain χ := by
  simp only [map_sum,signedTransfer_orientedCell,Finset.sum_const]

end Transfer

/-- The shuffle index is the subset of labels assigned to the first ordered
block; the orders inside both blocks are fixed. -/
abbrev ShuffleIndex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

theorem card_shuffleIndex (n k : ℕ) : Fintype.card (ShuffleIndex n k) = n.choose k := by
  classical
  have he : (Finset.univ : Finset (Fin n)).powersetCard k =
      Finset.univ.filter (fun s : Finset (Fin n) => s.card = k) := by
    ext s
    simp
  rw [Fintype.card_subtype]
  rw [← he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

/-- The source orientation character, before changing coefficients. -/
def permutationOrientation (n : ℕ) : Equiv.Perm (Fin n) →* ℤˣ := Equiv.Perm.sign

/-- The exact integral signed-orbit boundary coefficient of one two-block
shuffle type. This does not assert a geometric attaching-map formula. -/
theorem transfer_shuffle_faces (n k : ℕ)
    (face : ShuffleIndex n k → Equiv.Perm (Fin n)) :
    signedTransfer (permutationOrientation n)
      (∑ s : ShuffleIndex n k,orientedCell (permutationOrientation n) (face s)) =
        n.choose k • orbitChain (permutationOrientation n) := by
  simpa only [Finset.card_univ,card_shuffleIndex]
    using signedTransfer_sum_orientedCell (permutationOrientation n) Finset.univ face

end NRR.PrimePowerTopology
