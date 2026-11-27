import NRR.PrimePowerTopologyTransfer
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
The lowest nonzero degree of the signed cellular chain calculation.

The incoming matrix has the internal binomial coefficients as its columns.
For n=p^a its reduction modulo p vanishes and the oriented orbit generator
has nonzero class in the explicit quotient. This is an algebraic quotient;
the identification with actual configuration-space homology is not asserted
by this file.
-/

noncomputable section
open Finset

namespace NRR.PrimePowerTopology

/-- The incoming scalar matrix, with one column for every nontrivial split
of the ordered vertical labels into two nonempty blocks. -/
def binomialBoundary (R : Type*) [CommRing R] (n : ℕ) :
    (Fin (n-1) → R) →ₗ[R] R where
  toFun c := ∑ i : Fin (n-1),(n.choose (i.val+1) : R)*c i
  map_add' c d := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The corresponding incoming matrix before collapsing the oriented
permutation orbit to its one-dimensional coefficient module. -/
def orbitBoundary {R : Type*} [CommRing R] {G : Type*} [Group G]
    (χ : G →* Rˣ) (n : ℕ) : (Fin (n-1) → R) →ₗ[R] (G → R) :=
  (binomialBoundary R n).smulRight (orbitChain χ)

theorem primePower_choose_mod_zero {p a : ℕ} (hp : p.Prime)
    (i : Fin (p^a-1)) : (Nat.choose (p^a) (i.val+1) : ZMod p) = 0 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  exact hp.dvd_choose_pow (by omega) (by have := i.isLt; omega)

/-- Every incoming boundary coefficient vanishes modulo the prime. -/
theorem binomialBoundary_primePower_zero {p a : ℕ} (hp : p.Prime) :
    binomialBoundary (ZMod p) (p^a) = 0 := by
  apply LinearMap.ext
  intro c
  change (∑ i : Fin (p^a-1),(Nat.choose (p^a) (i.val+1) : ZMod p)*c i) = 0
  simp only [primePower_choose_mod_zero hp,zero_mul,Finset.sum_const_zero]

theorem orbitBoundary_primePower_zero {p a : ℕ} (hp : p.Prime)
    {G : Type*} [Group G] (χ : G →* (ZMod p)ˣ) :
    orbitBoundary χ (p^a) = 0 := by
  rw [orbitBoundary,binomialBoundary_primePower_zero hp]
  ext c h
  simp

/-- The oriented minimal chain is not a boundary in this matrix, in every
prime-power size and for every unit-valued orientation character. -/
theorem orbit_not_boundary_primePower {p a : ℕ} (hp : p.Prime)
    {G : Type*} [Group G] (χ : G →* (ZMod p)ˣ) :
    orbitChain χ ∉ LinearMap.range (orbitBoundary χ (p^a)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [orbitBoundary_primePower_zero hp,LinearMap.range_zero]
  simpa only [Submodule.mem_bot] using orbitChain_ne_zero χ

/-- The explicit lowest-degree quotient in the signed boundary calculation. -/
abbrev BoundaryQuotient {R : Type*} [CommRing R] {G : Type*} [Group G]
    (χ : G →* Rˣ) (n : ℕ) := (G → R) ⧸ LinearMap.range (orbitBoundary χ n)

/-- The quotient class represented by the sum of the oriented minimal
cells is provably nonzero modulo p. -/
theorem orbit_class_nonzero_primePower {p a : ℕ} (hp : p.Prime)
    {G : Type*} [Group G] (χ : G →* (ZMod p)ˣ) :
    (Submodule.mkQ (LinearMap.range (orbitBoundary χ (p^a)))) (orbitChain χ) ≠ 0 := by
  intro he
  apply orbit_not_boundary_primePower hp χ
  have hk : orbitChain χ ∈ LinearMap.ker
      (Submodule.mkQ (LinearMap.range (orbitBoundary χ (p^a)))) := he
  rwa [Submodule.ker_mkQ] at hk

/-- Changing the source orientation character to prime coefficients. -/
def permutationOrientationMod (p n : ℕ) : Equiv.Perm (Fin n) →* (ZMod p)ˣ :=
  (Units.map (Int.castRingHom (ZMod p)).toMonoidHom).comp (permutationOrientation n)

theorem minimal_orbit_class_nonzero {p a : ℕ} (hp : p.Prime) :
    (Submodule.mkQ (LinearMap.range
      (orbitBoundary (permutationOrientationMod p (p^a)) (p^a))))
        (orbitChain (permutationOrientationMod p (p^a))) ≠ 0 :=
  orbit_class_nonzero_primePower hp _

end NRR.PrimePowerTopology
