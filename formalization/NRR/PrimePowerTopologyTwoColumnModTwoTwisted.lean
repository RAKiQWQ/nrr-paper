import NRR.PrimePowerTopologyMinimalTwistedProjection
import NRR.PrimePowerTopologyTwoColumnModTwo
import NRR.PrimePowerTopologyTwoColumnRelabel
import NRR.PrimePowerTopologyBoundary

/-! The actual twisted first differential on projections of the canonical
two-column disk classes, with coefficients in the field of two elements. -/

noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

private theorem minimalProjection_modTwo_at_degree
    {D n q : ℕ} [NeZero n] (hd : 0 < D) (hq : q = D+n)
    (χ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (i₀ : Fin n)
    (z : (fuksRelativeComplex (ZMod 2) (d := D) (n := n)
      (show D-1 ≤ D by omega)).homology q) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := D) χ
      (show D-1 ≤ D by omega)) q z =
      (∑ σ : Equiv.Perm (Fin n), coherentMinimalRelativeCoefficient (ZMod 2) hd i₀ σ
        (eqToHom (congrArg (fun k => (fuksRelativeComplex (ZMod 2) (d := D) (n := n)
          (show D-1 ≤ D by omega)).homology k) hq) z)) •
      eqToHom (congrArg (fun k => (twistedFuksRelativeComplex (ZMod 2) (d := D) χ
        (show D-1 ≤ D by omega)).homology k) hq.symm)
        (coherentTwistedMinimalClass (ZMod 2) χ hd i₀) := by
  subst q
  have hχ (σ : Equiv.Perm (Fin n)) : (χ σ : ZMod 2) = 1 :=
    congrArg Units.val (Subsingleton.elim (χ σ) 1)
  simpa only [hχ, mul_one, eqToHom_refl, ModuleCat.id_apply] using
    minimalTwistedProjection_eq_character_sum (ZMod 2) χ hd i₀ z

/-- In the genuine twisted group the boundary of the projected disk class
is the binomial coefficient times the coherent minimum class. -/
theorem twistedFuksDifferential_modTwo_projected_basis {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (split : TwoColumnSplit n)
    (i₀ : Fin n) :
    twistedFuksDifferential (ZMod 2) (d := d+1) χ (show d ≤ d+1 by omega)
      (show d+1 ≤ d+2 by omega) (d+n+1)
      (HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1) χ
        (show d+1 ≤ d+2 by omega)) (d+n+2)
        (twoColumnFuksBasis (ZMod 2) d n hn (split,1))) =
      (n.choose split.val.val : ZMod 2) •
        eqToHom (congrArg (fun k => (twistedFuksRelativeComplex (ZMod 2) (d := d+1) χ
          (show d ≤ d+1 by omega)).homology k) (show (d+1)+n = d+n+1 by omega))
          (coherentTwistedMinimalClass (ZMod 2) χ (show 0 < d+1 by omega) i₀) := by
  let x := twoColumnFuksBasis (ZMod 2) d n hn (split,1)
  have h := fuksDifferential_projection (ZMod 2) (d := d+1) χ (Nat.le_succ d)
    (Nat.le_succ (d+1)) (d+n+1)
  let z := fuksDifferential (ZMod 2) (d := d+1) (n := n) (Nat.le_succ d)
    (Nat.le_succ (d+1)) (d+n+1) x
  let g := eqToHom (congrArg (fun k => (twistedFuksRelativeComplex (ZMod 2) (d := d+1) χ
    (Nat.le_succ d)).homology k) (show (d+1)+n = d+n+1 by omega))
      (coherentTwistedMinimalClass (ZMod 2) χ (show 0 < d+1 by omega) i₀)
  have h₁ := congrArg (fun f : (fuksRelativeComplex (ZMod 2) (d := d+1) (n := n)
    (Nat.le_succ (d+1))).homology (d+n+2) ⟶ (twistedFuksRelativeComplex (ZMod 2)
      (d := d+1) χ (Nat.le_succ d)).homology (d+n+1) => f x) h.symm
  have h₂ := minimalProjection_modTwo_at_degree (D := d+1) (n := n) (q := d+n+1)
    (by omega) (by omega) χ i₀ z
  have h₃ := congrArg (fun r : ZMod 2 => r • g)
    (sum_twoColumnMinimalRelativeCoefficient_fuksDifferential_modTwo (d := d) hn split i₀)
  exact h₁.trans (h₂.trans h₃)

/-- At a power of two the projected canonical two-column disks have zero
twisted boundary. This assertion covers every nontrivial split size. -/
theorem twistedFuksDifferential_projected_basis_two_pow {d n a : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (hpow : n = 2^a)
    (split : TwoColumnSplit n) :
    twistedFuksDifferential (ZMod 2) (d := d+1) χ (show d ≤ d+1 by omega)
      (show d+1 ≤ d+2 by omega) (d+n+1)
      (HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1) χ
        (show d+1 ≤ d+2 by omega)) (d+n+2)
        (twoColumnFuksBasis (ZMod 2) d n hn (split,1))) = 0 := by
  subst n
  rw [twistedFuksDifferential_modTwo_projected_basis χ hn split 0]
  let i : Fin (2^a-1) := ⟨split.val.val-1, by
    have := split.val.isLt
    have := split.property
    omega⟩
  have hi : i.val+1 = split.val.val := Nat.sub_add_cancel split.property
  rw [← hi, primePower_choose_mod_zero Nat.prime_two i, zero_smul]

/-- Modulo two, the projected two-column class only depends on the split
size. This is the group action on actual singular pair homology. -/
theorem twoColumnFuksBasis_modTwo_projection_relabel {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (split : TwoColumnSplit n)
    (σ : Equiv.Perm (Fin n)) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1) χ
      (Nat.le_succ (d+1))) (d+n+2) (twoColumnFuksBasis (ZMod 2) d n hn (split,σ)) =
    HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1) χ
      (Nat.le_succ (d+1))) (d+n+2) (twoColumnFuksBasis (ZMod 2) d n hn (split,1)) := by
  let x := twoColumnFuksBasis (ZMod 2) d n hn (split,1)
  let π := twistedFuksRelativeProj (ZMod 2) (d := d+1) χ (Nat.le_succ (d+1))
  let ρ := fuksRelativeRelabel (ZMod 2) (d := d+1) (Nat.le_succ (d+1)) σ
  have hχ : (χ σ : ZMod 2) = 1 := congrArg Units.val (Subsingleton.elim (χ σ) 1)
  have h : ρ ≫ π = π := by
    dsimp only [ρ, π]
    rw [fuksRelativeRelabel_proj, hχ, one_smul]
  have hr : HomologicalComplex.homologyMap ρ (d+n+2) x =
      twoColumnFuksBasis (ZMod 2) d n hn (split,σ) := by
    simpa only [mul_one] using
      twoColumnFuksBasis_relabel (ZMod 2) (d := d) hn (split,1) σ
  rw [← hr]
  exact congrArg (fun f : (fuksRelativeComplex (ZMod 2) (d := d+1) (n := n)
    (Nat.le_succ (d+1))).homology (d+n+2) ⟶ (twistedFuksRelativeComplex (ZMod 2)
      (d := d+1) χ (Nat.le_succ (d+1))).homology (d+n+2) => f x)
    ((HomologicalComplex.homologyMap_comp ρ π (d+n+2)).symm.trans
      (congrArg (fun f => HomologicalComplex.homologyMap f (d+n+2)) h))

/-- At powers of two, the twisted first differential annihilates the image
of the entire ordinary source, in every label order and for all linear
combinations of the two-column basis. -/
@[reassoc]
theorem projection_comp_twistedFuksDifferential_two_pow {d n a : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (hpow : n = 2^a) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1) χ
      (Nat.le_succ (d+1))) (d+n+2) ≫
      twistedFuksDifferential (ZMod 2) (d := d+1) χ (Nat.le_succ d)
        (Nat.le_succ (d+1)) (d+n+1) = 0 := by
  apply ModuleCat.hom_ext
  apply (twoColumnFuksBasis (ZMod 2) d n hn).ext
  intro ⟨split,σ⟩
  change twistedFuksDifferential (ZMod 2) (d := d+1) χ (Nat.le_succ d)
    (Nat.le_succ (d+1)) (d+n+1)
    (HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1) χ
      (Nat.le_succ (d+1))) (d+n+2) (twoColumnFuksBasis (ZMod 2) d n hn (split,σ))) = 0
  rw [twoColumnFuksBasis_modTwo_projection_relabel χ hn split σ]
  exact twistedFuksDifferential_projected_basis_two_pow χ hn hpow split

end NRR.PrimePowerTopology
