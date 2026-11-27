import NRR.PrimePowerTopologyShuffleIncidenceOrientation
import NRR.PrimePowerTopologyTwistedFuksBM

/-! Prime-power persistence for the genuine sign-twisted Fuks complex.
The actual shuffle incidence signs cancel the coefficient character. Thus
the first boundary is a proper binomial coefficient times a common genuine
disk incidence, and vanishes over every prime field at prime-power size.
The surviving class is transported to the full configuration BM complex. -/

noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- The sign character cancels the sign of a genuine shuffle incidence.
The common incidence amplitude need not be normalized to one. -/
theorem twoColumnDiskIncidenceCoefficient_sign_twist
    (p : ℕ) {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    twoColumnDiskIncidenceCoefficient (ZMod p) (d := d) split i₀ σ 1 *
        (permutationOrientationMod p n σ : ZMod p) =
      twoColumnDiskIncidenceCoefficient (ZMod p) (d := d) split i₀ 1 1 := by
  rw [twoColumnDiskIncidenceCoefficient_of_shuffle (ZMod p) (d := d) split i₀ σ hs]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [permutationOrientationMod, permutationOrientation, h]

/-- Summing the actual, character-weighted first differential counts all
legal shuffles with the same genuine incidence amplitude. -/
theorem sum_twoColumnMinimalRelativeCoefficient_fuksDifferential_sign
    (p : ℕ) {d n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (split : TwoColumnSplit n) (i₀ : Fin n) :
    (∑ σ : Equiv.Perm (Fin n),
      twoColumnMinimalRelativeCoefficient (ZMod p) d n i₀ σ
        (fuksDifferential (ZMod p) (d := d+1) (n := n) (Nat.le_succ d)
          (Nat.le_succ (d+1)) (d+n+1)
          (twoColumnFuksBasis (ZMod p) d n hn (split,1))) *
            (permutationOrientationMod p n σ : ZMod p)) =
      (n.choose split.val.val : ZMod p) *
        twoColumnDiskIncidenceCoefficient (ZMod p) (d := d) split i₀ 1 1 := by
  classical
  calc
    _ = (∑ σ : Equiv.Perm (Fin n),
        if IsColumnShuffle (canonicalColumnLabels split) σ then (1 : ZMod p) else 0) *
          twoColumnDiskIncidenceCoefficient (ZMod p) (d := d) split i₀ 1 1 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      rw [twoColumnMinimalRelativeCoefficient_fuksDifferential]
      by_cases hs : IsColumnShuffle (canonicalColumnLabels split) σ
      · rw [if_pos hs, one_mul]
        exact twoColumnDiskIncidenceCoefficient_sign_twist p split i₀ σ hs
      · rw [if_neg hs, zero_mul,
          twoColumnDiskIncidenceCoefficient_eq_zero_of_not_shuffle (ZMod p) split i₀ σ hs]
        simp
    _ = _ := by
      rw [Finset.sum_boole, ← Fintype.card_subtype, card_actualColumnShuffles,
        canonicalColumnLabels, card_firstColumnLabels]

/-- Every proper split has a prime-divisible number of actual shuffles. -/
theorem prime_dvd_choose_of_primePower_split {p n a : ℕ}
    (hp : p.Prime) (hpow : n = p^a) (split : TwoColumnSplit n) :
    p ∣ n.choose split.val.val := by
  subst n
  exact hp.dvd_choose_pow (by have := split.property; omega)
    (by have := split.val.isLt; omega)

theorem primePower_choose_split_mod_zero {p n a : ℕ}
    (hp : p.Prime) (hpow : n = p^a) (split : TwoColumnSplit n) :
    (n.choose split.val.val : ZMod p) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (prime_dvd_choose_of_primePower_split hp hpow split)

private theorem minimalProjection_sign_at_degree
    (p : ℕ) {D n q : ℕ} [NeZero n] (hd : 0 < D) (hq : q = D+n)
    (i₀ : Fin n)
    (z : (fuksRelativeComplex (ZMod p) (d := D) (n := n)
      (show D-1 ≤ D by omega)).homology q) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod p) (d := D)
      (permutationOrientationMod p n) (show D-1 ≤ D by omega)) q z =
      (∑ σ : Equiv.Perm (Fin n), coherentMinimalRelativeCoefficient (ZMod p) hd i₀ σ
        (eqToHom (congrArg (fun k => (fuksRelativeComplex (ZMod p) (d := D) (n := n)
          (show D-1 ≤ D by omega)).homology k) hq) z) *
            (permutationOrientationMod p n σ : ZMod p)) •
      eqToHom (congrArg (fun k => (twistedFuksRelativeComplex (ZMod p) (d := D)
        (permutationOrientationMod p n) (show D-1 ≤ D by omega)).homology k) hq.symm)
        (coherentTwistedMinimalClass (ZMod p) (permutationOrientationMod p n) hd i₀) := by
  subst q
  simpa only [eqToHom_refl, ModuleCat.id_apply] using
    minimalTwistedProjection_eq_character_sum (ZMod p) (permutationOrientationMod p n) hd i₀ z

/-- The genuine projected first boundary is the binomial coefficient times
the common disk amplitude and the actual coherent twisted minimal class. -/
theorem twistedFuksDifferential_sign_projected_basis
    (p : ℕ) {d n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (split : TwoColumnSplit n) (i₀ : Fin n) :
    twistedFuksDifferential (ZMod p) (d := d+1) (permutationOrientationMod p n)
      (Nat.le_succ d) (Nat.le_succ (d+1)) (d+n+1)
      (HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod p) (d := d+1)
        (permutationOrientationMod p n) (Nat.le_succ (d+1))) (d+n+2)
        (twoColumnFuksBasis (ZMod p) d n hn (split,1))) =
      ((n.choose split.val.val : ZMod p) *
        twoColumnDiskIncidenceCoefficient (ZMod p) (d := d) split i₀ 1 1) •
        eqToHom (congrArg (fun k => (twistedFuksRelativeComplex (ZMod p) (d := d+1)
          (permutationOrientationMod p n) (Nat.le_succ d)).homology k)
          (show (d+1)+n = d+n+1 by omega))
            (coherentTwistedMinimalClass (ZMod p) (permutationOrientationMod p n)
              (show 0 < d+1 by omega) i₀) := by
  let χ := permutationOrientationMod p n
  let x := twoColumnFuksBasis (ZMod p) d n hn (split,1)
  let z := fuksDifferential (ZMod p) (d := d+1) (n := n) (Nat.le_succ d)
    (Nat.le_succ (d+1)) (d+n+1) x
  let g := eqToHom (congrArg (fun k => (twistedFuksRelativeComplex (ZMod p) (d := d+1) χ
    (Nat.le_succ d)).homology k) (show (d+1)+n = d+n+1 by omega))
      (coherentTwistedMinimalClass (ZMod p) χ (show 0 < d+1 by omega) i₀)
  have h₁ := congrArg (fun f : (fuksRelativeComplex (ZMod p) (d := d+1) (n := n)
    (Nat.le_succ (d+1))).homology (d+n+2) ⟶ (twistedFuksRelativeComplex (ZMod p)
      (d := d+1) χ (Nat.le_succ d)).homology (d+n+1) => f x)
        (fuksDifferential_projection (ZMod p) (d := d+1) χ (Nat.le_succ d)
          (Nat.le_succ (d+1)) (d+n+1)).symm
  have h₂ := minimalProjection_sign_at_degree p (D := d+1) (n := n) (q := d+n+1)
    (by omega) (by omega) i₀ z
  have h₃ := congrArg (fun r : ZMod p => r • g)
    (sum_twoColumnMinimalRelativeCoefficient_fuksDifferential_sign p (d := d) hn split i₀)
  exact h₁.trans (h₂.trans h₃)

theorem twistedFuksDifferential_projected_basis_primePower
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hn : 2 ≤ n) (hpow : n = p^a)
    (split : TwoColumnSplit n) :
    twistedFuksDifferential (ZMod p) (d := d+1) (permutationOrientationMod p n)
      (Nat.le_succ d) (Nat.le_succ (d+1)) (d+n+1)
      (HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod p) (d := d+1)
        (permutationOrientationMod p n) (Nat.le_succ (d+1))) (d+n+2)
        (twoColumnFuksBasis (ZMod p) d n hn (split,1))) = 0 := by
  rw [twistedFuksDifferential_sign_projected_basis p hn split 0,
    primePower_choose_split_mod_zero hp hpow split, zero_mul, zero_smul]

private theorem homologyMap_primePower_smul
    (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (r : R) (q : ℕ) :
    HomologicalComplex.homologyMap (r • f) q = r • HomologicalComplex.homologyMap f q := by
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map
      (r • f) = r • (HomologicalComplex.shortComplexFunctor (ModuleCat R)
        (ComplexShape.down ℕ) q).map f by rfl,
    ShortComplex.homologyMap_smul]

/-- The ordinary two-column basis transforms by the character after actual
projection, over any commutative ring. -/
theorem twoColumnFuksBasis_projection_relabel
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hn : 2 ≤ n) (split : TwoColumnSplit n)
    (σ : Equiv.Perm (Fin n)) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj R (d := d+1) χ
      (Nat.le_succ (d+1))) (d+n+2) (twoColumnFuksBasis R d n hn (split,σ)) =
      (χ σ : R) • HomologicalComplex.homologyMap (twistedFuksRelativeProj R (d := d+1) χ
        (Nat.le_succ (d+1))) (d+n+2) (twoColumnFuksBasis R d n hn (split,1)) := by
  let x := twoColumnFuksBasis R d n hn (split,1)
  let π := twistedFuksRelativeProj R (d := d+1) χ (Nat.le_succ (d+1))
  let ρ := fuksRelativeRelabel R (d := d+1) (Nat.le_succ (d+1)) σ
  have hr : HomologicalComplex.homologyMap ρ (d+n+2) x =
      twoColumnFuksBasis R d n hn (split,σ) := by
    simpa only [mul_one] using twoColumnFuksBasis_relabel R (d := d) hn (split,1) σ
  rw [← hr]
  change (HomologicalComplex.homologyMap ρ (d+n+2) ≫
    HomologicalComplex.homologyMap π (d+n+2)) x = _
  rw [← HomologicalComplex.homologyMap_comp]
  have h : ρ ≫ π = (χ σ : R) • π := fuksRelativeRelabel_proj R χ _ σ
  rw [h, homologyMap_primePower_smul]
  rfl

/-- The projected genuine first differential vanishes on every ordinary
source class, including all relabelled two-column disks. -/
@[reassoc]
theorem projection_comp_twistedFuksDifferential_primePower
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hn : 2 ≤ n) (hpow : n = p^a) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod p) (d := d+1)
      (permutationOrientationMod p n) (Nat.le_succ (d+1))) (d+n+2) ≫
      twistedFuksDifferential (ZMod p) (d := d+1) (permutationOrientationMod p n)
        (Nat.le_succ d) (Nat.le_succ (d+1)) (d+n+1) = 0 := by
  apply ModuleCat.hom_ext
  apply (twoColumnFuksBasis (ZMod p) d n hn).ext
  intro ⟨split,σ⟩
  change twistedFuksDifferential (ZMod p) (d := d+1) (permutationOrientationMod p n)
    (Nat.le_succ d) (Nat.le_succ (d+1)) (d+n+1)
    (HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod p) (d := d+1)
      (permutationOrientationMod p n) (Nat.le_succ (d+1))) (d+n+2)
      (twoColumnFuksBasis (ZMod p) d n hn (split,σ))) = 0
  rw [twoColumnFuksBasis_projection_relabel, map_smul,
    twistedFuksDifferential_projected_basis_primePower hp hn hpow split, smul_zero]

/-- Surjectivity in the first cell degree upgrades projected vanishing to
vanishing on every class of the genuine twisted source. -/
theorem twistedFuksDifferential_primePower {p d n a : ℕ} [NeZero n]
    (hp : p.Prime) (hn : 2 ≤ n) (hpow : n = p^a) :
    twistedFuksDifferential (ZMod p) (d := d+1) (permutationOrientationMod p n)
      (Nat.le_succ d) (Nat.le_succ (d+1)) (d+n+1) = 0 := by
  let π := HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod p) (d := d+1)
    (permutationOrientationMod p n) (Nat.le_succ (d+1))) (d+n+2)
  letI : Epi π := epi_twistedFuksRelativeProj_through_cell_degree (ZMod p)
    (d := d+1) (permutationOrientationMod p n) hn (show d+n+2 ≤ d+1+1+n by omega)
  apply (cancel_epi π).mp
  simpa only [comp_zero] using
    (projection_comp_twistedFuksDifferential_primePower hp hn hpow)

/-- At every prime-power size, the genuine nonzero lowest sign-twisted
class persists to the entire compactified configuration space. -/
theorem twistedMinimalClass_primePower_survives {p d n a : ℕ} [NeZero n]
    (hp : p.Prime) (hn : 2 ≤ n) (hpow : n = p^a) (i₀ : Fin n) :
    HomologicalComplex.homologyMap (twistedFuksRelativeMap (ZMod p) (d := d+1)
      (permutationOrientationMod p n) (Nat.le_succ d)
      (show d ≤ (d+1)*n by nlinarith) (le_refl d)
      (show d+1 ≤ (d+1)*n by nlinarith)) ((d+1)+n)
        (coherentTwistedMinimalClass (ZMod p) (permutationOrientationMod p n)
          (show 0 < d+1 by omega) i₀) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let χ := permutationOrientationMod p n
  let f := HomologicalComplex.homologyMap (twistedFuksRelativeMap (ZMod p) (d := d+1) χ
    (Nat.le_succ d) (show d ≤ (d+1)*n by nlinarith) (le_refl d)
    (show d+1 ≤ (d+1)*n by nlinarith)) ((d+1)+n)
  have hfirst : twistedFuksDifferential (ZMod p) (d := d+1) χ (Nat.le_succ d)
      (Nat.le_succ (d+1)) ((d+1)+n) = 0 := by
    rw [show (d+1)+n = d+n+1 by omega]
    exact twistedFuksDifferential_primePower hp hn hpow
  have hm : Mono f := mono_twistedFuksMinimal_to_level_of_first_zero (ZMod p)
    (d := d+1) χ hn rfl (show d+1 ≤ (d+1)*n by nlinarith) hfirst
  intro hz
  exact coherentTwistedMinimalClass_ne_zero (ZMod p) χ (show 0 < d+1 by omega) i₀
    ((ModuleCat.mono_iff_injective f).mp hm (hz.trans (map_zero f.hom).symm))

/-- Unconditional nonvanishing in the full configuration BM source over
every prime field, including odd primes. No incidence, orientation,
projection, or persistence hypothesis is left to discharge. -/
theorem bm_twistedMinimalClass_primePower_ne_zero {p d n a : ℕ} [NeZero n]
    (hp : p.Prime) (hn : 2 ≤ n) (hpow : n = p^a) (i₀ : Fin n) :
    HomologicalComplex.homologyMap
      (topFuksBMTwistedChainIso (ZMod p) d n (permutationOrientationMod p n) hn).hom
      ((d+1)+n)
      (HomologicalComplex.homologyMap (twistedFuksRelativeMap (ZMod p) (d := d+1)
        (permutationOrientationMod p n) (Nat.le_succ d)
        (show d ≤ (d+1)*n by nlinarith) (le_refl d)
        (show d+1 ≤ (d+1)*n by nlinarith)) ((d+1)+n)
          (coherentTwistedMinimalClass (ZMod p) (permutationOrientationMod p n)
            (show 0 < d+1 by omega) i₀)) ≠ 0 := by
  let e := topFuksBMTwistedChainIso (ZMod p) d n (permutationOrientationMod p n) hn
  let f := HomologicalComplex.homologyMap e.hom ((d+1)+n)
  intro hz
  apply twistedMinimalClass_primePower_survives hp hn hpow i₀
  exact (ModuleCat.mono_iff_injective f).mp inferInstance (hz.trans (map_zero f.hom).symm)

end NRR.PrimePowerTopology

