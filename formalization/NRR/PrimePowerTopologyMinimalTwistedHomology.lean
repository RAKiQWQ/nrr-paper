import NRR.PrimePowerTopologyMinimalEquivariance
import NRR.PrimePowerTopologyChainTransfer

/-! A genuine chain-transfer detector for the actual twisted lowest Fuks
class. The transfer sum is not divided by the symmetric-group order.
Its identity-cell coefficient detects exactly one summand, so the argument
is valid even when the coefficient characteristic divides the group order. -/

noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

theorem compactifiedFuksRelabelMap_mul {d n k : ℕ} [NeZero n]
    (σ τ : Equiv.Perm (Fin n)) :
    compactifiedFuksRelabelMap (d := d) (k := k) (σ*τ) =
      compactifiedFuksRelabelMap τ ≫ compactifiedFuksRelabelMap σ := by
  ext x
  exact compactifiedConfigurationRelabel_mul_apply σ τ x.val

/-- The actual relative chain actions satisfy the same left action law
as the underlying compactified configurations. -/
theorem fuksRelativeRelabel_mul {d n k l : ℕ} [NeZero n]
    (hkl : k ≤ l) (σ τ : Equiv.Perm (Fin n)) :
    fuksRelativeRelabel R (d := d) hkl (σ*τ) =
      fuksRelativeRelabel R hkl τ ≫ fuksRelativeRelabel R hkl σ := by
  symm
  unfold fuksRelativeRelabel
  rw [relComplexMap_comp]
  congr 1
  · exact (compactifiedFuksRelabelMap_mul σ τ).symm
  · exact (compactifiedFuksRelabelMap_mul σ τ).symm

private theorem homologyMap_smul_moduleChains
    {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (r : R) (q : ℕ) :
    HomologicalComplex.homologyMap (r • f) q = r • HomologicalComplex.homologyMap f q := by
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map
      (r • f) = r • (HomologicalComplex.shortComplexFunctor (ModuleCat R)
        (ComplexShape.down ℕ) q).map f by rfl,
    ShortComplex.homologyMap_smul]

/-- The genuine chain transfer induces the expected finite signed sum
on actual homology; this statement inverts no group-order scalar. -/
theorem homologyMap_twistedChainTransfer {G : Type} [Group G] [Fintype G]
    (χ : G →* Rˣ) (K : ChainComplex (ModuleCat R) ℕ)
    (ρ : G → (K ⟶ K)) (q : ℕ) :
    HomologicalComplex.homologyMap (twistedChainTransfer R χ K ρ) q =
      ∑ g : G, ((χ g)⁻¹ : Rˣ).val • HomologicalComplex.homologyMap (ρ g) q := by
  classical
  unfold twistedChainTransfer
  change (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map _ = _
  rw [Functor.map_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact homologyMap_smul_moduleChains R (ρ g) _ q

/-- A map from the actual twisted lowest relative chain complex back to
the actual untwisted pair, supplied by the proved chain transfer. -/
def minimalTwistedTransfer {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) :
    twistedFuksRelativeComplex R (d := d) χ (show d-1 ≤ d by omega) ⟶
      fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega) :=
  twistedChainTransferDesc R χ
    (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega))
    (fuksRelativeRelabel R (show d-1 ≤ d by omega))
    (fuksRelativeRelabel_mul R (show d-1 ≤ d by omega))

/-- An actual homology functional on the twisted chain complex. It is
transfer followed by the coherent identity-cell coefficient. -/
def coherentTwistedMinimalCoefficient {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    (twistedFuksRelativeComplex R (d := d) χ (show d-1 ≤ d by omega)).homology (d+n) ⟶
      ModuleCat.of R R :=
  HomologicalComplex.homologyMap (minimalTwistedTransfer R (d := d) χ) (d+n) ≫
    coherentMinimalRelativeCoefficient R hd i₀ 1

theorem coherentTwistedMinimalClass_coefficient {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    coherentTwistedMinimalCoefficient R χ hd i₀
      (coherentTwistedMinimalClass R χ hd i₀) = 1 := by
  classical
  let K := fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)
  let ρ := fuksRelativeRelabel R (d := d) (n := n) (show d-1 ≤ d by omega)
  let z := coherentMinimalRelativeClass R hd i₀ (1 : Equiv.Perm (Fin n))
  have evaluation (g : Equiv.Perm (Fin n)) :
      coherentMinimalRelativeCoefficient R hd i₀ 1
        ((HomologicalComplex.homologyMap (ρ g) (d+n)).hom z) =
        if g = 1 then 1 else 0 := by
    change coherentMinimalRelativeCoefficient R hd i₀ 1
      (HomologicalComplex.homologyMap
        (fuksRelativeRelabel R (d := d) (n := n) (show d-1 ≤ d by omega) g) (d+n)
        (coherentMinimalRelativeClass R hd i₀ 1)) = _
    rw [coherentMinimalRelativeClass_relabel, mul_one]
    exact coherentMinimalRelativeClass_coefficient R hd i₀ g 1
  have projection : coherentTwistedMinimalClass R χ hd i₀ =
      HomologicalComplex.homologyMap (twistedFuksRelativeProj R χ (show d-1 ≤ d by omega))
        (d+n) z := rfl
  unfold coherentTwistedMinimalCoefficient
  rw [projection]
  change coherentMinimalRelativeCoefficient R hd i₀ 1
    ((HomologicalComplex.homologyMap
        (twistedFuksRelativeProj R χ (show d-1 ≤ d by omega)) (d+n) ≫
      HomologicalComplex.homologyMap (minimalTwistedTransfer R (d := d) χ) (d+n)) z) = 1
  rw [← HomologicalComplex.homologyMap_comp]
  change coherentMinimalRelativeCoefficient R hd i₀ 1
    (HomologicalComplex.homologyMap
      (twistedChainProj R χ K ρ ≫ twistedChainTransferDesc R χ K ρ
        (fuksRelativeRelabel_mul R (show d-1 ≤ d by omega))) (d+n) z) = 1
  rw [twistedChainProj_transferDesc, homologyMap_twistedChainTransfer]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  calc
    _ = ∑ g : Equiv.Perm (Fin n), ((χ g)⁻¹ : Rˣ).val *
        (if g = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [evaluation]
    _ = 1 := by simp

/-- The true twisted class map admits a retraction over every commutative
ring. Only the identity cell survives the signed transfer coefficient. -/
@[reassoc (attr := simp)]
theorem coherentTwistedMinimalMap_coefficient {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    coherentTwistedMinimalMap R χ hd i₀ ≫ coherentTwistedMinimalCoefficient R χ hd i₀ =
      𝟙 (ModuleCat.of R R) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change coherentTwistedMinimalCoefficient R χ hd i₀
    (coherentTwistedMinimalClass R χ hd i₀) = 1
  exact coherentTwistedMinimalClass_coefficient R χ hd i₀

/-- A specified splitting of the actual twisted fundamental-class map.
This asserts a copy of R in homology, not a generation theorem for it. -/
def coherentTwistedMinimalSplitMono {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    SplitMono (coherentTwistedMinimalMap R χ hd i₀) where
  retraction := coherentTwistedMinimalCoefficient R χ hd i₀
  id := coherentTwistedMinimalMap_coefficient R χ hd i₀

theorem isSplitMono_coherentTwistedMinimalMap {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    IsSplitMono (coherentTwistedMinimalMap R χ hd i₀) :=
  IsSplitMono.mk' (coherentTwistedMinimalSplitMono R χ hd i₀)

theorem coherentTwistedMinimalMap_injective {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    Function.Injective (coherentTwistedMinimalMap R χ hd i₀) := by
  have hleft : Function.LeftInverse (coherentTwistedMinimalCoefficient R χ hd i₀)
      (coherentTwistedMinimalMap R χ hd i₀) := by
    intro r
    exact congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f r)
      (coherentTwistedMinimalMap_coefficient R χ hd i₀)
  exact hleft.injective

/-- The detector evaluates the actual projection of every coherently
oriented cell by its character value. -/
theorem coherentMinimalRelativeClass_twistedCoefficient {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) :
    coherentTwistedMinimalCoefficient R χ hd i₀
      (HomologicalComplex.homologyMap
        (twistedFuksRelativeProj R (d := d) χ (show d-1 ≤ d by omega)) (d+n)
        (coherentMinimalRelativeClass R hd i₀ σ)) = (χ σ : R) := by
  rw [coherentMinimalRelativeClass_twistedImage, map_smul,
    coherentTwistedMinimalClass_coefficient]
  simp only [smul_eq_mul, mul_one]

/-- The actual twisted lowest relative class is nonzero over every
nontrivial commutative coefficient ring, including every prime field. -/
theorem coherentTwistedMinimalClass_ne_zero [Nontrivial R]
    {d n : ℕ} [NeZero n] (χ : Equiv.Perm (Fin n) →* Rˣ)
    (hd : 0 < d) (i₀ : Fin n) :
    coherentTwistedMinimalClass R χ hd i₀ ≠ 0 := by
  intro hz
  have h := coherentTwistedMinimalClass_coefficient R χ hd i₀
  rw [hz, map_zero] at h
  exact zero_ne_one h

end NRR.PrimePowerTopology
