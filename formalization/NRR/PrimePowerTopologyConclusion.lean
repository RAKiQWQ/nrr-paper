import NRR.PrimePowerTopologyStaircaseEulerSource
import NRR.PrimePowerTopologyEulerThomPrimePower
import NRR.PrimePowerExistencePowerConclusion
import NRR.PrescribedCounterexamples

/-! The unconditional prime-power obstruction and the full classification. -/

noncomputable section
open Set Topology CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- Every equivariant map from the actual configuration space to the
reduced permutation representation has a zero at prime-power size. -/
theorem configuration_equivariant_has_zero_primePower
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hd : 0 < d)
    (hn : 2 ≤ n) (hpow : n = p^a)
    (f : C(Configuration (d+1) n,ReducedValues (d+1) n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) : ∃ x, f x = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let χ := associatedAmbientOrientationMod p (d+1) n
  have hex : ∃ c : (associatedBMTwistedSource (ZMod p) (d := d+1) χ).homology ((d+1)*n),
      HomologicalComplex.homologyMap (verticalNormalTwistedCollapse (ZMod p) (d := d) χ)
        ((d+1)*n) c ≠ 0 := by
    have h : ∃ c : (associatedBMTwistedSource (ZMod p) (d := d+1) χ).homology (n*(d+1)),
        HomologicalComplex.homologyMap (verticalNormalTwistedCollapse (ZMod p) (d := d) χ)
          (n*(d+1)) c ≠ 0 :=
      ⟨configurationGenuineTwistedFundamentalClass p (d+1) n (Nat.succ_pos d),
        configurationGenuineTwistedFundamentalClass_normal_ne_zero p⟩
    rwa [Nat.mul_comm n (d+1)] at h
  obtain ⟨c,hc⟩ := hex
  exact equivariant_has_zero_of_associatedBMTwistedEulerMap_ne_zero (ZMod p) χ ((d+1)*n)
    (associatedBMTwistedEulerMap_primePower_ne_zero_of_collapse hp hd hn hpow c hc) f he

/-- The configuration zero theorem has no topological or geometric
hypotheses beyond the dimension and prime-power assumptions. -/
theorem configuration_equivariant_has_zero
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (hpow : IsPrimePow n)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) : ∃ x, f x = 0 := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨p,a,hp,_ha,hpa⟩ := (isPrimePow_nat_iff n).mp hpow
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  exact configuration_equivariant_has_zero_primePower hp (by omega) hn hpa.symm f he

end NRR.PrimePowerTopology

namespace NRR

/-- The prime-power existence direction for every prescribed convex body
and every absolutely continuous probability measure in the manuscript. -/
theorem primePowerExistence : PrimePowerExistence :=
  primePowerExistence_of_configuration_zero fun d n hd hn hp f he =>
    PrimePowerTopology.configuration_equivariant_has_zero d n (by omega) hn hp f he

/-- The full pointwise classification in the original quantifier order. -/
theorem fullClassification : FullClassification :=
  classification_iff.mpr ⟨primePowerExistence,prescribedCounterexamples⟩

end NRR
