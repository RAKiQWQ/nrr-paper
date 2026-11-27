import NRR.PrimePowerTopologyEulerThomTransfer
import NRR.PrimePowerTopologyAssociatedBMTargetNonzero

/-! The actual closed-normal comparison is an isomorphism at every
prime-power cardinality with the genuine ambient orientation twist. -/

noncomputable section
open CategoryTheory
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

theorem isIso_verticalNormalTwistedInclude_primePower {p d n a : ℕ} [NeZero n]
    (hp : p.Prime) (hd : 0 < d) (hn : 2 ≤ n) (hpow : n = p^a) :
    IsIso (HomologicalComplex.homologyMap
      (verticalNormalTwistedInclude (ZMod p) (d := d) (associatedAmbientOrientationMod p (d+1) n))
      ((d+1)*n)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := nontrivial_associatedBMTwistedTarget_primePower hp hd hn hpow
  exact isIso_verticalNormalTwistedInclude_of_nontrivial (ZMod p)
    (associatedAmbientOrientationMod p (d+1) n) hd hn (0 : Fin n)

theorem verticalEulerTargetGenerator_primePower_ne_zero {p d n a : ℕ} [NeZero n]
    (hp : p.Prime) (hd : 0 < d) (hn : 2 ≤ n) (hpow : n = p^a) (i₀ : Fin n) :
    verticalEulerTargetGenerator (ZMod p) (associatedAmbientOrientationMod p (d+1) n) hd hn i₀ ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := nontrivial_associatedBMTwistedTarget_primePower hp hd hn hpow
  exact verticalEulerTargetGenerator_ne_zero (ZMod p) _ hd hn i₀

/-- At prime-power cardinality, the Euler image of an actual source class
is nonzero as soon as its genuine normal collapse is nonzero. The closed
normal comparison is discharged by the proved prime-power target theorem. -/
theorem associatedBMTwistedEulerMap_primePower_apply_ne_zero_of_collapse
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hd : 0 < d) (hn : 2 ≤ n) (hpow : n = p^a)
    (c : (associatedBMTwistedSource (ZMod p) (d := d+1)
      (associatedAmbientOrientationMod p (d+1) n)).homology ((d+1)*n))
    (hc : HomologicalComplex.homologyMap (verticalNormalTwistedCollapse (ZMod p)
      (associatedAmbientOrientationMod p (d+1) n)) ((d+1)*n) c ≠ 0) :
    associatedBMTwistedEulerMap (ZMod p) (associatedAmbientOrientationMod p (d+1) n) ((d+1)*n) c ≠ 0 := by
  let f := HomologicalComplex.homologyMap (verticalNormalTwistedInclude (ZMod p) (d := d)
    (associatedAmbientOrientationMod p (d+1) n)) ((d+1)*n)
  letI : IsIso f := isIso_verticalNormalTwistedInclude_primePower hp hd hn hpow
  rw [associatedBMTwistedEulerMap_eq_pointNormal, ModuleCat.comp_apply]
  intro hz
  apply hc
  exact (ModuleCat.mono_iff_injective f).mp inferInstance (hz.trans (map_zero f.hom).symm)

theorem associatedBMTwistedEulerMap_primePower_ne_zero_of_collapse
    {p d n a : ℕ} [NeZero n] (hp : p.Prime) (hd : 0 < d) (hn : 2 ≤ n) (hpow : n = p^a)
    (c : (associatedBMTwistedSource (ZMod p) (d := d+1)
      (associatedAmbientOrientationMod p (d+1) n)).homology ((d+1)*n))
    (hc : HomologicalComplex.homologyMap (verticalNormalTwistedCollapse (ZMod p)
      (associatedAmbientOrientationMod p (d+1) n)) ((d+1)*n) c ≠ 0) :
    associatedBMTwistedEulerMap (ZMod p) (d := d+1)
      (associatedAmbientOrientationMod p (d+1) n) ((d+1)*n) ≠ 0 := by
  intro hz
  have h := associatedBMTwistedEulerMap_primePower_apply_ne_zero_of_collapse hp hd hn hpow c hc
  exact h (by rw [hz]; rfl)

end NRR.PrimePowerTopology
