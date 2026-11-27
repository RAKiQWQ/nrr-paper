import NRR.PrimePowerTopologyStaircaseAmbient
import NRR.PrimePowerTopologyEulerThomTransfer
import NRR.PrimePowerTopologyStaircaseLocalHomology

/-! Detection of the genuine twisted staircase class by the actual normal
collapse, reduced to ordinary staircase nonvanishing. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

theorem verticalNormalCollapse_ambientImage_ne_zero_degree (R : Type) [CommRing R]
    {d n k : ℕ} [NeZero n] (hk : 0 < k)
    (a : Habs R k (TopCat.of (OnePoint (Fin n → Space (d+1))))) (ha : a ≠ 0) :
    HrelMap R k _ _ (verticalNormalCollapse_square (d := d) (n := n))
      (relJ R k (associatedBMSourceIncl (d+1) n)
        (HabsMap R k (TopCat.ofHom (configurationOnePointCollapse (d+1) n)) a)) ≠ 0 := by
  cases k with
  | zero => omega
  | succ q => exact verticalNormalCollapse_ambientImage_ne_zero R q a ha

theorem configurationGenuineTwistedFundamentalClass_normal_ne_zero_of_ordinary
    (p : ℕ) {d n : ℕ} [NeZero n]
    (hc : configurationOrdinaryStaircaseClass p (d+1) n ≠ 0) :
    HomologicalComplex.homologyMap
      (verticalNormalTwistedCollapse (ZMod p) (d := d)
        (associatedAmbientOrientationMod p (d+1) n)) (n*(d+1))
      (configurationGenuineTwistedFundamentalClass p (d+1) n (Nat.succ_pos d)) ≠ 0 := by
  have hpos : 0 < n*(d+1) := Nat.mul_pos (NeZero.pos n) (Nat.succ_pos d)
  obtain ⟨a,ha,he⟩ := configurationOrdinaryStaircaseClass_ambient_image_nonzero p (d+1) n hpos hc
  apply verticalNormalTwistedCollapse_ne_zero_of_transfer (ZMod p) _ _
  rw [configurationGenuineTwistedFundamentalClass_transfer]
  rw [← he]
  exact verticalNormalCollapse_ambientImage_ne_zero_degree (ZMod p) hpos a ha

theorem configurationGenuineTwistedFundamentalClass_normal_ne_zero
    (p : ℕ) [Nontrivial (ZMod p)] {d n : ℕ} [NeZero n] :
    HomologicalComplex.homologyMap
      (verticalNormalTwistedCollapse (ZMod p) (d := d)
        (associatedAmbientOrientationMod p (d+1) n)) (n*(d+1))
      (configurationGenuineTwistedFundamentalClass p (d+1) n (Nat.succ_pos d)) ≠ 0 :=
  configurationGenuineTwistedFundamentalClass_normal_ne_zero_of_ordinary p
    (configurationOrdinaryStaircaseClass_ne_zero p (Nat.succ_pos d))

end NRR.PrimePowerTopology
