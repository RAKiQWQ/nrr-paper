import NRR.PrimePowerTopologyFilteredChains

/-! The canonical lower-level inclusion viewed as a closed subset of the
upper level, with the resulting identification of singular relative homology. -/

noncomputable section
open Set Topology CategoryTheory
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

instance compactSpace_compactifiedFuksLevel (d n k : ℕ) :
    CompactSpace (compactifiedFuksLevel d n k) :=
  isCompact_iff_compactSpace.mp (isClosed_compactifiedFuksLevel d n k).isCompact

def fuksLowerSubsetHomeomorph {d n a b : ℕ} (hab : a ≤ b) :
    compactifiedFuksLevel d n a ≃ₜ
      (Subtype.val ⁻¹' compactifiedFuksLevel d n a : Set (compactifiedFuksLevel d n b)) where
  toFun x := ⟨⟨x.val, compactifiedFuksLevel_mono d n hab x.property⟩, x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def fuksSubsetPairIso (R : Type) [CommRing R] {d n a b : ℕ} (hab : a ≤ b) (q : ℕ) :
    (fuksRelativeComplex R (d := d) (n := n) hab).homology q ≅ Hrel R q
      (subIncl (Y := TopCat.of (compactifiedFuksLevel d n b)) (Subtype.val ⁻¹' compactifiedFuksLevel d n a)) := by
  let X := TopCat.of (compactifiedFuksLevel d n b)
  let L : Set X := Subtype.val ⁻¹' compactifiedFuksLevel d n a
  let i := compactifiedFuksInclusion (d := d) (n := n) hab
  let j := subIncl (Y := X) L
  let e := TopCat.isoOfHomeo (X := TopCat.of (compactifiedFuksLevel d n a))
    (Y := TopCat.of L) (fuksLowerSubsetHomeomorph hab)
  have w : i ≫ 𝟙 X = e.hom ≫ j := by ext; rfl
  letI := isIso_HrelMap_of_isIso R q i j w
  exact asIso (HrelMap R q i j w)

end NRR.PrimePowerTopology
