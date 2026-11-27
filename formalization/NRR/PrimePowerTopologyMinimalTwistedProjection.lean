import NRR.PrimePowerTopologyMinimalTwistedHomology
import NRR.PrimePowerTopologyMinimalGeneration
import NRR.PrimePowerTopologyTwistedBoundaryTransfer

/-! Coordinates of the actual ordinary-to-twisted projection in the lowest
Fuks group. Only the action on honest geometric cell generators is used. -/

noncomputable section
open CategoryTheory
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]

private theorem generator_apply (M : ModuleCat R) (g : ModuleCat.of R R ⟶ M) (r : R) :
    g r = r • g (1 : R) := by
  simpa only [smul_eq_mul, mul_one] using g.hom.map_smul r (1 : R)

/-- The coherent orientation gauges cancel between a cell coefficient and
the corresponding generator, so these classes expand every relative class. -/
theorem coherentMinimalRelativeClass_sum_coeff (hd : 0 < d) (i₀ : Fin n)
    (z : (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n)) :
    ∑ σ : Equiv.Perm (Fin n), coherentMinimalRelativeCoefficient R hd i₀ σ z •
      coherentMinimalRelativeClass R hd i₀ σ = z := by
  let e := minimalActualRelativeComparisonIso R d n hd
  let x := e.inv z
  have hpos : 0 < d+n := by omega
  have hσ (σ : Equiv.Perm (Fin n)) :
      coherentMinimalRelativeCoefficient R hd i₀ σ z • coherentMinimalRelativeClass R hd i₀ σ =
        e.hom (minimalCellCoefficient R i₀ σ hpos x •
          minimalFundamentalClass R i₀ σ hpos) := by
    have hg :
        coherentMinimalCoefficient R i₀ σ hpos ≫ coherentMinimalGenerator R i₀ σ hpos =
          minimalCellCoefficient R i₀ σ hpos ≫ minimalCellGenerator R i₀ σ hpos := by
      rw [coherentMinimalCoefficient_eq_old, coherentMinimalGenerator_eq_old]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change coherentMinimalCoefficient R i₀ σ hpos x •
      e.hom (coherentMinimalGenerator R i₀ σ hpos 1) = _
    rw [← map_smul, ← generator_apply R _ (coherentMinimalGenerator R i₀ σ hpos),
      minimalFundamentalClass, ← generator_apply R _ (minimalCellGenerator R i₀ σ hpos)]
    exact congrArg e.hom (congrArg
      (fun f : Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ⟶
        Habs R (d+n) (TopCat.of (minimalSkeleton d n)) => f x) hg)
  simp_rw [hσ]
  rw [← map_sum, minimalFundamentalClass_sum_coeff]
  exact e.toLinearEquiv.apply_symm_apply z

/-- On an arbitrary ordinary class, projection into the genuine twisted
complex multiplies the twisted generator by the character-weighted sum of
its coherent cell coordinates. -/
theorem minimalTwistedProjection_eq_character_sum (χ : Equiv.Perm (Fin n) →* Rˣ)
    (hd : 0 < d) (i₀ : Fin n)
    (z : (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n)) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj R (d := d) χ
      (show d-1 ≤ d by omega)) (d+n) z =
      (∑ σ : Equiv.Perm (Fin n), coherentMinimalRelativeCoefficient R hd i₀ σ z * (χ σ : R)) •
        coherentTwistedMinimalClass R χ hd i₀ := by
  conv_lhs => rw [← coherentMinimalRelativeClass_sum_coeff R hd i₀ z]
  simp only [map_sum, map_smul, coherentMinimalRelativeClass_twistedImage, smul_smul, Finset.sum_smul]

/-- The kernel on ordinary lowest classes is detected by one scalar even in
prime characteristic, because the twisted generator map is split injective. -/
theorem minimalTwistedProjection_eq_zero_iff (χ : Equiv.Perm (Fin n) →* Rˣ)
    (hd : 0 < d) (i₀ : Fin n)
    (z : (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n)) :
    HomologicalComplex.homologyMap (twistedFuksRelativeProj R (d := d) χ
      (show d-1 ≤ d by omega)) (d+n) z = 0 ↔
      (∑ σ : Equiv.Perm (Fin n), coherentMinimalRelativeCoefficient R hd i₀ σ z * (χ σ : R)) = 0 := by
  rw [minimalTwistedProjection_eq_character_sum R χ hd i₀ z]
  constructor
  · intro h
    have hh := congrArg (coherentTwistedMinimalCoefficient R χ hd i₀) h
    rw [map_smul, coherentTwistedMinimalClass_coefficient R χ hd i₀, map_zero] at hh
    simpa only [smul_eq_mul, mul_one] using hh
  · intro h
    rw [h, zero_smul]

/-- Projection from the ordered chains to the twisted chains commutes with the
actual three-level boundary, even when the group order vanishes in the ring. -/
@[reassoc]
theorem fuksDifferential_projection (χ : Equiv.Perm (Fin n) →* Rˣ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    fuksDifferential R (d := d) (n := n) hab hbc q ≫
        HomologicalComplex.homologyMap (twistedFuksRelativeProj R χ hab) q =
      HomologicalComplex.homologyMap (twistedFuksRelativeProj R χ hbc) (q+1) ≫
        twistedFuksDifferential R (d := d) χ hab hbc q := by
  let f : fuksTriple R (d := d) (n := n) hab hbc ⟶ twistedFuksTriple R χ hab hbc :=
    { τ₁ := twistedFuksRelativeProj R χ hab
      τ₂ := twistedFuksRelativeProj R χ (hab.trans hbc)
      τ₃ := twistedFuksRelativeProj R χ hbc
      comm₁₂ := twistedFuksRelativeProj_map R χ hab (hab.trans hbc) (le_refl a) hbc
      comm₂₃ := twistedFuksRelativeProj_map R χ (hab.trans hbc) hbc hab (le_refl c) }
  rw [fuksDifferential_eq_tripleδ, twistedFuksDifferential_eq_tripleδ]
  exact HomologicalComplex.HomologySequence.δ_naturality f
    (fuksTriple_shortExact R hab hbc) (twistedFuksTriple_shortExact R χ hab hbc)
    (q+1) q rfl

end NRR.PrimePowerTopology
