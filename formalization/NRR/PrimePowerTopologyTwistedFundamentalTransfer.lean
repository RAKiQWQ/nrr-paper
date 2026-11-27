import NRR.PrimePowerTopologyChainTransfer
import NRR.PrimePowerTopologyRelativePairOrbitBasis

/-! The signed transfer on a complex with a regular orbit basis is split
injective in each chain degree, over every commutative coefficient ring.
The splitting selects the coefficient at the identity in each actual free
orbit. No group-order scalar is inverted. -/

noncomputable section
open CategoryTheory Limits Classical

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {G : Type} [Group G] [Fintype G]
  (χ : G →* Rˣ) (K : ChainComplex (ModuleCat R) ℕ) (ρ : G → (K ⟶ K))
  (law : ∀ g h, ρ (g*h) = ρ h ≫ ρ g)
  {I : ℕ → Type} (b : ∀ q, Module.Basis (G × I q) R (K.X q))
  (hb : ∀ q g h a, (ρ g).f q (b q (h,a)) = b q (g*h,a))

/-- Select the identity-labelled representative in each actual free chain
orbit and project that representative to the twisted quotient. -/
def twistedFundamentalTransferRetract (q : ℕ) :
    K.X q ⟶ (twistedChainComplex R χ K ρ).X q :=
  ModuleCat.ofHom ((b q).constr R fun p =>
    if p.1 = 1 then (twistedChainProj R χ K ρ).f q (b q p) else 0)

@[simp] theorem twistedFundamentalTransferRetract_basis (q : ℕ) (g : G) (a : I q) :
    twistedFundamentalTransferRetract R χ K ρ b q (b q (g,a)) =
      if g = 1 then (twistedChainProj R χ K ρ).f q (b q (g,a)) else 0 :=
  (b q).constr_basis R _ _

include hb

theorem twistedFundamentalProjection_basis (q : ℕ) (g : G) (a : I q) :
    (twistedChainProj R χ K ρ).f q (b q (g,a)) =
      (χ g : R) • (twistedChainProj R χ K ρ).f q (b q (1,a)) := by
  have h := congrArg (fun f : K ⟶ twistedChainComplex R χ K ρ =>
      f.f q (b q (1,a))) (chainAction_proj R χ K ρ g)
  change (twistedChainProj R χ K ρ).f q ((ρ g).f q (b q (1,a))) = _ at h
  change (twistedChainProj R χ K ρ).f q ((ρ g).f q (b q (1,a))) =
    (χ g : R) • (twistedChainProj R χ K ρ).f q (b q (1,a)) at h
  simpa only [hb, mul_one] using h

/-- Transfer followed by representative selection is the identity on the
actual character-coinvariant chain module. -/
theorem twistedFundamentalTransfer_retract (q : ℕ) :
    (twistedChainTransferDesc R χ K ρ law).f q ≫
      twistedFundamentalTransferRetract R χ K ρ b q = 𝟙 _ := by
  let π := twistedChainProj R χ K ρ
  have hπ : Epi (π.f q) :=
    inferInstanceAs (Epi ((cokernel.π (chainActionRelations R χ K ρ)).f q))
  apply hπ.left_cancellation
  have hn : π.f q ≫ (twistedChainTransferDesc R χ K ρ law).f q =
      (twistedChainTransfer R χ K ρ).f q :=
    congrArg (fun f : K ⟶ K => f.f q) (twistedChainProj_transferDesc R χ K ρ law)
  rw [← Category.assoc, hn, Category.comp_id]
  apply ModuleCat.hom_ext
  apply (b q).ext
  rintro ⟨h,a⟩
  change twistedFundamentalTransferRetract R χ K ρ b q
    ((twistedChainTransfer R χ K ρ).f q (b q (h,a))) = π.f q (b q (h,a))
  have ht : (twistedChainTransfer R χ K ρ).f q (b q (h,a)) =
      ∑ g : G, ((χ g)⁻¹ : Rˣ).val • b q (g*h,a) := by
    unfold twistedChainTransfer
    have hs := map_sum (HomologicalComplex.Hom.fAddMonoidHom (C₁ := K) (C₂ := K) q)
      (fun g : G => ((χ g)⁻¹ : Rˣ).val • ρ g) Finset.univ
    change (∑ g : G, ((χ g)⁻¹ : Rˣ).val • ρ g).f q = _ at hs
    rw [hs]
    change (∑ g : G, ((χ g)⁻¹ : Rˣ).val • (ρ g).f q) (b q (h,a)) = _
    simp [hb]
  rw [ht, map_sum]
  simp only [map_smul, twistedFundamentalTransferRetract_basis]
  rw [Finset.sum_eq_single h⁻¹]
  · simp only [inv_mul_cancel, if_pos rfl, map_inv, inv_inv]
    exact (twistedFundamentalProjection_basis R χ K ρ b hb q h a).symm
  · intro g hg hgh
    have hne : g*h ≠ 1 := by
      intro he
      exact hgh (mul_eq_one_iff_eq_inv.mp he)
    simp only [if_neg hne, smul_zero]
  · simp

/-- The genuine signed transfer is injective on each chain module of a
complex free on label orbits. This holds also in the modular case. -/
theorem twistedFundamentalTransfer_injective (q : ℕ) :
    Function.Injective ((twistedChainTransferDesc R χ K ρ law).f q) := by
  intro x y hxy
  have h := congrArg (twistedFundamentalTransferRetract R χ K ρ b q) hxy
  have he := twistedFundamentalTransfer_retract R χ K ρ law b hb q
  have hx := congrArg (fun f => f x) he
  have hy := congrArg (fun f => f y) he
  exact hx.symm.trans (h.trans hy)

/-- Any chain whose signed transfer is an ordinary cycle is itself a
twisted cycle. The conclusion is verified by transfer in the boundary
degree, rather than by dividing by the order of the label group. -/
theorem twistedFundamentalCycle_of_transfer (q : ℕ)
    (z : (twistedChainComplex R χ K ρ).X q)
    (hz : K.d q (q-1) ((twistedChainTransferDesc R χ K ρ law).f q z) = 0) :
    (twistedChainComplex R χ K ρ).d q (q-1) z = 0 := by
  apply twistedFundamentalTransfer_injective R χ K ρ law b hb (q-1)
  rw [map_zero]
  have hc := congrArg (fun f => f z)
    ((twistedChainTransferDesc R χ K ρ law).comm q (q-1))
  exact hc.symm.trans hz

end NRR.PrimePowerTopology
