import NRR.PrimePowerTopologyFilteredChains

/-! Genuine orientation-twisted transfer on singular chain complexes.
It descends through the actual coinvariant cokernel. No division by the
group order and no claim of injectivity of transfer is used. -/

noncomputable section
open CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {G : Type} [Group G] [Fintype G]
  (χ : G →* Rˣ) (K : ChainComplex (ModuleCat R) ℕ) (ρ : G → (K ⟶ K))

def twistedChainTransfer : K ⟶ K := ∑ g : G,((χ g)⁻¹ : Rˣ).val • ρ g

theorem action_comp_twistedChainTransfer
    (law : ∀ g h,ρ (g*h) = ρ h ≫ ρ g) (h : G) :
    ρ h ≫ twistedChainTransfer R χ K ρ = (χ h : R) • twistedChainTransfer R χ K ρ := by
  classical
  rw [twistedChainTransfer,Preadditive.comp_sum,Finset.smul_sum]
  calc
    (∑ g : G,ρ h ≫ (((χ g)⁻¹ : Rˣ).val • ρ g)) =
        ∑ g : G,(χ h : R) • (((χ (g*h))⁻¹ : Rˣ).val • ρ (g*h)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Linear.comp_smul,← law,smul_smul]
      congr 1
      rw [map_mul,mul_inv_rev,Units.val_mul]
      rw [← mul_assoc,← Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
    _ = ∑ g : G,(χ h : R) • (((χ g)⁻¹ : Rˣ).val • ρ g) :=
      Equiv.sum_comp (Equiv.mulRight h)
        (fun g : G => (χ h : R) • (((χ g)⁻¹ : Rˣ).val • ρ g))

theorem chainActionRelation_transfer
    (law : ∀ g h,ρ (g*h) = ρ h ≫ ρ g) (g : G) :
    chainActionRelation R χ K ρ g ≫ twistedChainTransfer R χ K ρ = 0 := by
  rw [chainActionRelation,Preadditive.sub_comp,Linear.smul_comp,Category.id_comp,
    action_comp_twistedChainTransfer R χ K ρ law,sub_self]

def twistedChainTransferDesc (law : ∀ g h,ρ (g*h) = ρ h ≫ ρ g) :
    twistedChainComplex R χ K ρ ⟶ K :=
  cokernel.desc (chainActionRelations R χ K ρ) (twistedChainTransfer R χ K ρ) (by
    apply Sigma.hom_ext
    intro g
    simpa only [← Category.assoc,chainActionRelations,Sigma.ι_desc,comp_zero] using
      chainActionRelation_transfer R χ K ρ law g)

@[reassoc (attr := simp)] theorem twistedChainProj_transferDesc
    (law : ∀ g h,ρ (g*h) = ρ h ≫ ρ g) :
    twistedChainProj R χ K ρ ≫ twistedChainTransferDesc R χ K ρ law =
      twistedChainTransfer R χ K ρ :=
  cokernel.π_desc _ _ _

/-- The composite back to coinvariants is multiplication by |G|. This
identity is valid also in characteristic dividing |G| and is not inverted. -/
theorem twistedChainTransfer_proj :
    twistedChainTransfer R χ K ρ ≫ twistedChainProj R χ K ρ =
      Fintype.card G • twistedChainProj R χ K ρ := by
  rw [twistedChainTransfer,Preadditive.sum_comp]
  simp only [Linear.smul_comp,chainAction_proj,smul_smul,← Units.val_mul,
    inv_mul_cancel,Units.val_one,one_smul,Finset.sum_const,Finset.card_univ]

end NRR.PrimePowerTopology
