import NRR.PrimePowerTopologyPermutationDegree
import NRR.PrimePowerTopologyMinimalEquivariance
import NRR.PrimePowerTopologyCellCollapse

/-! Orientation of the actual open-chamber collapse in common height
coordinates, using the genuine singular-homology permutation action. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

def minimalChamberCoordinateEmbedding {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    C(Space d × heightChamber n σ, Space d × (Fin n → ℝ)) :=
  ⟨fun p => (p.1,p.2.val),continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

theorem isOpenEmbedding_minimalChamberCoordinateEmbedding {d n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    IsOpenEmbedding (minimalChamberCoordinateEmbedding (d := d) σ) :=
  IsOpenEmbedding.id.prodMap (isOpen_heightChamber n σ).isOpenEmbedding_subtypeVal

def minimalChamberOnePointCollapse {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    C(OnePoint (Space d × (Fin n → ℝ)), OnePoint (Space d × heightChamber n σ)) :=
  onePointOpenEmbeddingCollapse (minimalChamberCoordinateEmbedding (d := d) σ)
    (isOpenEmbedding_minimalChamberCoordinateEmbedding (d := d) σ)

@[simp] theorem minimalChamberOnePointCollapse_coe {d n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Space d × heightChamber n σ) :
    minimalChamberOnePointCollapse (d := d) σ
      (((p.1,p.2.val) : Space d × (Fin n → ℝ)) : OnePoint _) =
        (p : OnePoint (Space d × heightChamber n σ)) :=
  onePointOpenEmbeddingCollapse_coe _ _ p

@[simp] theorem minimalChamberOnePointCollapse_infty {d n : ℕ}
    (σ : Equiv.Perm (Fin n)) : minimalChamberOnePointCollapse (d := d) σ ∞ = ∞ :=
  onePointOpenEmbeddingCollapse_infty _ _

theorem minimalChamberOnePointCollapse_outside {d n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : OnePoint (Space d × (Fin n → ℝ)))
    (hx : x ∉ range (fun p : Space d × heightChamber n σ =>
      (((p.1,p.2.val) : Space d × (Fin n → ℝ)) : OnePoint _))) :
    minimalChamberOnePointCollapse (d := d) σ x = ∞ :=
  onePointOpenEmbeddingCollapse_outside _ _ x hx

theorem minimalChamberOnePointCollapse_fiber_coe {d n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : OnePoint (Space d × (Fin n → ℝ)))
    (p : Space d × heightChamber n σ) :
    minimalChamberOnePointCollapse (d := d) σ x =
        (p : OnePoint (Space d × heightChamber n σ)) ↔
      x = (((p.1,p.2.val) : Space d × (Fin n → ℝ)) : OnePoint _) := by
  classical
  constructor
  · intro h
    by_cases hx : x ∈ range (fun p : Space d × heightChamber n σ =>
        (((p.1,p.2.val) : Space d × (Fin n → ℝ)) : OnePoint _))
    · obtain ⟨q,rfl⟩ := hx
      rw [minimalChamberOnePointCollapse_coe] at h
      have he : q = p := Option.some.inj h
      rw [he]
    · rw [minimalChamberOnePointCollapse_outside σ x hx] at h
      exact False.elim (OnePoint.infty_ne_coe p h)
  · rintro rfl
    exact minimalChamberOnePointCollapse_coe σ p

theorem minimalChamberOnePointCollapse_relabel {d n : ℕ}
    (ρ σ : Equiv.Perm (Fin n)) :
    heightPermutationOnePointMap (Space d) ρ ≫
        TopCat.ofHom (minimalChamberOnePointCollapse (d := d) (ρ*σ)) =
      TopCat.ofHom (minimalChamberOnePointCollapse (d := d) σ) ≫
        compactifiedCellRelabelMap (d := d) ρ σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  induction x using OnePoint.rec with
  | infty =>
      change minimalChamberOnePointCollapse (d := d) (ρ*σ) ∞ =
        compactifiedCellRelabel ρ σ (minimalChamberOnePointCollapse (d := d) σ ∞)
      rw [minimalChamberOnePointCollapse_infty, minimalChamberOnePointCollapse_infty]
      rfl
  | coe p =>
      by_cases hp : p.2 ∈ heightChamber n σ
      · let q : Space d × heightChamber n σ := (p.1,⟨p.2,hp⟩)
        change minimalChamberOnePointCollapse (d := d) (ρ*σ)
          (((q.1,(heightChamberRelabel ρ σ q.2).val) : Space d × (Fin n → ℝ)) : OnePoint _) =
          compactifiedCellRelabel ρ σ (minimalChamberOnePointCollapse (d := d) σ
            (((q.1,q.2.val) : Space d × (Fin n → ℝ)) : OnePoint _))
        rw [minimalChamberOnePointCollapse_coe σ q]
        exact minimalChamberOnePointCollapse_coe (ρ*σ) (q.1,heightChamberRelabel ρ σ q.2)
      · have hn : labelPermutationLinear ρ p.2 ∉ heightChamber n (ρ*σ) := by
          change ¬ StrictMono (fun i => p.2 (ρ.symm ((ρ*σ) i)))
          simpa only [Equiv.Perm.mul_apply, Equiv.symm_apply_apply] using hp
        have h₁ : (p : OnePoint (Space d × (Fin n → ℝ))) ∉
            range (fun q : Space d × heightChamber n σ =>
              (((q.1,q.2.val) : Space d × (Fin n → ℝ)) : OnePoint _)) := by
          rintro ⟨q,hq⟩
          have he := congrArg Prod.snd (Option.some.inj hq)
          exact hp (he ▸ q.2.property)
        have h₂ : ((p.1,labelPermutationLinear ρ p.2) : OnePoint (Space d × (Fin n → ℝ))) ∉
            range (fun q : Space d × heightChamber n (ρ*σ) =>
              (((q.1,q.2.val) : Space d × (Fin n → ℝ)) : OnePoint _)) := by
          rintro ⟨q,hq⟩
          have he : q.2.val = labelPermutationLinear ρ p.2 :=
            congrArg Prod.snd (Option.some.inj hq)
          exact hn (he ▸ q.2.property)
        change minimalChamberOnePointCollapse (d := d) (ρ*σ)
          ((p.1,labelPermutationLinear ρ p.2) : OnePoint (Space d × (Fin n → ℝ))) =
          compactifiedCellRelabel ρ σ
            (minimalChamberOnePointCollapse (d := d) σ (p : OnePoint _))
        rw [minimalChamberOnePointCollapse_outside _ _ h₁,
          minimalChamberOnePointCollapse_outside _ _ h₂]
        rfl

theorem HabsMap_identityCellRelabel_coherent (R : Type) [CommRing R]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    HabsMap R (d+n) (identityCellRelabelMap (d := d) σ) ≫
      (coherentCellTopHomologyIso R σ hdim).hom =
        (minimalCellTopHomologyIso R d n 1 hdim).hom := by
  change (HabsIsoOfHomotopyEquiv R (d+n)
    (identityCellRelabel (d := d) σ).toHomotopyEquiv).hom ≫
      ((HabsIsoOfHomotopyEquiv R (d+n)
        (identityCellRelabel (d := d) σ).toHomotopyEquiv).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

theorem minimalChamberCollapse_coherent_sign (R : Type) [CommRing R]
    {d n : ℕ} (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    HabsMap R (d+n) (TopCat.ofHom (minimalChamberOnePointCollapse (d := d) σ)) ≫
        (coherentCellTopHomologyIso R σ hdim).hom =
      (Equiv.Perm.sign σ : ℤ) •
        (HabsMap R (d+n) (TopCat.ofHom (minimalChamberOnePointCollapse (d := d) 1)) ≫
          (minimalCellTopHomologyIso R d n 1 hdim).hom) := by
  have h : heightPermutationOnePointMap (Space d) σ ≫
      TopCat.ofHom (minimalChamberOnePointCollapse (d := d) σ) =
      TopCat.ofHom (minimalChamberOnePointCollapse (d := d) 1) ≫
        identityCellRelabelMap (d := d) σ := by
    simpa only [mul_one] using minimalChamberOnePointCollapse_relabel (d := d) σ 1
  have hn := congrArg (fun f => HabsMap R (d+n) f ≫
    (coherentCellTopHomologyIso R σ hdim).hom) h
  dsimp only at hn
  simp only [HabsMap_comp, Category.assoc,
    HabsMap_identityCellRelabel_coherent] at hn
  have hs : HabsMap R (d+n) (heightPermutationOnePointMap (Space d) σ) =
      (Equiv.Perm.sign σ : ℤ) • 𝟙 _ := by
    have hs₀ := heightPermutationOnePointMap_top R (Space d) σ
    have hd : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
    rw [hd] at hs₀
    exact hs₀
  simp only [hs, Preadditive.zsmul_comp, Category.id_comp] at hn
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · simpa only [hσ, Units.val_one, one_smul] using hn
  · have hn' := congrArg Neg.neg hn
    simpa only [hσ, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg] using hn'

end NRR.PrimePowerTopology
