import NRR.PrimePowerTopologyShuffleOrientation

/-! The relative signs of the actual disk-boundary shuffle incidences. -/

noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory
open NRR.SingularHomology NRR.SingularHomology.FiniteCellAttachment
open NRR.PrimePower

namespace NRR.PrimePowerTopology

theorem isColumnShuffle_one {n : ℕ} (S : Finset (Fin n)) :
    IsColumnShuffle S (1 : Equiv.Perm (Fin n)) := by
  intro i j hij _
  exact hij

theorem twoColumnShuffleIncidenceMap_coherent_relative_sign
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    HabsMap R ((d+1)+n) (TopCat.ofHom
      (twoColumnShuffleIncidenceMap (d := d) S iL iR hL hR i₀ σ)) ≫
        (coherentCellTopHomologyIso R σ (by omega)).hom =
      (Equiv.Perm.sign σ : ℤ) •
        (HabsMap R ((d+1)+n) (TopCat.ofHom
          (twoColumnShuffleIncidenceMap (d := d) S iL iR hL hR i₀ 1)) ≫
            (coherentCellTopHomologyIso R 1 (by omega)).hom) := by
  rw [twoColumnShuffleIncidenceMap_coherent_sign R S iL iR hL hR i₀ σ hs,
    twoColumnShuffleIncidenceMap_coherent_sign R S iL iR hL hR i₀ 1
      (isColumnShuffle_one S)]
  simp

private theorem HabsMap_orientation_degree_cast (R : Type) [Ring R]
    {X Y : TopCat} (f : X ⟶ Y) {q k : ℕ} (h : q = k) :
    eqToHom (congrArg (fun j => Habs R j X) h) ≫ HabsMap R k f =
      HabsMap R q f ≫ eqToHom (congrArg (fun j => Habs R j Y) h) := by
  subst k
  simp

theorem twoColumnShuffleIncidenceMap_relative_sign
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    HabsMap R (d+n+1) (TopCat.ofHom (twoColumnShuffleIncidenceMap (d := d)
      (canonicalColumnLabels split) 0 split.val (zero_mem_canonicalColumnLabels split)
      (split_not_mem_canonicalColumnLabels split) i₀ σ)) ≫
        (twoColumnMinimalTargetTopHomologyIso R d n σ).hom =
      (Equiv.Perm.sign σ : ℤ) •
        (HabsMap R (d+n+1) (TopCat.ofHom (twoColumnShuffleIncidenceMap (d := d)
          (canonicalColumnLabels split) 0 split.val (zero_mem_canonicalColumnLabels split)
          (split_not_mem_canonicalColumnLabels split) i₀ 1)) ≫
            (twoColumnMinimalTargetTopHomologyIso R d n 1).hom) := by
  have h := twoColumnShuffleIncidenceMap_coherent_relative_sign R
    (d := d) (canonicalColumnLabels split) 0 split.val
    (zero_mem_canonicalColumnLabels split) (split_not_mem_canonicalColumnLabels split) i₀ σ hs
  have he : d+n+1 = (d+1)+n := by omega
  have h' := congrArg (fun f => eqToHom (congrArg (fun j => Habs R j
    (TopCat.of (twoColumnCharacteristicBoundary (d := d) (canonicalColumnLabels split)))) he) ≫ f) h
  dsimp only at h'
  simp only [Preadditive.comp_zsmul, ← Category.assoc] at h'
  have hσ := HabsMap_orientation_degree_cast R (TopCat.ofHom
    (twoColumnShuffleIncidenceMap (d := d) (canonicalColumnLabels split) 0 split.val
      (zero_mem_canonicalColumnLabels split) (split_not_mem_canonicalColumnLabels split) i₀ σ)) he
  have h₁ := HabsMap_orientation_degree_cast R (TopCat.ofHom
    (twoColumnShuffleIncidenceMap (d := d) (canonicalColumnLabels split) 0 split.val
      (zero_mem_canonicalColumnLabels split) (split_not_mem_canonicalColumnLabels split) i₀ 1)) he
  rw [hσ, h₁] at h'
  simpa only [twoColumnMinimalTargetTopHomologyIso, Iso.trans_hom,
    eqToIso.hom, Category.assoc] using h'

theorem twoColumnDiskAttachingSphereMinimalPinch_relative_sign
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    HabsMap R (d+n+1) (TopCat.ofHom
      (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1))) ≫
        (twoColumnMinimalTargetTopHomologyIso R d n σ).hom =
      (Equiv.Perm.sign σ : ℤ) •
        (HabsMap R (d+n+1) (TopCat.ofHom
          (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ 1 (split,1))) ≫
            (twoColumnMinimalTargetTopHomologyIso R d n 1).hom) := by
  let e := twoColumnBoundaryDiskHomeomorph (d := d) (canonicalColumnLabels split)
  let g := TopCat.ofHom (⟨e,e.continuous⟩ : C(_, _))
  letI : IsIso (HabsMap R (d+n+1) g) :=
    (HabsIsoOfHomotopyEquiv R (d+n+1) e.toHomotopyEquiv).isIso_hom
  have hg (τ : Equiv.Perm (Fin n)) : HabsMap R (d+n+1) g ≫
      HabsMap R (d+n+1) (TopCat.ofHom
        (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ τ (split,1))) =
      HabsMap R (d+n+1) (TopCat.ofHom (twoColumnShuffleIncidenceMap (d := d)
        (canonicalColumnLabels split) 0 split.val (zero_mem_canonicalColumnLabels split)
        (split_not_mem_canonicalColumnLabels split) i₀ τ)) := by
    rw [← HabsMap_comp]
    exact congrArg (fun f => HabsMap R (d+n+1) (TopCat.ofHom f))
      (twoColumnDiskAttachingSphereMinimalPinch_boundaryChart split i₀ τ)
  apply (cancel_epi (HabsMap R (d+n+1) g)).mp
  simp only [Preadditive.comp_zsmul, ← Category.assoc, hg]
  exact twoColumnShuffleIncidenceMap_relative_sign R split i₀ σ hs

/-- All true disk incidence coefficients share the same common-face
amplitude; their only relative sign is the actual label-permutation sign. -/
theorem twoColumnDiskIncidenceCoefficient_of_shuffle
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    twoColumnDiskIncidenceCoefficient R (d := d) split i₀ σ =
      (Equiv.Perm.sign σ : ℤ) • twoColumnDiskIncidenceCoefficient R (d := d) split i₀ 1 := by
  unfold twoColumnDiskIncidenceCoefficient
  simp only [Category.assoc, twoColumnDiskAttachingSphereMinimalPinch_relative_sign R split i₀ σ hs,
    Preadditive.comp_zsmul]

end NRR.PrimePowerTopology
