import NRR.PrimePowerTopologyTwoColumnOpen
import NRR.PrimePowerTopologyFilteredChains

/-! Canonical continuous collapse maps onto compactified open Fuks cells.
These are topological maps of the actual filtration spaces; no homology
isomorphism for a closed quotient is asserted without a good-pair proof. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology Filter CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

section OpenEmbedding

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [LocallyCompactSpace Y] (f : X → Y) (hf : IsOpenEmbedding f)

def onePointOpenRangeHomeomorph :
    X ≃ₜ range (fun x : X => (f x : OnePoint Y)) :=
  (OnePoint.isOpenEmbedding_coe.comp hf).isEmbedding.toHomeomorph

/-- An open embedding has a canonical collapse from the whole ambient
one-point compactification, including its point at infinity. -/
def onePointOpenEmbeddingCollapse : C(OnePoint Y, OnePoint X) :=
  ⟨fun y => (onePointOpenRangeHomeomorph f hf).symm.onePointCongr
      (openCollapse (range (fun x : X => (f x : OnePoint Y))) y),
    (onePointOpenRangeHomeomorph f hf).symm.onePointCongr.continuous.comp
      (continuous_openCollapse _ (OnePoint.isOpenEmbedding_coe.comp hf).isOpen_range)⟩

@[simp] theorem onePointOpenEmbeddingCollapse_coe (x : X) :
    onePointOpenEmbeddingCollapse f hf (f x : OnePoint Y) = (x : OnePoint X) := by
  change (onePointOpenRangeHomeomorph f hf).symm.onePointCongr
    (openCollapse (range (fun x : X => (f x : OnePoint Y))) (f x : OnePoint Y)) = _
  have hm : (f x : OnePoint Y) ∈ range (fun x : X => (f x : OnePoint Y)) := ⟨x, rfl⟩
  rw [openCollapse_of_mem (range (fun x : X => (f x : OnePoint Y))) hm]
  change ((onePointOpenRangeHomeomorph f hf).symm
    ⟨(f x : OnePoint Y), ⟨x, rfl⟩⟩ : OnePoint X) = (x : OnePoint X)
  exact congrArg ((↑) : X → OnePoint X)
    ((onePointOpenRangeHomeomorph f hf).symm_apply_apply x)

theorem onePointOpenEmbeddingCollapse_outside (y : OnePoint Y)
    (hy : y ∉ range (fun x : X => (f x : OnePoint Y))) :
    onePointOpenEmbeddingCollapse f hf y = ∞ := by
  change (onePointOpenRangeHomeomorph f hf).symm.onePointCongr
    (openCollapse (range (fun x : X => (f x : OnePoint Y))) y) = _
  rw [openCollapse_of_not_mem _ hy]
  rfl

@[simp] theorem onePointOpenEmbeddingCollapse_infty :
    onePointOpenEmbeddingCollapse f hf ∞ = ∞ := by
  apply onePointOpenEmbeddingCollapse_outside
  rintro ⟨x, hx⟩
  exact OnePoint.coe_ne_infty (f x) hx

end OpenEmbedding

instance locallyCompact_fuksLevel (d n k : ℕ) : LocallyCompactSpace (fuksLevel d n k) :=
  (isClosed_fuksLevel d n k).locallyCompactSpace

/-- Compactifying the actual closed level is the same as taking its
previously defined closed subset in the compactified configuration space. -/
def compactifiedFuksLevelParam (d n k : ℕ) :
    C(OnePoint (fuksLevel d n k), compactifiedFuksLevel d n k) := by
  let f : fuksLevel d n k → Configuration (d+1) n := Subtype.val
  have he : IsClosedEmbedding f := (isClosed_fuksLevel d n k).isClosedEmbedding_subtypeVal
  refine ⟨fun x => ⟨OnePoint.map f x, ?_⟩, ?_⟩
  · induction x using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe x => exact Or.inr ⟨x.val, x.property, rfl⟩
  · apply Continuous.subtype_mk
    apply OnePoint.continuous_map continuous_subtype_val
    rw [coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact]
    exact he.tendsto_cocompact

theorem isEmbedding_compactifiedFuksLevelParam (d n k : ℕ) :
    IsEmbedding (compactifiedFuksLevelParam d n k) := by
  have hinj : Function.Injective (compactifiedFuksLevelParam d n k) := by
    intro x y he
    have hv := congrArg Subtype.val he
    exact Option.map_injective Subtype.val_injective hv
  exact ((compactifiedFuksLevelParam d n k).continuous.isClosedEmbedding hinj).isEmbedding

theorem surjective_compactifiedFuksLevelParam (d n k : ℕ) :
    Function.Surjective (compactifiedFuksLevelParam d n k) := by
  intro x
  rcases x.property with hx | ⟨y, hy, he⟩
  · exact ⟨∞, Subtype.ext hx.symm⟩
  · exact ⟨(⟨y, hy⟩ : fuksLevel d n k), Subtype.ext he⟩

def compactifiedFuksLevelHomeomorph (d n k : ℕ) :
    OnePoint (fuksLevel d n k) ≃ₜ compactifiedFuksLevel d n k :=
  (isEmbedding_compactifiedFuksLevelParam d n k).toHomeomorphOfSurjective
    (surjective_compactifiedFuksLevelParam d n k)

@[simp] theorem compactifiedFuksLevelHomeomorph_infty (d n k : ℕ) :
    (compactifiedFuksLevelHomeomorph d n k ∞).val = ∞ := rfl

@[simp] theorem compactifiedFuksLevelHomeomorph_coe (d n k : ℕ) (x : fuksLevel d n k) :
    (compactifiedFuksLevelHomeomorph d n k (x : OnePoint (fuksLevel d n k))).val =
      (x.val : OnePoint (Configuration (d+1) n)) := rfl

def twoColumnCellCollapse {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    C(compactifiedFuksLevel (d+1) n (d+2), OnePoint (twoColumnDomain (d := d) S)) :=
  (onePointOpenEmbeddingCollapse (twoColumnIntoLevel S)
      (isOpenEmbedding_twoColumnIntoLevel S hne hproper)).comp
    ⟨(compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm,
      (compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm.continuous⟩

@[simp] theorem twoColumnCellCollapse_infty {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    twoColumnCellCollapse (d := d) S hne hproper ⟨∞, Or.inl rfl⟩ = ∞ := by
  change onePointOpenEmbeddingCollapse (twoColumnIntoLevel S) _
    ((compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm ⟨∞, Or.inl rfl⟩) = _
  have he : (compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm ⟨∞, Or.inl rfl⟩ = ∞ :=
    (compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm_apply_apply ∞
  rw [he, onePointOpenEmbeddingCollapse_infty]

/-- On the selected actual open cell, the collapse is precisely its
coordinate inverse, followed by the ordinary inclusion into its sphere. -/
theorem twoColumnCellCollapse_cell {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (p : twoColumnDomain (d := d) S) :
    twoColumnCellCollapse S hne hproper
      ⟨(twoColumnMap S p : OnePoint (Configuration (d+2) n)),
        Or.inr ⟨twoColumnMap S p, twoColumnMap_mem_nextFuks S p, rfl⟩⟩ =
      (p : OnePoint (twoColumnDomain (d := d) S)) := by
  change onePointOpenEmbeddingCollapse (twoColumnIntoLevel S) _
    ((compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm
      ((compactifiedFuksLevelHomeomorph (d+1) n (d+2))
        ((twoColumnIntoLevel S p : fuksLevel (d+1) n (d+2)) :
          OnePoint (fuksLevel (d+1) n (d+2))))) = _
  rw [Homeomorph.symm_apply_apply, onePointOpenEmbeddingCollapse_coe]

theorem twoColumnCellCollapse_vertical {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (x : fuksLevel (d+1) n (d+2)) (hv : x.val ∈ verticalSet (d+1) n) :
    twoColumnCellCollapse S hne hproper
      ⟨(x.val : OnePoint (Configuration (d+2) n)), Or.inr ⟨x.val, x.property, rfl⟩⟩ = ∞ := by
  change onePointOpenEmbeddingCollapse (twoColumnIntoLevel S) _
    ((compactifiedFuksLevelHomeomorph (d+1) n (d+2)).symm
      ((compactifiedFuksLevelHomeomorph (d+1) n (d+2))
        (x : OnePoint (fuksLevel (d+1) n (d+2))))) = _
  rw [Homeomorph.symm_apply_apply]
  apply onePointOpenEmbeddingCollapse_outside
  rintro ⟨p, hp⟩
  have he : twoColumnMap S p = x.val := congrArg Subtype.val (Option.some.inj hp)
  apply twoColumnMap_not_vertical S p hne hproper
  rw [he]
  exact hv

/-- The whole actual lower level, including infinity, is collapsed to the
point at infinity of the selected compactified two-column cell. -/
theorem twoColumnCellCollapse_lower {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (x : compactifiedFuksLevel (d+1) n (d+1)) :
    twoColumnCellCollapse S hne hproper
      (compactifiedFuksInclusion (show d+1 ≤ d+2 by omega) x) = ∞ := by
  rcases x.property with hx | ⟨y, hy, he⟩
  · have hx' : x = ⟨∞, Or.inl rfl⟩ := Subtype.ext hx
    subst x
    exact twoColumnCellCollapse_infty S hne hproper
  · have hnext : y ∈ fuksLevel (d+1) n (d+2) :=
      fuksLevel_mono (d+1) n (show d+1 ≤ d+2 by omega) hy
    have hv : y ∈ verticalSet (d+1) n := by
      rw [← fuksLevel_minimal]
      exact hy
    have hx' : compactifiedFuksInclusion (show d+1 ≤ d+2 by omega) x =
        (⟨(y : OnePoint (Configuration (d+2) n)), Or.inr ⟨y, hnext, rfl⟩⟩ :
          compactifiedFuksLevel (d+1) n (d+2)) := Subtype.ext he.symm
    rw [hx']
    exact twoColumnCellCollapse_vertical S hne hproper ⟨y, hnext⟩ hv

def twoColumnLowerPointMap {d n : ℕ} :
    TopCat.of (compactifiedFuksLevel (d+1) n (d+1)) ⟶ TopCat.of Unit :=
  TopCat.ofHom (ContinuousMap.const _ ())

theorem twoColumnCellCollapse_pair_comm {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    compactifiedFuksInclusion (show d+1 ≤ d+2 by omega) ≫
        TopCat.ofHom (twoColumnCellCollapse (d := d) S hne hproper) =
      twoColumnLowerPointMap ≫
        homologyPointIncl (X := TopCat.of (OnePoint (twoColumnDomain (d := d) S))) ∞ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact twoColumnCellCollapse_lower S hne hproper x

/-- A genuine map from the first actual Fuks relative chain complex to the
selected cell's point-relative singular chains. It is not postulated to be
a quasi-isomorphism. -/
def twoColumnCellRelativeChainMap (R : Type) [CommRing R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    fuksRelativeComplex R (d := d+1) (n := n) (show d+1 ≤ d+2 by omega) ⟶
      relComplex R
        (homologyPointIncl (X := TopCat.of (OnePoint (twoColumnDomain (d := d) S))) ∞) :=
  relComplexMap R
    (compactifiedFuksInclusion (show d+1 ≤ d+2 by omega))
    (homologyPointIncl (X := TopCat.of (OnePoint (twoColumnDomain (d := d) S))) ∞)
    (twoColumnCellCollapse_pair_comm S hne hproper)

/-- The scalar coordinate obtained from the actual collapse map of pairs
and the already proved top fundamental class of that cell. -/
def twoColumnRelativeCoordinate (R : Type) [CommRing R]
    {d n : ℕ} [NeZero n] (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    (fuksRelativeComplex R (d := d+1) (n := n)
      (show d+1 ≤ d+2 by omega)).homology (d+n+2) ⟶ ModuleCat.of R R :=
  HomologicalComplex.homologyMap (twoColumnCellRelativeChainMap R S hne hproper) (d+n+2) ≫
    ((pointRelativePositiveIso R (d+n+1)
      (X := TopCat.of (OnePoint (twoColumnDomain (d := d) S)))
      (∞ : OnePoint (twoColumnDomain (d := d) S))).symm ≪≫
        twoColumnCellTopHomologyIso R d n S).hom

end NRR.PrimePowerTopology
