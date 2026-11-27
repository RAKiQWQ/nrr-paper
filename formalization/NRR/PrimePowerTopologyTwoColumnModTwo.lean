import NRR.PrimePowerTopologyShuffleIncidenceDegree
import NRR.PrimePowerTopologyTwoColumnIncidenceSupport
import Mathlib.Data.ZMod.Basic

/-! Characteristic-two coefficients of the genuine first Fuks differential.
The row maps below use the actual minimal-cell pinches and the canonical
positive-degree comparison with the relative minimal Fuks group. -/

noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
open Set Metric Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology
open NRR.SingularHomology.FiniteCellAttachment

namespace NRR.PrimePowerTopology

/-- The actual cone-boundary chart, restricted to the boundary of its disk. -/
def twoColumnBoundaryDiskHomeomorph {d n : ℕ} (S : Finset (Fin n)) :
    twoColumnCharacteristicBoundary (d := d) S ≃ₜ
      diskBoundary (TwoColumnAmbientParameters d n) :=
  (twoColumnDiskHomeomorph S).subtype (fun x =>
    (twoColumnDiskHomeomorph_boundary_iff S x).symm)

/-- With identity relabeling, the disk attaching map is exactly the raw
geometric attaching map in the cone-boundary chart. -/
theorem twoColumnDiskAttachingSphereMinimalPinch_boundaryChart
    {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1)).comp
      ⟨twoColumnBoundaryDiskHomeomorph (canonicalColumnLabels split),
        (twoColumnBoundaryDiskHomeomorph (canonicalColumnLabels split)).continuous⟩ =
    twoColumnShuffleIncidenceMap (d := d) (canonicalColumnLabels split)
      0 split.val (zero_mem_canonicalColumnLabels split)
      (split_not_mem_canonicalColumnLabels split) i₀ σ := by
  ext p
  apply congrArg (minimalCellRetraction (d := d+1) i₀ σ)
  apply Subtype.ext
  change compactifiedConfigurationRelabel 1
    (compactTwoColumnAttaching (canonicalColumnLabels split) 0 split.val _ _
      ((twoColumnDiskHomeomorph (canonicalColumnLabels split)).symm
        ((twoColumnDiskHomeomorph (canonicalColumnLabels split)) p.val))) = _
  rw [Homeomorph.symm_apply_apply, compactifiedConfigurationRelabel_one_apply]
  rfl

/-- Every shuffle gives an isomorphism for the genuine disk-boundary pinch. -/
theorem isIso_HabsMap_twoColumnDiskAttachingSphereMinimalPinch
    (R : Type) [Ring R] {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) (q : ℕ) :
    IsIso (HabsMap R (q+1) (TopCat.ofHom
      (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1)))) := by
  let e := twoColumnBoundaryDiskHomeomorph (d := d) (canonicalColumnLabels split)
  let f := TopCat.ofHom
    (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1))
  let g := TopCat.ofHom (⟨e,e.continuous⟩ : C(_, _))
  letI : IsIso (HabsMap R (q+1) g) :=
    (HabsIsoOfHomotopyEquiv R (q+1) e.toHomotopyEquiv).isIso_hom
  have he : g ≫ f = TopCat.ofHom
      (twoColumnShuffleIncidenceMap (d := d) (canonicalColumnLabels split)
        0 split.val (zero_mem_canonicalColumnLabels split)
        (split_not_mem_canonicalColumnLabels split) i₀ σ) := by
    exact congrArg TopCat.ofHom
      (twoColumnDiskAttachingSphereMinimalPinch_boundaryChart split i₀ σ)
  letI : IsIso (HabsMap R (q+1) g ≫ HabsMap R (q+1) f) := by
    rw [← HabsMap_comp, he]
    exact isIso_HabsMap_twoColumnShuffleIncidence R _ _ _ _ _ _ _ hs q
  exact IsIso.of_isIso_comp_left (HabsMap R (q+1) g) (HabsMap R (q+1) f)

/-- Top homology of the actual model disk, in the orientation used by the
ordered two-column Fuks basis. -/
def twoColumnDiskTopHomologyIso (R : Type) [Ring R] (d n : ℕ) :
    Hrel R (d+n+2) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
      (diskBoundary (TwoColumnAmbientParameters d n))) ≅ ModuleCat.of R R :=
  diskChartHomologyIso R diskBoundary_nonempty (d+n+1) ≪≫
    vectorOnePointTopHomologyIso R (TwoColumnAmbientParameters d n) (d+n+2)
      (finrank_twoColumnAmbientParameters d n) (by omega)

@[simp] theorem twoColumnDiskTopHomologyIso_inv_one
    (R : Type) [CommRing R] (d n : ℕ) :
    (twoColumnDiskTopHomologyIso R d n).inv 1 = twoColumnOrientedDiskClass R d n := rfl

/-- The target sphere orientation, with the genuine minimal-cell dimension. -/
def twoColumnMinimalTargetTopHomologyIso (R : Type) [CommRing R]
    (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Habs R (d+n+1) (TopCat.of (OnePoint (Space (d+1) × heightChamber n σ))) ≅
      ModuleCat.of R R :=
  eqToIso (congrArg (fun k => Habs R k
    (TopCat.of (OnePoint (Space (d+1) × heightChamber n σ))))
      (show d+n+1 = (d+1)+n by omega)) ≪≫
    coherentCellTopHomologyIso R (d := d+1) (n := n) σ (by omega)

/-- A genuine disk-boundary incidence, in the common disk orientation and
coherent minimal-cell orientation. -/
def twoColumnDiskIncidenceCoefficient (R : Type) [CommRing R]
    {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    ModuleCat.of R R ⟶ ModuleCat.of R R :=
  (twoColumnDiskTopHomologyIso R d n).inv ≫
    relδ R (d+n+1) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
      (diskBoundary (TwoColumnAmbientParameters d n))) ≫
    HabsMap R (d+n+1) (TopCat.ofHom
      (twoColumnDiskAttachingSphereMinimalPinch (d := d) i₀ σ (split,1))) ≫
    (twoColumnMinimalTargetTopHomologyIso R d n σ).hom

/-- The real disk connecting map is an isomorphism in the incidence degree. -/
theorem isIso_twoColumnDisk_relδ (R : Type) [Ring R] (d n : ℕ) :
    IsIso (relδ R (d+n+1) (subIncl (Y := TopCat.of (TwoColumnDisk d n))
      (diskBoundary (TwoColumnAmbientParameters d n)))) :=
  isIso_relδ_of_ambient_zero R (d+n+1) _
    (isZero_Habs_closedBall R (d+n+1+1) (by omega) 1 (by norm_num))
    (isZero_Habs_closedBall R (d+n+1) (by omega) 1 (by norm_num))

/-- The disk incidence between two actual rank-one groups is invertible
at every shuffle; no incidence or orientation hypothesis is assumed. -/
theorem isIso_twoColumnDiskIncidenceCoefficient
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    IsIso (twoColumnDiskIncidenceCoefficient R (d := d) split i₀ σ) := by
  letI := isIso_twoColumnDisk_relδ R d n
  letI := isIso_HabsMap_twoColumnDiskAttachingSphereMinimalPinch R
    (d := d) split i₀ σ hs (d+n)
  unfold twoColumnDiskIncidenceCoefficient
  infer_instance

private theorem modTwo_iso_apply_one
    (f : ModuleCat.of (ZMod 2) (ZMod 2) ⟶ ModuleCat.of (ZMod 2) (ZMod 2))
    [IsIso f] : f 1 = 1 := by
  have hne : f 1 ≠ 0 := by
    intro h
    have hi := (ModuleCat.mono_iff_injective f).mp inferInstance
    have hz : f 1 = f 0 := h.trans (map_zero f.hom).symm
    exact one_ne_zero (hi hz)
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (f 1) with h | h
  · exact False.elim (hne h)
  · exact h

/-- Over the field with two elements, every actual shuffle incidence is one. -/
theorem twoColumnDiskIncidenceCoefficient_modTwo_of_shuffle
    {d n : ℕ} [NeZero n] (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle (canonicalColumnLabels split) σ) :
    twoColumnDiskIncidenceCoefficient (ZMod 2) (d := d) split i₀ σ 1 = 1 := by
  letI := isIso_twoColumnDiskIncidenceCoefficient (ZMod 2) (d := d) split i₀ σ hs
  exact modTwo_iso_apply_one _

/-- Readout on the actual minimal relative Fuks group, using the coherent
minimal-cell orientation. This is the existing coherent coefficient,
with only its dimension normalized to the differential's degree. -/
def twoColumnMinimalRelativeCoefficient (R : Type) [CommRing R]
    (d n : ℕ) [NeZero n] (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (fuksRelativeComplex R (d := d+1) (n := n)
      (show d ≤ d+1 by omega)).homology (d+n+1) ⟶ ModuleCat.of R R :=
  eqToHom (congrArg (fun k => (fuksRelativeComplex R (d := d+1) (n := n)
    (show d ≤ d+1 by omega)).homology k) (show d+n+1 = (d+1)+n by omega)) ≫
    coherentMinimalRelativeCoefficient R (d := d+1) (n := n) (by omega) i₀ σ

private theorem relJ_degree_cast (R : Type) [Ring R]
    {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] {k l : ℕ} (h : k = l) :
    relJ R k i ≫ eqToHom (congrArg (fun q => Hrel R q i) h) =
      eqToHom (congrArg (fun q => Habs R q X) h) ≫ relJ R l i := by
  subst l
  simp

private theorem HabsMap_degree_cast (R : Type) [Ring R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) {k l : ℕ} (h : k = l) :
    eqToHom (congrArg (fun q => Habs R q X) h) ≫ HabsMap R l f =
      HabsMap R k f ≫ eqToHom (congrArg (fun q => Habs R q Y) h) := by
  subst l
  simp

/-- The coherent row coefficient after the genuine pair quotient is the
geometric pinch coefficient on the actual minimal skeleton. -/
theorem relJ_comp_coherentMinimalRelativeCoefficient_geometric
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    relJ R (d+n) (compactifiedFuksInclusion (d := d) (n := n)
      (show d-1 ≤ d by omega)) ≫ coherentMinimalRelativeCoefficient R hd i₀ σ =
    (HabsIsoOfHomotopyEquiv R (d+n)
      (minimalLevelHomeomorph d n).toHomotopyEquiv).inv ≫
      coherentMinimalCoefficient R i₀ σ (by omega) := by
  let e := HabsIsoOfHomotopyEquiv R (d+n)
    (minimalLevelHomeomorph d n).toHomotopyEquiv
  have he : e.hom ≫ relJ R (d+n) (compactifiedFuksInclusion (d := d) (n := n)
      (show d-1 ≤ d by omega)) = (minimalActualRelativeComparisonIso R d n hd).hom := rfl
  apply (cancel_epi e.hom).mp
  unfold coherentMinimalRelativeCoefficient
  change e.hom ≫ (relJ R (d+n) _ ≫
    ((minimalActualRelativeComparisonIso R d n hd).inv ≫ _)) = e.hom ≫ (e.inv ≫ _)
  simp only [← Category.assoc, he, Iso.hom_inv_id, Category.id_comp]

/-- The dimension-normalized coherent row coefficient is precisely the
boundary-of-disk incidence for a genuine two-column Fuks basis vector. -/
theorem twoColumnMinimalRelativeCoefficient_fuksDifferential
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    twoColumnMinimalRelativeCoefficient R d n i₀ σ
      (fuksDifferential R (d := d+1) (n := n) (show d ≤ d+1 by omega)
        (show d+1 ≤ d+2 by omega) (d+n+1)
        (twoColumnFuksBasis R d n hn (split,1))) =
    twoColumnDiskIncidenceCoefficient R (d := d) split i₀ σ 1 := by
  rw [fuksDifferential_twoColumnFuksBasis R hn]
  have h := relJ_comp_coherentMinimalRelativeCoefficient_geometric R
    (d := d+1) (n := n) (by omega) i₀ σ
  let g := TopCat.ofHom
    (⟨(minimalLevelHomeomorph (d+1) n).symm,
      (minimalLevelHomeomorph (d+1) n).symm.continuous⟩ : C(_, _)) ≫
      minimalCellRetractionMap (d := d+1) i₀ σ
  have hg : relJ R ((d+1)+n) (compactifiedFuksInclusion (d := d+1) (n := n)
      (show d ≤ d+1 by omega)) ≫
      coherentMinimalRelativeCoefficient R (d := d+1) (n := n) (by omega) i₀ σ =
      HabsMap R ((d+1)+n) g ≫
        (coherentCellTopHomologyIso R (d := d+1) (n := n) σ (by omega)).hom := by
    simpa only [g, HabsMap_comp, Category.assoc, coherentMinimalCoefficient,
      HabsIsoOfHomotopyEquiv] using h
  have h' : relJ R (d+n+1) (compactifiedFuksInclusion (d := d+1) (n := n)
      (show d ≤ d+1 by omega)) ≫ twoColumnMinimalRelativeCoefficient R d n i₀ σ =
      HabsMap R (d+n+1) (TopCat.ofHom
        (⟨(minimalLevelHomeomorph (d+1) n).symm,
          (minimalLevelHomeomorph (d+1) n).symm.continuous⟩ : C(_, _))) ≫
        HabsMap R (d+n+1) (minimalCellRetractionMap (d := d+1) i₀ σ) ≫
          (twoColumnMinimalTargetTopHomologyIso R d n σ).hom := by
    unfold twoColumnMinimalRelativeCoefficient
    rw [← Category.assoc, relJ_degree_cast R _ (show d+n+1 = (d+1)+n by omega),
      Category.assoc, hg, ← Category.assoc,
      HabsMap_degree_cast R _ (show d+n+1 = (d+1)+n by omega)]
    change (HabsMap R (d+n+1) g ≫ _) ≫ _ = _
    simp only [g, HabsMap_comp, Category.assoc]
    rfl
  change (relJ R (d+n+1) _ ≫ twoColumnMinimalRelativeCoefficient R d n i₀ σ) _ = _
  rw [h']
  unfold twoColumnDiskIncidenceCoefficient
  change (twoColumnMinimalTargetTopHomologyIso R d n σ).hom
    ((HabsMap R (d+n+1) (TopCat.ofHom (twoColumnDiskAttachingSphere (d := d) (split,1))) ≫
      HabsMap R (d+n+1) (TopCat.ofHom
        (⟨(minimalLevelHomeomorph (d+1) n).symm,
          (minimalLevelHomeomorph (d+1) n).symm.continuous⟩ : C(_, _))) ≫
      HabsMap R (d+n+1) (minimalCellRetractionMap (d := d+1) i₀ σ)) _) = _
  rw [← HabsMap_comp, ← HabsMap_comp]
  rfl

/-- Non-shuffle incidences of the actual attaching sphere vanish, over
any commutative ring and independently of orientation choices. -/
theorem twoColumnDiskIncidenceCoefficient_eq_zero_of_not_shuffle
    (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
    (split : TwoColumnSplit n) (i₀ : Fin n) (σ : Equiv.Perm (Fin n))
    (hs : ¬ IsColumnShuffle (canonicalColumnLabels split) σ) :
    twoColumnDiskIncidenceCoefficient R (d := d) split i₀ σ = 0 := by
  unfold twoColumnDiskIncidenceCoefficient
  rw [HabsMap_twoColumnDiskAttachingSphereMinimalPinch_eq_zero R i₀ σ (split,1)
    (by simpa using hs) (d+n+1) (by omega), zero_comp, comp_zero, comp_zero]

/-- A complete characteristic-two row computation for the genuine Fuks
differential on a canonical ordered two-column disk. -/
theorem twoColumnMinimalRelativeCoefficient_fuksDifferential_modTwo
    {d n : ℕ} [NeZero n] (hn : 2 ≤ n) (split : TwoColumnSplit n)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    twoColumnMinimalRelativeCoefficient (ZMod 2) d n i₀ σ
      (fuksDifferential (ZMod 2) (d := d+1) (n := n) (show d ≤ d+1 by omega)
        (show d+1 ≤ d+2 by omega) (d+n+1)
        (twoColumnFuksBasis (ZMod 2) d n hn (split,1))) =
      if IsColumnShuffle (canonicalColumnLabels split) σ then 1 else 0 := by
  classical
  rw [twoColumnMinimalRelativeCoefficient_fuksDifferential]
  by_cases hs : IsColumnShuffle (canonicalColumnLabels split) σ
  · rw [if_pos hs]
    exact twoColumnDiskIncidenceCoefficient_modTwo_of_shuffle split i₀ σ hs
  · rw [if_neg hs,
      twoColumnDiskIncidenceCoefficient_eq_zero_of_not_shuffle (ZMod 2) split i₀ σ hs]
    rfl

/-- Summing the actual differential's coherent minimal-cell coordinates
counts the genuine boundary shuffles, hence gives the binomial coefficient
in the field with two elements. -/
theorem sum_twoColumnMinimalRelativeCoefficient_fuksDifferential_modTwo
    {d n : ℕ} [NeZero n] (hn : 2 ≤ n) (split : TwoColumnSplit n) (i₀ : Fin n) :
    (∑ σ : Equiv.Perm (Fin n),
      twoColumnMinimalRelativeCoefficient (ZMod 2) d n i₀ σ
        (fuksDifferential (ZMod 2) (d := d+1) (n := n) (show d ≤ d+1 by omega)
          (show d+1 ≤ d+2 by omega) (d+n+1)
          (twoColumnFuksBasis (ZMod 2) d n hn (split,1)))) =
      (n.choose split.val.val : ZMod 2) := by
  classical
  simp_rw [twoColumnMinimalRelativeCoefficient_fuksDifferential_modTwo hn split i₀]
  rw [Finset.sum_boole, ← Fintype.card_subtype,
    card_actualColumnShuffles, canonicalColumnLabels, card_firstColumnLabels]

end NRR.PrimePowerTopology
