import NRR.SingularHomologyFiniteCellGroups

/-! The coordinates of a finite disk attachment are induced by the genuine
relative maps of its characteristic disks. Naturality of the relative connecting
homomorphism then reduces each boundary column to its attaching sphere map. -/

noncomputable section
open Set Topology Metric CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePowerTopology

namespace NRR.SingularHomology.FiniteCellAttachment

variable {ι V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X] {A : Set X}

def diskBoundary (V : Type) [NormedAddCommGroup V] : Set (CellDisk V) :=
  {q | ‖q.val‖ = 1}

instance : CompactSpace (diskBoundary V) :=
  isCompact_iff_compactSpace.mp ((isClosed_eq (continuous_norm.comp continuous_subtype_val)
    continuous_const : IsClosed (diskBoundary V)).isCompact)

omit [FiniteDimensional ℝ V] in
theorem diskBoundary_nonempty [Nontrivial V] : (diskBoundary V).Nonempty := by
  obtain ⟨v,hv⟩ := exists_norm_eq V (zero_le_one : (0 : ℝ) ≤ 1)
  exact ⟨⟨v, mem_closedBall_zero_iff.mpr hv.le⟩, hv⟩

/-- The identity characteristic map for a single disk attached to its boundary. -/
def diskAttachment (V : Type) [NormedAddCommGroup V] :
    FiniteCellAttachment Unit V (CellDisk V) (diskBoundary V) where
  characteristic _ := ContinuousMap.id _
  boundary _ _ := Iff.rfl
  interior_unique _ _ _ _ _ he := ⟨rfl, he⟩
  cover x := Or.inr ⟨(), x, rfl⟩

def diskInteriorChart : V ≃ₜ ((diskBoundary V)ᶜ : Set (CellDisk V)) :=
  (diskAttachment V).characteristicInteriorChart ()

variable (P : FiniteCellAttachment ι V X A)

def attachingSphere (i : ι) : C(diskBoundary V, A) :=
  ⟨fun x => ⟨P.characteristic i x.val, (P.boundary i x.val).mpr x.property⟩,
    ((P.characteristic i).continuous.comp continuous_subtype_val).subtype_mk _⟩

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T2Space X] in
theorem characteristic_pair_comm (i : ι) :
    subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V) ≫ TopCat.ofHom (P.characteristic i) =
      TopCat.ofHom (P.attachingSphere i) ≫ subIncl (Y := TopCat.of X) A := rfl

def characteristicRelativeMap (R : Type) [Ring R] (i : ι) (k : ℕ) :
    Hrel R k (subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V)) ⟶
      Hrel R k (subIncl (Y := TopCat.of X) A) :=
  HrelMap R k _ _ (P.characteristic_pair_comm i)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T2Space X] in
theorem characteristicRelativeMap_boundary (R : Type) [Ring R] (i : ι) (k : ℕ) :
    P.characteristicRelativeMap R i (k+1) ≫ relδ R k (subIncl (Y := TopCat.of X) A) =
      relδ R k (subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V)) ≫
        HabsMap R k (TopCat.ofHom (P.attachingSphere i)) :=
  (relδ_naturality R k _ _ (P.characteristic_pair_comm i)).symm

def compactifiedDiskInteriorMap (i : ι) :
    C(OnePoint ((diskBoundary V)ᶜ : Set (CellDisk V)), OnePoint (Aᶜ : Set X)) :=
  (P.compactifiedBranch i).comp
    ⟨diskInteriorChart.symm.onePointCongr, diskInteriorChart.symm.onePointCongr.continuous⟩

theorem characteristic_collapse_square (i : ι) (x : CellDisk V) :
    openCollapse Aᶜ (P.characteristic i x) =
      P.compactifiedDiskInteriorMap i (openCollapse (diskBoundary V)ᶜ x) := by
  by_cases hx : x ∈ diskBoundary V
  · rw [openCollapse_of_not_mem Aᶜ (fun h => h ((P.boundary i x).mpr hx)),
      openCollapse_of_not_mem (diskBoundary V)ᶜ (fun h => h hx)]
    rfl
  · have hp : P.characteristic i x ∈ Aᶜ := fun h => hx ((P.boundary i x).mp h)
    rw [openCollapse_of_mem Aᶜ hp, openCollapse_of_mem (diskBoundary V)ᶜ hx]
    apply congrArg (fun z : (Aᶜ : Set X) => (z : OnePoint (Aᶜ : Set X)))
    apply Subtype.ext
    change P.characteristic i x = P.characteristic i
      (diskInteriorChart (diskInteriorChart.symm (⟨x,hx⟩ : ((diskBoundary V)ᶜ : Set (CellDisk V))))).val
    rw [Homeomorph.apply_symm_apply]

theorem compactifiedDiskInteriorMap_pair_comm (i : ι) :
    homologyPointIncl (X := TopCat.of (OnePoint ((diskBoundary V)ᶜ : Set (CellDisk V)))) ∞ ≫
      TopCat.ofHom (P.compactifiedDiskInteriorMap i) =
    𝟙 (TopCat.of Unit) ≫ homologyPointIncl (X := TopCat.of (OnePoint (Aᶜ : Set X))) ∞ := rfl

variable [Finite ι] [CompactSpace A] [CompactSpace X] (R : Type) [Ring R]

omit [Finite ι] in
private theorem collapseMap_naturality (hne : A.Nonempty) (hb : (diskBoundary V).Nonempty)
    (i : ι) (k : ℕ) :
    P.characteristicRelativeMap R i k ≫ P.relativeCollapseMap R hne k =
      (diskAttachment V).relativeCollapseMap R hb k ≫
        HrelMap R k _ _ (P.compactifiedDiskInteriorMap_pair_comm i) := by
  unfold characteristicRelativeMap relativeCollapseMap
  rw [HrelMap_comp, HrelMap_comp]
  congr 1
  ext x
  exact P.characteristic_collapse_square i x

theorem positiveCollapse_naturality (hne : A.Nonempty) (hb : (diskBoundary V).Nonempty)
    (i : ι) (k : ℕ) :
    P.characteristicRelativeMap R i (k+1) ≫ (P.relativeCollapsePositiveIso R hne k).hom =
      ((diskAttachment V).relativeCollapsePositiveIso R hb k).hom ≫
        HabsMap R (k+1) (TopCat.ofHom (P.compactifiedDiskInteriorMap i)) := by
  let p := pointRelativePositiveIso R k (X := TopCat.of (OnePoint (Aᶜ : Set X))) ∞
  let q := pointRelativePositiveIso R k
    (X := TopCat.of (OnePoint ((diskBoundary V)ᶜ : Set (CellDisk V)))) ∞
  let g := TopCat.ofHom (P.compactifiedDiskInteriorMap i)
  have hn := relJ_naturality R (k+1) _ _ (P.compactifiedDiskInteriorMap_pair_comm i)
  change q.hom ≫ _ = HabsMap R (k+1) g ≫ p.hom at hn
  change P.characteristicRelativeMap R i (k+1) ≫ P.relativeCollapseMap R hne (k+1) ≫ p.inv =
    ((diskAttachment V).relativeCollapseMap R hb (k+1) ≫ q.inv) ≫ HabsMap R (k+1) g
  apply (cancel_mono p.hom).mp
  simp only [Category.assoc, p.inv_hom_id, Category.comp_id, ← hn, q.inv_hom_id_assoc]
  exact P.collapseMap_naturality R hne hb i (k+1)

/-- Disk-relative homology expressed in the very same radial vector chart used
to orient all the cells; this choice is shared by every characteristic map. -/
def diskChartHomologyIso (hb : (diskBoundary V).Nonempty) (k : ℕ) :
    Hrel R (k+1) (subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V)) ≅
      Habs R (k+1) (TopCat.of (OnePoint V)) :=
  (diskAttachment V).relativeCollapsePositiveIso R hb k ≪≫
    HabsIsoOfHomotopyEquiv R (k+1) diskInteriorChart.symm.onePointCongr.toHomotopyEquiv

theorem characteristicRelativeMap_eq_branch (hne : A.Nonempty) (hb : (diskBoundary V).Nonempty)
    (i : ι) (k : ℕ) :
    P.characteristicRelativeMap R i (k+1) ≫ (P.relativeCollapsePositiveIso R hne k).hom =
      (diskChartHomologyIso R hb k).hom ≫ HabsMap R (k+1) (TopCat.ofHom (P.compactifiedBranch i)) := by
  rw [P.positiveCollapse_naturality R hne hb i k]
  change _ = (((diskAttachment V).relativeCollapsePositiveIso R hb k).hom ≫
    HabsMap R (k+1) (TopCat.ofHom ⟨diskInteriorChart.symm.onePointCongr,
      diskInteriorChart.symm.onePointCongr.continuous⟩)) ≫ _
  rw [Category.assoc, ← HabsMap_comp]
  rfl

/-- In cellular coordinates each *actual relative characteristic map* is the
single-coordinate inclusion of the homology of the disk-boundary pair. -/
theorem relativeCellEquiv_characteristic [Nonempty ι] [DecidableEq ι]
    (hne : A.Nonempty) (hb : (diskBoundary V).Nonempty) (i : ι) (k : ℕ)
    (x : Hrel R (k+1) (subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V))) :
    P.relativeCellEquiv R hne k (P.characteristicRelativeMap R i (k+1) x) =
      Pi.single i ((diskChartHomologyIso R hb k).hom x) := by
  classical
  letI := Fintype.ofFinite ι
  apply (P.relativeCellEquiv R hne k).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply (P.relativeCollapsePositiveIso R hne k).toLinearEquiv.injective
  let E := P.relativeCollapsePositiveIso R hne k
  let y := (diskChartHomologyIso R hb k).hom x
  change E.hom (P.characteristicRelativeMap R i (k+1) x) =
    E.toLinearEquiv (E.toLinearEquiv.symm ((P.wedgePresentation.homologySumLinear R k) (Pi.single i y)))
  rw [LinearEquiv.apply_symm_apply, FiniteWedgePresentation.homologySumLinear_single]
  exact congrArg (fun f : Hrel R (k+1) (subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V)) ⟶
    Habs R (k+1) (TopCat.of (OnePoint (Aᶜ : Set X))) => f x)
    (P.characteristicRelativeMap_eq_branch R hne hb i k)


/-- One orientation of the model disk is used for all characteristic maps of
the attachment. Its image under the chart is the vector compactification class. -/
def diskChartTopClass (hb : (diskBoundary V).Nonempty) (q : ℕ)
    (hdim : Module.finrank ℝ V = q+1) :
    Hrel R (q+1) (subIncl (Y := TopCat.of (CellDisk V)) (diskBoundary V)) :=
  (diskChartHomologyIso R hb q).toLinearEquiv.symm
    ((vectorOnePointTopHomologyIso R V (q+1) hdim (by omega)).toLinearEquiv.symm (1 : R))

theorem relativeTopEquiv_characteristic [Nonempty ι] [DecidableEq ι]
    (hne : A.Nonempty) (hb : (diskBoundary V).Nonempty) (i : ι) (q : ℕ)
    (hdim : Module.finrank ℝ V = q+1) :
    P.relativeTopEquiv R hne q hdim
      (P.characteristicRelativeMap R i (q+1) (diskChartTopClass R hb q hdim)) =
      Pi.single i (1 : R) := by
  ext j
  let e := (vectorOnePointTopHomologyIso R V (q+1) hdim (by omega)).toLinearEquiv
  change e ((P.relativeCellEquiv R hne q
    (P.characteristicRelativeMap R i (q+1) (diskChartTopClass R hb q hdim))) j) = _
  rw [P.relativeCellEquiv_characteristic]
  by_cases hij : j = i
  · subst j
    simp only [Pi.single_eq_same]
    change e ((diskChartHomologyIso R hb q).toLinearEquiv
      ((diskChartHomologyIso R hb q).toLinearEquiv.symm (e.symm (1 : R)))) = 1
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · simp [Pi.single_eq_of_ne hij]

end NRR.SingularHomology.FiniteCellAttachment
