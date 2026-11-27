import NRR.PrimePowerTopologyTwoColumns
import NRR.PrimePowerTopologyOnePointHomology

/-! Euclidean cell coordinates for the actual two-column strata and the
fundamental classes of their genuine one-point compactifications. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology Metric CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

def boundedTwoColumnHeights {n : ℕ} (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  twoColumnHeights S ∩ {t | ∀ i, t i ∈ Ioo (-(Real.pi/2)) (Real.pi/2)}

theorem isOpen_boundedTwoColumnHeights {n : ℕ} (S : Finset (Fin n)) :
    IsOpen (boundedTwoColumnHeights S) := by
  apply (isOpen_twoColumnHeights S).inter
  have repr : {t : Fin n → ℝ | ∀ i, t i ∈ Ioo (-(Real.pi/2)) (Real.pi/2)} =
      ⋂ i : Fin n, (fun t : Fin n → ℝ => t i) ⁻¹' Ioo (-(Real.pi/2)) (Real.pi/2) := by
    ext t
    simp
  rw [repr]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

theorem convex_boundedTwoColumnHeights {n : ℕ} (S : Finset (Fin n)) :
    Convex ℝ (boundedTwoColumnHeights S) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_twoColumnHeights S hx.1 hy.1 ha hb hab, ?_⟩
  intro i
  exact convex_Ioo (-(Real.pi/2)) (Real.pi/2) (hx.2 i) (hy.2 i) ha hb hab

theorem boundedTwoColumnHeights_nonempty {n : ℕ} (S : Finset (Fin n)) :
    (boundedTwoColumnHeights S).Nonempty := by
  obtain ⟨t, ht⟩ := twoColumnHeights_nonempty S
  exact ⟨fun i => Real.arctan (t i),
    (fun i j hij hmem => Real.arctan_strictMono (ht i j hij hmem)),
    fun i => Real.arctan_mem_Ioo (t i)⟩

theorem isBounded_boundedTwoColumnHeights {n : ℕ} (S : Finset (Fin n)) :
    Bornology.IsBounded (boundedTwoColumnHeights S) := by
  have hc := isCompact_univ_pi (fun _ : Fin n =>
    isCompact_Icc (a := -(Real.pi/2)) (b := Real.pi/2))
  apply hc.isBounded.subset
  intro t ht i _
  exact ⟨(ht.2 i).1.le, (ht.2 i).2.le⟩

def boundTwoColumnHeights {n : ℕ} (S : Finset (Fin n)) :
    twoColumnHeights S ≃ₜ boundedTwoColumnHeights S where
  toFun t := ⟨fun i => Real.arctan (t.val i),
    (fun i j hij hmem => Real.arctan_strictMono (t.property i j hij hmem)),
    fun i => Real.arctan_mem_Ioo (t.val i)⟩
  invFun t := ⟨fun i => Real.tanOrderIso ⟨t.val i, t.property.2 i⟩, by
    intro i j hij hmem
    apply Real.tanOrderIso.strictMono
    exact t.property.1 i j hij hmem⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    exact Real.tanOrderIso.apply_symm_apply (t.val i)
  right_inv t := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (Real.tanOrderIso.symm_apply_apply ⟨t.val i, t.property.2 i⟩)
  continuous_toFun :=
    (continuous_pi (fun i => Real.continuous_arctan.comp
      ((continuous_apply i).comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact Real.tanOrderIso.toHomeomorph.continuous.comp
      (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)

/-- The height variables satisfying the actual within-column inequalities
form a genuine Euclidean n-cell. -/
def twoColumnHeightsEuclidean {n : ℕ} (S : Finset (Fin n)) :
    twoColumnHeights S ≃ₜ (Fin n → ℝ) := by
  classical
  let witness := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_boundedTwoColumnHeights S)
    (by simpa only [(isOpen_boundedTwoColumnHeights S).interior_eq]
      using boundedTwoColumnHeights_nonempty S)
    (isBounded_boundedTwoColumnHeights S)
  let e := Classical.choose witness
  have he : e '' interior (boundedTwoColumnHeights S) = ball 0 1 :=
    (Classical.choose_spec witness).1
  rw [(isOpen_boundedTwoColumnHeights S).interior_eq] at he
  exact (boundTwoColumnHeights S).trans
    ((e.image (boundedTwoColumnHeights S)).trans
      ((Homeomorph.setCongr he).trans Homeomorph.unitBall.symm))

def twoColumnDomainProduct {d n : ℕ} (S : Finset (Fin n)) :
    twoColumnDomain (d := d) S ≃ₜ ((Space d × ℝ) × twoColumnHeights S) × Ioi (0 : ℝ) where
  toFun p := ((p.val.1.1, ⟨p.val.1.2, p.property.2⟩), ⟨p.val.2, p.property.1⟩)
  invFun q := ⟨((q.1.1, q.1.2.val), q.2.val), q.2.property, q.1.2.property⟩
  left_inv p := rfl
  right_inv q := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Actual free cell coordinates of dimension d+n+2, including the positive
column gap. No compactified attaching map or homological comparison is assumed. -/
def twoColumnDomainEuclidean {d n : ℕ} (S : Finset (Fin n)) :
    twoColumnDomain (d := d) S ≃ₜ TwoColumnAmbientParameters d n :=
  (twoColumnDomainProduct S).trans
    (((Homeomorph.refl (Space d × ℝ)).prodCongr (twoColumnHeightsEuclidean S)).prodCongr
      Real.expOrderIso.toHomeomorph.symm)

def twoColumnCellSphere (d n : ℕ) (S : Finset (Fin n)) :
    OnePoint (twoColumnDomain (d := d) S) ≃ₜ Sph (d+n+2) :=
  (twoColumnDomainEuclidean S).onePointCongr.trans
    (vectorOnePointSphere (TwoColumnAmbientParameters d n) (d+n+2)
      (finrank_twoColumnAmbientParameters d n))

variable (R : Type) [Ring R]

/-- The actual top singular homology of the compactified two-column cell. -/
def twoColumnCellTopHomologyIso (d n : ℕ) (S : Finset (Fin n)) :
    Habs R (d+n+2) (TopCat.of (OnePoint (twoColumnDomain (d := d) S))) ≅ ModuleCat.of R R :=
  HabsIsoOfHomotopyEquiv R (d+n+2) (twoColumnCellSphere d n S).toHomotopyEquiv ≪≫
    sphereTopHomologyIso R (d+n+1)

theorem isZero_twoColumnCellHomology_off_top (d n k : ℕ) (S : Finset (Fin n))
    (hk : k ≠ 0) (hktop : k ≠ d+n+2) :
    IsZero (Habs R k (TopCat.of (OnePoint (twoColumnDomain (d := d) S)))) :=
  IsZero.of_iso (isZero_Habs_sphere_off_top R k (d+n+2) hk hktop)
    (HabsIsoOfHomotopyEquiv R k (twoColumnCellSphere d n S).toHomotopyEquiv)

end NRR.PrimePowerTopology
