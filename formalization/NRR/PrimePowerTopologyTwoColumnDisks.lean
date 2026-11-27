import NRR.PrimePowerTopologyTwoColumnPresentation
import NRR.ClosedPolyhedralCone

/-! Closed disk characteristic maps for the actual first nonminimal
Fuks layer, with the exact lower-level boundary condition. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Metric Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

theorem closedTwoColumnDomain_eq_cone {d n : ℕ} (S : Finset (Fin n)) :
    closedTwoColumnDomain (d := d) S =
      ClosedPolyhedralCone.carrier (twoColumnConeFunctional (d := d) S) := by
  ext p
  exact closedTwoColumnDomain_iff_cone S p

def twoColumnClosedConeHomeomorph {d n : ℕ} (S : Finset (Fin n)) :
    closedTwoColumnDomain (d := d) S ≃ₜ
      ClosedPolyhedralCone.carrier (twoColumnConeFunctional (d := d) S) :=
  Homeomorph.setCongr (closedTwoColumnDomain_eq_cone S)

def twoColumnCompactConeHomeomorph {d n : ℕ} (S : Finset (Fin n)) :
    OnePoint (closedTwoColumnDomain (d := d) S) ≃ₜ
      OnePoint (ClosedPolyhedralCone.carrier (twoColumnConeFunctional (d := d) S)) :=
  (twoColumnClosedConeHomeomorph S).onePointCongr

theorem twoColumnCompactConeHomeomorph_boundary_iff {d n : ℕ}
    (S : Finset (Fin n)) (p : OnePoint (closedTwoColumnDomain (d := d) S)) :
    twoColumnCompactConeHomeomorph S p ∈
        ClosedPolyhedralCone.compactifiedBoundary (twoColumnConeFunctional S) ↔
      p ∈ twoColumnCharacteristicBoundary S := by
  induction p using OnePoint.rec with
  | infty =>
      simp [twoColumnCompactConeHomeomorph, Homeomorph.onePointCongr_apply,
        twoColumnCharacteristicBoundary]
  | coe p =>
      change ((twoColumnClosedConeHomeomorph S p) :
        OnePoint (ClosedPolyhedralCone.carrier (twoColumnConeFunctional (d := d) S))) ∈
          ClosedPolyhedralCone.compactifiedBoundary (twoColumnConeFunctional (d := d) S) ↔
        (p : OnePoint (closedTwoColumnDomain (d := d) S)) ∈ twoColumnCharacteristicBoundary S
      rw [ClosedPolyhedralCone.coe_mem_compactifiedBoundary_iff,
        mem_twoColumnCharacteristicBoundary_coe]
      change (¬ ∀ a, 0 < twoColumnConeFunctional S a p.val) ↔ _
      exact not_congr (twoColumnDomain_iff_strictCone S p.val).symm

/-- The actual closed parameter compactification is a disk as a pair,
not merely a contractible compact space. -/
theorem exists_twoColumnDiskHomeomorph_pair {d n : ℕ} (S : Finset (Fin n)) :
    ∃ e : OnePoint (closedTwoColumnDomain (d := d) S) ≃ₜ
        closedBall (0 : TwoColumnAmbientParameters d n) 1,
      ∀ p, ‖(e p).val‖ = 1 ↔ p ∈ twoColumnCharacteristicBoundary S := by
  obtain ⟨e, he⟩ := ClosedPolyhedralCone.exists_onePointHomeomorphClosedBall_pair
    (twoColumnConeFunctional (d := d) S) (twoColumnConeDirection_positive S)
  refine ⟨(twoColumnCompactConeHomeomorph S).trans e, ?_⟩
  intro p
  simpa only [Homeomorph.trans_apply, mem_sphere_zero_iff_norm] using
    (he (twoColumnCompactConeHomeomorph S p)).trans
      (twoColumnCompactConeHomeomorph_boundary_iff S p)

def twoColumnDiskHomeomorph {d n : ℕ} (S : Finset (Fin n)) :
    OnePoint (closedTwoColumnDomain (d := d) S) ≃ₜ
      closedBall (0 : TwoColumnAmbientParameters d n) 1 :=
  (exists_twoColumnDiskHomeomorph_pair S).choose

theorem twoColumnDiskHomeomorph_boundary_iff {d n : ℕ} (S : Finset (Fin n))
    (p : OnePoint (closedTwoColumnDomain (d := d) S)) :
    ‖(twoColumnDiskHomeomorph S p).val‖ = 1 ↔
      p ∈ twoColumnCharacteristicBoundary S :=
  (exists_twoColumnDiskHomeomorph_pair S).choose_spec p

abbrev TwoColumnDisk (d n : ℕ) := closedBall (0 : TwoColumnAmbientParameters d n) 1

def orderedTwoColumnDiskCharacteristic {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n) :
    C(TwoColumnDisk d n, compactifiedFuksLevel (d+1) n (d+2)) :=
  (orderedTwoColumnCharacteristic c).comp
    ⟨(twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm,
      (twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm.continuous⟩

/-- Exactly the sphere boundary, including all collision faces and the
original point at infinity, maps into the genuine lower level. -/
theorem orderedTwoColumnDiskCharacteristic_mem_lower_iff {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n) (q : TwoColumnDisk d n) :
    (orderedTwoColumnDiskCharacteristic c q).val ∈ compactifiedFuksLevel (d+1) n (d+1) ↔
      ‖q.val‖ = 1 := by
  rw [orderedTwoColumnDiskCharacteristic, ContinuousMap.comp_apply,
    orderedTwoColumnCharacteristic_mem_lower_iff]
  exact ((twoColumnDiskHomeomorph_boundary_iff (canonicalColumnLabels c.1)
    ((twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm q)).symm.trans
      (by rw [Homeomorph.apply_symm_apply]))

def twoColumnLowerSubset (d n : ℕ) :
    Set (compactifiedFuksLevel (d+1) n (d+2)) :=
  Subtype.val ⁻¹' compactifiedFuksLevel (d+1) n (d+1)

theorem orderedTwoColumnDiskCharacteristic_interior_unique {d n : ℕ} [NeZero n]
    (c e : TwoColumnCellIndex n) (q r : TwoColumnDisk d n)
    (hq : ‖q.val‖ < 1)
    (he : orderedTwoColumnDiskCharacteristic c q = orderedTwoColumnDiskCharacteristic e r) :
    c = e ∧ q = r := by
  have hn : (orderedTwoColumnDiskCharacteristic c q).val ∉
      compactifiedFuksLevel (d+1) n (d+1) := by
    rw [orderedTwoColumnDiskCharacteristic_mem_lower_iff]
    exact ne_of_lt hq
  have hc : c = e := by
    by_contra hce
    exact hn (orderedTwoColumnCharacteristic_intersection_lower c e hce
      ((twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm q)
      ((twoColumnDiskHomeomorph (canonicalColumnLabels e.1)).symm r) he)
  subst e
  refine ⟨rfl, ?_⟩
  have hp : (twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm q ∉
      twoColumnCharacteristicBoundary (canonicalColumnLabels c.1) := by
    intro hp
    exact hn ((orderedTwoColumnCharacteristic_mem_lower_iff c _).mpr hp)
  have hr : (twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm r ∉
      twoColumnCharacteristicBoundary (canonicalColumnLabels c.1) := by
    intro hr
    apply hn
    rw [he]
    exact (orderedTwoColumnCharacteristic_mem_lower_iff c _).mpr hr
  exact (twoColumnDiskHomeomorph (canonicalColumnLabels c.1)).symm.injective
    (orderedTwoColumnCharacteristic_injective_on_interior c hp hr he)

theorem orderedTwoColumnDiskCharacteristic_cover {d n : ℕ} [NeZero n]
    (x : compactifiedFuksLevel (d+1) n (d+2)) :
    x ∈ twoColumnLowerSubset d n ∨
      ∃ c q, orderedTwoColumnDiskCharacteristic c q = x := by
  obtain ⟨y,hy⟩ := twoColumnCharacteristicPresentation_surjective (d := d) (n := n) x
  cases y with
  | inl a =>
      left
      change x.val ∈ compactifiedFuksLevel (d+1) n (d+1)
      rw [← hy]
      exact a.property
  | inr z =>
      right
      refine ⟨z.1, twoColumnDiskHomeomorph (canonicalColumnLabels z.1.1) z.2, ?_⟩
      change orderedTwoColumnCharacteristic z.1
        ((twoColumnDiskHomeomorph (canonicalColumnLabels z.1.1)).symm
          (twoColumnDiskHomeomorph (canonicalColumnLabels z.1.1) z.2)) = x
      rw [Homeomorph.symm_apply_apply]
      exact hy

end NRR.PrimePowerTopology
