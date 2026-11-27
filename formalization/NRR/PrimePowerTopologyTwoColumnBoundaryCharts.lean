import NRR.PrimePowerTopologyTwoColumnDisks
import NRR.PrimePowerTopologyMinimalWedge

/-! Actual collision-free shuffle charts on the characteristic boundary.
They are open in that boundary, and the attaching map is the genuine
minimal vertical chart on each one. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Metric Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

def twoColumnShuffleFace {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    C(Space (d+1) × heightChamber n σ, closedTwoColumnDomain (d := d) S) where
  toFun p := ⟨((horizontalHeight d p.1,p.2.val),0), by
    refine ⟨le_refl 0, ?_⟩
    have ht := (twoColumnHeights_iff_shuffle S σ p.2.property).mpr hs
    exact fun i j hij hijS => (ht i j hij hijS).le⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((horizontalHeight d).continuous.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).prodMk continuous_const

def twoColumnShuffleBoundaryChart {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    C(Space (d+1) × heightChamber n σ, twoColumnCharacteristicBoundary (d := d) S) where
  toFun p := ⟨((twoColumnShuffleFace S σ hs p) :
      OnePoint (closedTwoColumnDomain (d := d) S)), by
    rw [mem_twoColumnCharacteristicBoundary_coe]
    intro hp
    exact (lt_irrefl (0 : ℝ)) hp.1⟩
  continuous_toFun := (OnePoint.continuous_coe.comp
    (twoColumnShuffleFace S σ hs).continuous).subtype_mk _

theorem twoColumnShuffleBoundaryChart_injective {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    Function.Injective (twoColumnShuffleBoundaryChart (d := d) S σ hs) := by
  intro p q he
  have h := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val he))
  have hu : p.1 = q.1 := (horizontalHeight d).injective
    (congrArg (fun z : TwoColumnAmbientParameters d n => z.1.1) h)
  have ht : p.2 = q.2 := Subtype.ext
    (congrArg (fun z : TwoColumnAmbientParameters d n => z.1.2) h)
  exact Prod.ext hu ht

theorem range_twoColumnShuffleBoundaryChart {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    range (twoColumnShuffleBoundaryChart (d := d) S σ hs) =
      Subtype.val ⁻¹' (OnePoint.some ''
        {p : closedTwoColumnDomain (d := d) S | p.val.1.2 ∈ heightChamber n σ}) := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨twoColumnShuffleFace S σ hs p,p.2.property,rfl⟩
  · rintro ⟨p,hp,hz⟩
    have hb : (p : OnePoint (closedTwoColumnDomain (d := d) S)) ∈
        twoColumnCharacteristicBoundary S := hz ▸ z.property
    have hgap : p.val.2 = 0 := by
      apply le_antisymm _ p.property.1
      by_contra h
      have ht := (twoColumnHeights_iff_shuffle S σ hp).mpr hs
      exact ((mem_twoColumnCharacteristicBoundary_coe S p).mp hb)
        ⟨lt_of_not_ge h,ht⟩
    refine ⟨((horizontalHeight d).symm p.val.1.1,⟨p.val.1.2,hp⟩), ?_⟩
    apply Subtype.ext
    change OnePoint.some (twoColumnShuffleFace S σ hs
      ((horizontalHeight d).symm p.val.1.1,⟨p.val.1.2,hp⟩)) = z.val
    rw [← hz]
    congr 1
    apply Subtype.ext
    change (((horizontalHeight d ((horizontalHeight d).symm p.val.1.1)),p.val.1.2),0) = p.val
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hgap.symm

theorem isOpen_range_twoColumnShuffleBoundaryChart {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    IsOpen (range (twoColumnShuffleBoundaryChart (d := d) S σ hs)) := by
  rw [range_twoColumnShuffleBoundaryChart]
  refine (OnePoint.isOpenEmbedding_coe.isOpenMap _ ?_).preimage continuous_subtype_val
  exact (isOpen_heightChamber n σ).preimage
    (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))

theorem isEmbedding_twoColumnShuffleFace {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    IsEmbedding (twoColumnShuffleFace (d := d) S σ hs) := by
  let recovery : C(closedTwoColumnDomain (d := d) S, Space (d+1) × (Fin n → ℝ)) :=
    ⟨fun p => ((horizontalHeight d).symm p.val.1.1,p.val.1.2), by fun_prop⟩
  have he : IsEmbedding (fun p : Space (d+1) × heightChamber n σ => (p.1,p.2.val)) :=
    IsEmbedding.id.prodMap IsEmbedding.subtypeVal
  have hcomp : (fun p => recovery (twoColumnShuffleFace S σ hs p)) =
      (fun p : Space (d+1) × heightChamber n σ => (p.1,p.2.val)) := by
    funext p
    simp only [recovery,ContinuousMap.coe_mk,twoColumnShuffleFace,
      ContinuousLinearEquiv.symm_apply_apply]
  apply IsEmbedding.of_comp (twoColumnShuffleFace S σ hs).continuous recovery.continuous
  change IsEmbedding (fun p => recovery (twoColumnShuffleFace S σ hs p))
  rw [hcomp]
  exact he

theorem isOpenEmbedding_twoColumnShuffleBoundaryChart {d n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) :
    IsOpenEmbedding (twoColumnShuffleBoundaryChart (d := d) S σ hs) := by
  refine ⟨?_, isOpen_range_twoColumnShuffleBoundaryChart S σ hs⟩
  apply IsEmbedding.of_comp (twoColumnShuffleBoundaryChart S σ hs).continuous
    continuous_subtype_val
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp
    (isEmbedding_twoColumnShuffleFace S σ hs)

theorem twoColumnShuffleBoundaryChart_attaching {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ)
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) (i₀ : Fin n)
    (p : Space (d+1) × heightChamber n σ) :
    compactTwoColumnAttaching S iL iR hL hR
        (twoColumnShuffleBoundaryChart S σ hs p).val =
      (minimalCellInclusion i₀ σ (p : OnePoint (Space (d+1) × heightChamber n σ))).val := by
  change compactTwoColumnAttaching S iL iR hL hR
    (OnePoint.some (twoColumnShuffleFace S σ hs p)) = _
  rw [compactTwoColumnAttaching_coe]
  change twoColumnAttaching S ((horizontalHeight d p.1,p.2.val),0) = _
  have ht : Function.Injective p.2.val := heightChamber_injective p.2.property
  rw [twoColumnAttaching_zero_vertical S i₀ _ ⟨p.2.val,ht⟩]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rfl

private theorem twoColumnAmbient_eq_verticalPoint {d n : ℕ}
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (p : TwoColumnAmbientParameters d n) (u : Space (d+1)) (t : Fin n → ℝ)
    (h : twoColumnAmbient S p =
      fun i => (horizontalHeight (d+1)).symm (u,t i)) :
    p = ((horizontalHeight d u,t),0) := by
  have hpair (i : Fin n) :
      ((horizontalHeight d).symm
        (p.1.1.1,if i ∈ S then p.1.1.2 else p.1.1.2+p.2),p.1.2 i) =
        (u,t i) := by
    have hi := congrArg (horizontalHeight (d+1)) (congrFun h i)
    simpa only [twoColumnAmbient,ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply] using hi
  have hbaseL : (p.1.1.1,p.1.1.2) = horizontalHeight d u := by
    simpa only [hL,if_pos,ContinuousLinearEquiv.apply_symm_apply] using
      congrArg (horizontalHeight d) (congrArg Prod.fst (hpair iL))
  have hbaseR : (p.1.1.1,p.1.1.2+p.2) = horizontalHeight d u := by
    simpa only [hR,if_neg,ContinuousLinearEquiv.apply_symm_apply] using
      congrArg (horizontalHeight d) (congrArg Prod.fst (hpair iR))
  have hgap : p.2 = 0 := by
    have hL' := congrArg Prod.snd hbaseL
    have hR' := congrArg Prod.snd hbaseR
    linarith
  have hheight : p.1.2 = t := funext fun i =>
    congrArg Prod.snd (hpair i)
  apply Prod.ext
  · apply Prod.ext
    · exact hbaseL
    · exact hheight
  · exact hgap

/-- Every preimage of a finite point in a minimal cell is exactly its
collision-free shuffle-chart point. In particular, the full characteristic
boundary has no additional preimages over the interior of a minimal cell. -/
theorem compactTwoColumnAttaching_fiber_minimalCell {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (σ : Equiv.Perm (Fin n)) (hs : IsColumnShuffle S σ) (i₀ : Fin n)
    (x : Space (d+1) × heightChamber n σ)
    (z : OnePoint (closedTwoColumnDomain (d := d) S)) :
    compactTwoColumnAttaching S iL iR hL hR z =
        (minimalCellInclusion i₀ σ (x : OnePoint
          (Space (d+1) × heightChamber n σ))).val
      ↔ z = (twoColumnShuffleBoundaryChart S σ hs x).val := by
  induction z using OnePoint.rec with
  | infty =>
      simp [compactTwoColumnAttaching_infty,minimalCellInclusion,
        compactifiedVerticalCell,twoColumnShuffleBoundaryChart]
  | coe q =>
      constructor
      · intro h
        have hcollapse :
            configurationCollapse (d+2) n (twoColumnAmbient S q.val) =
              ((verticalCellEmbedding i₀ σ x :
                Configuration (d+2) n) : OnePoint (Configuration (d+2) n)) := by
          simpa [compactTwoColumnAttaching_coe,compactifiedConfigurationCollapse_coe,
            twoColumnAttaching,minimalCellInclusion,compactifiedVerticalCell] using h
        by_cases hinj : Function.Injective (twoColumnAmbient S q.val)
        · have hsome :
              ((⟨twoColumnAmbient S q.val,hinj⟩ : Configuration (d+2) n) :
                OnePoint (Configuration (d+2) n)) =
                ((verticalCellEmbedding i₀ σ x :
                  Configuration (d+2) n) : OnePoint (Configuration (d+2) n)) := by
              rw [← configurationCollapse_injective (d := d+2) (n := n)
                (twoColumnAmbient S q.val) hinj]
              exact hcollapse
          have hconfig :
              (⟨twoColumnAmbient S q.val,hinj⟩ : Configuration (d+2) n) =
                verticalCellEmbedding i₀ σ x := Option.some.inj hsome
          have hambient :
              twoColumnAmbient S q.val =
                fun i => (horizontalHeight (d+1)).symm (x.1,x.2.val i) := by
            funext i
            have hi := congrFun (congrArg Subtype.val hconfig) i
            simpa [verticalCellEmbedding,verticalCellCoordinates] using hi
          have hval := twoColumnAmbient_eq_verticalPoint S iL iR hL hR
            q.val x.1 x.2.val hambient
          have hq : q = twoColumnShuffleFace S σ hs x := by
            apply Subtype.ext
            exact hval
          simpa [twoColumnShuffleBoundaryChart] using congrArg
            (fun a : closedTwoColumnDomain (d := d) S =>
              (a : OnePoint (closedTwoColumnDomain (d := d) S))) hq
        · have hbad : (∞ : OnePoint (Configuration (d+2) n)) =
              ((verticalCellEmbedding i₀ σ x :
                Configuration (d+2) n) : OnePoint (Configuration (d+2) n)) := by
              rw [configurationCollapse_collision _ hinj] at hcollapse
              exact hcollapse
          exact False.elim ((OnePoint.infty_ne_coe _) hbad)
      · intro hz
        rw [hz]
        exact twoColumnShuffleBoundaryChart_attaching S σ hs iL iR hL hR i₀ x

/-- The same singleton-fiber computation for the actual boundary map into
the next compactified Fuks level. -/
theorem twoColumnCharacteristicBoundaryMap_fiber_minimalCell {d n : ℕ}
    [NeZero n] (S : Finset (Fin n)) (iL iR : Fin n)
    (hL : iL ∈ S) (hR : iR ∉ S) (σ : Equiv.Perm (Fin n))
    (hs : IsColumnShuffle S σ) (i₀ : Fin n)
    (x : Space (d+1) × heightChamber n σ)
    (z : twoColumnCharacteristicBoundary (d := d) S) :
    twoColumnCharacteristicBoundaryMap S iL iR hL hR z =
      ⟨(minimalCellInclusion i₀ σ (x : OnePoint
        (Space (d+1) × heightChamber n σ))).val, by
        rw [compactifiedFuksLevel_minimal]
        exact (minimalCellInclusion i₀ σ
          (x : OnePoint (Space (d+1) × heightChamber n σ))).property⟩
      ↔ z = twoColumnShuffleBoundaryChart S σ hs x := by
  constructor
  · intro h
    apply Subtype.ext
    have hraw := congrArg Subtype.val h
    exact (compactTwoColumnAttaching_fiber_minimalCell S iL iR hL hR
      σ hs i₀ x z.val).mp hraw
  · intro hz
    subst z
    apply Subtype.ext
    exact twoColumnShuffleBoundaryChart_attaching S σ hs iL iR hL hR i₀ x

end NRR.PrimePowerTopology
