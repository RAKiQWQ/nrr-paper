import NRR.PrimePowerTopologyRelativePairOrbitBasisAssociatedBM
import NRR.SingularHomologyGoodPair

/-! Radial expansion in the fiber contracts the compactified complement
of the zero section to infinity. This identifies the point-relative
homology of the total space with the actual relative Euler target. -/

noncomputable section
open Set Topology Filter CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology
variable {d n : ℕ}

private def expandFiber (t : unitInterval) (z : OnePoint (AssociatedCover d n)) :
    OnePoint (AssociatedCover d n) :=
  if t = 0 then ∞ else OnePoint.map (fun p => (p.1,(t : ℝ)⁻¹ • p.2)) z

private theorem expandFiber_continuousAt_finite (t : unitInterval) (ht : t ≠ 0)
    (p : AssociatedCover d n) :
    ContinuousAt (fun a : unitInterval × OnePoint (AssociatedCover d n) =>
      expandFiber a.1 a.2) (t,(p : OnePoint _)) := by
  have h : IsOpenEmbedding (Prod.map (id : unitInterval → unitInterval)
      ((↑) : AssociatedCover d n → OnePoint (AssociatedCover d n))) :=
    IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
  apply (h.continuousAt_iff (g := fun a => expandFiber a.1 a.2) (x := (t,p))).mp
  have ht' : (t : ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
  have hc : ContinuousAt (fun a : unitInterval × AssociatedCover d n =>
      (((a.2.1,(a.1 : ℝ)⁻¹ • a.2.2) : AssociatedCover d n) : OnePoint (AssociatedCover d n))) (t,p) :=
    OnePoint.continuous_coe.continuousAt.comp
      (continuous_snd.fst.continuousAt.prodMk
        (((continuous_subtype_val.comp continuous_fst).continuousAt (x := (t,p)) |>.inv₀ ht').smul
          continuous_snd.snd.continuousAt))
  apply hc.congr
  have hne : ∀ᶠ a : unitInterval × AssociatedCover d n in 𝓝 (t,p), a.1 ≠ 0 :=
    (isClosed_singleton.isOpen_compl.preimage continuous_fst).mem_nhds ht
  filter_upwards [hne] with a ha
  simp [expandFiber,ha,Function.comp_def]

private def complementExpansion (a : unitInterval × associatedBMComplement d n) :
    OnePoint (AssociatedCover d n) := expandFiber a.1 a.2.val

private theorem continuous_complementExpansion :
    Continuous (complementExpansion (d := d) (n := n)) := by
  classical
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,⟨z,hz⟩⟩
  by_cases hinf : expandFiber t z = ∞
  · change Tendsto complementExpansion _ (𝓝 (expandFiber t z))
    rw [hinf]
    apply OnePoint.le_nhds_infty.mpr
    intro K _ hK
    let shrink : unitInterval × AssociatedCover d n →
        unitInterval × OnePoint (AssociatedCover d n) :=
      fun a => (a.1,((a.2.1,(a.1 : ℝ) • a.2.2) : AssociatedCover d n))
    have hc : Continuous shrink := continuous_fst.prodMk (OnePoint.continuous_coe.comp
      (continuous_snd.fst.prodMk ((continuous_subtype_val.comp continuous_fst).smul
        continuous_snd.snd)))
    let B := shrink '' (Set.univ ×ˢ K)
    have hB : IsClosed B := ((isCompact_univ.prod hK).image hc).isClosed
    have hout : (t,z) ∉ B := by
      rintro ⟨⟨s,⟨x,v⟩⟩,_,he⟩
      cases he
      by_cases hs : s = 0
      · subst s
        exact ((associatedBMComplement_coe_iff _).mp hz) (by simp)
      · simpa [expandFiber, hs, shrink] using hinf
    let incl : unitInterval × associatedBMComplement d n →
        unitInterval × OnePoint (AssociatedCover d n) := fun a => (a.1,a.2.val)
    have hinc : Continuous incl := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hgood : incl ⁻¹' Bᶜ ∈ 𝓝 (t,(⟨z,hz⟩ : associatedBMComplement d n)) :=
      (hB.isOpen_compl.preimage hinc).mem_nhds hout
    apply Filter.mem_of_superset hgood
    rintro ⟨s,⟨w,hw⟩⟩ h
    by_cases hs : s = 0
    · exact Or.inr (by simp [complementExpansion,expandFiber,hs])
    · induction w using OnePoint.rec with
      | infty => exact Or.inr (by simp [complementExpansion,expandFiber,hs])
      | coe p =>
        have hs' : (s : ℝ) ≠ 0 := fun e => hs (Subtype.ext e)
        refine Or.inl ⟨(p.1,(s : ℝ)⁻¹ • p.2),?_,by simp [complementExpansion,expandFiber,hs]⟩
        intro hp
        apply h
        refine ⟨(s,(p.1,(s : ℝ)⁻¹ • p.2)),⟨mem_univ _,hp⟩,?_⟩
        simp [shrink,incl,smul_smul,hs']
  · have ht : t ≠ 0 := by rintro rfl; simp [expandFiber] at hinf
    induction z using OnePoint.rec with
    | infty => simp [expandFiber, ht] at hinf
    | coe p =>
      let j : unitInterval × associatedBMComplement d n →
          unitInterval × OnePoint (AssociatedCover d n) := fun a => (a.1,a.2.val)
      have hj : Continuous j :=
        continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
      exact (expandFiber_continuousAt_finite t ht p).comp (f := j)
        (hj.continuousAt (x := (t,⟨_,hz⟩)))

private theorem complementExpansion_mem (a : unitInterval × associatedBMComplement d n) :
    complementExpansion a ∈ associatedBMComplement d n := by
    obtain ⟨t,⟨z,hz⟩⟩ := a
    by_cases ht : t = 0
    · simpa [complementExpansion,expandFiber,ht] using associatedBMComplement_infty d n
    · induction z using OnePoint.rec with
      | infty => simpa [complementExpansion,expandFiber,ht] using associatedBMComplement_infty d n
      | coe p =>
        have ht' : (t : ℝ) ≠ 0 := fun e => ht (Subtype.ext e)
        simp only [complementExpansion,expandFiber,if_neg ht,OnePoint.map_some]
        exact (associatedBMComplement_coe_iff (p.1,(t : ℝ)⁻¹ • p.2)).mpr
          (smul_ne_zero (inv_ne_zero ht') ((associatedBMComplement_coe_iff p).mp hz))

/-- The contraction fixes infinity at every intermediate time. -/
def associatedBMComplementContraction :
    (ContinuousMap.const (associatedBMComplement d n)
      (⟨∞,associatedBMComplement_infty d n⟩ : associatedBMComplement d n)).Homotopy
      (ContinuousMap.id (associatedBMComplement d n)) where
  toFun a := ⟨complementExpansion a,complementExpansion_mem a⟩
  continuous_toFun := continuous_complementExpansion.subtype_mk _
  map_zero_left := fun _ => Subtype.ext (by simp [complementExpansion,expandFiber])
  map_one_left := by
    rintro ⟨z,hz⟩
    apply Subtype.ext
    change expandFiber 1 z = z
    induction z using OnePoint.rec <;> simp [expandFiber]

theorem associatedBMComplementContraction_equivariant (σ : ConfigurationGroup n)
    (t : unitInterval) (z : associatedBMComplement d n) :
    associatedBMComplementContraction (t,associatedBMComplementRelabel σ z) =
      associatedBMComplementRelabel σ (associatedBMComplementContraction (t,z)) := by
  obtain ⟨z,hz⟩ := z
  apply Subtype.ext
  change expandFiber t (associatedBMCoverRelabel σ z) =
    associatedBMCoverRelabel σ (expandFiber t z)
  by_cases ht : t = 0
  · simp [expandFiber, ht, associatedBMCoverRelabel]
  · induction z using OnePoint.rec with
    | infty => simp [expandFiber,ht,associatedBMCoverRelabel]
    | coe p =>
      change expandFiber t ((σ • p : AssociatedCover d n) : OnePoint (AssociatedCover d n)) =
        associatedBMCoverRelabel σ (expandFiber t (p : OnePoint (AssociatedCover d n)))
      simp only [expandFiber,if_neg ht,OnePoint.map_some]
      change (((σ • p.1,(t : ℝ)⁻¹ • (σ • p.2)) : AssociatedCover d n) : OnePoint (AssociatedCover d n)) =
        (((σ • p.1,σ • ((t : ℝ)⁻¹ • p.2)) : AssociatedCover d n) : OnePoint (AssociatedCover d n))
      rw [values_smul_real_smul]

def associatedBMPointToComplement :
    TopCat.of ({∞} : Set (OnePoint (AssociatedCover d n))) ⟶ TopCat.of (associatedBMComplement d n) :=
  TopCat.ofHom (ContinuousMap.const _ ⟨∞,associatedBMComplement_infty d n⟩)

theorem associatedBMPointToComplement_square :
    associatedBMCoverInfinityIncl d n ≫ 𝟙 _ =
      associatedBMPointToComplement ≫ associatedBMTargetIncl d n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact fun x => x.property

/-- The comparison uses the identity map of the total compactified space,
in every degree and over any ring. -/
theorem isIso_associatedBMPointToComplement (R : Type) [Ring R] (q : ℕ) :
    IsIso (HrelMap R q (associatedBMCoverInfinityIncl d n) (associatedBMTargetIncl d n)
      associatedBMPointToComplement_square) := by
  apply isIso_HrelMap_of_homologyEquivalences
  · intro k
    let e : ContinuousMap.HomotopyEquiv ({∞} : Set (OnePoint (AssociatedCover d n)))
        (associatedBMComplement d n) :=
      { toFun := associatedBMPointToComplement.hom
        invFun := ContinuousMap.const _ ⟨∞,rfl⟩
        left_inv := by
          have h : (ContinuousMap.const _ (⟨∞,rfl⟩ : ({∞} : Set (OnePoint (AssociatedCover d n))))).comp
              associatedBMPointToComplement.hom = ContinuousMap.id _ := Subsingleton.elim _ _
          rw [h]
        right_inv := ⟨associatedBMComplementContraction⟩ }
    exact (HabsIsoOfHomotopyEquiv R k e).isIso_hom
  · intro k
    rw [HabsMap_id]
    infer_instance

end NRR.PrimePowerTopology
