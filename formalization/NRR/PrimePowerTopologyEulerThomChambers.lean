import NRR.PrimePowerTopologyEulerThomVertical
import NRR.PrimePowerTopologyTwistedFuksBM

/-! Sorting the distinct heights trivializes the permutation action on the
normal coordinates over each ordering chamber. Absorbing those coordinates
into the common horizontal coordinate identifies the compactified normal
model equivariantly with an ordinary minimal Fuks skeleton of dimension dn+n. -/

noncomputable section
open Set Topology Filter CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology

namespace NRR.PrimePowerTopology
variable {d n : ℕ} [NeZero n]

private def kernelVertical : VerticalKernelConfiguration d n ≃ₜ verticalSet d n where
  toFun u := ⟨⟨u.val.val,u.property⟩,(canonicalSection_zero_iff _).mp u.val.property⟩
  invFun x := ⟨⟨x.val.val,(canonicalSection_zero_iff _).mpr x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

private def heightOrder (t : LineConfiguration n) : ConfigurationGroup n :=
  (exists_unique_heightChamber t).exists.choose

private theorem heightOrder_spec (t : LineConfiguration n) :
    t.val ∈ heightChamber n (heightOrder t) := (exists_unique_heightChamber t).exists.choose_spec

private theorem eventually_heightOrder_eq (t : LineConfiguration n) :
    ∀ᶠ s : LineConfiguration n in 𝓝 t, heightOrder s = heightOrder t := by
  filter_upwards [((isOpen_heightChamber n (heightOrder t)).preimage continuous_subtype_val).mem_nhds
    (heightOrder_spec t)] with s hs
  exact heightChamber_unique (heightOrder_spec s) hs

private def reindexHeight (σ : ConfigurationGroup n) (t : LineConfiguration n) :
    LineConfiguration n := ⟨fun i => t.val (σ.symm i),t.property.comp σ.symm.injective⟩

private theorem heightOrder_relabel (σ : ConfigurationGroup n) (t : LineConfiguration n) :
    heightOrder (reindexHeight σ t) = σ * heightOrder t := by
  apply heightChamber_unique (heightOrder_spec _)
  intro i j hij
  simpa only [reindexHeight,Equiv.Perm.mul_apply,Equiv.symm_apply_apply] using
    (show t.val (heightOrder t i) < t.val (heightOrder t j) from heightOrder_spec t hij)

private def recordNormal : (Space d × LineConfiguration n) × ReducedValues (d+1) n ≃ₜ
    (Space d × ReducedValues (d+1) n) × LineConfiguration n where
  toFun x := ((x.1.1,(heightOrder x.1.2)⁻¹ • x.2),x.1.2)
  invFun y := ((y.1.1,y.2),heightOrder y.2 • y.1.2)
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := by
    refine (continuous_fst.fst.prodMk ?_).prodMk continuous_fst.snd
    apply continuous_iff_continuousAt.mpr
    intro x
    apply ((continuous_const_smul (heightOrder x.1.2)⁻¹).comp continuous_snd).continuousAt.congr
    filter_upwards [(continuous_fst.snd.continuousAt (x := x)).eventually (eventually_heightOrder_eq x.1.2)] with y hy
    simp only [Function.comp_apply,hy]
  continuous_invFun := by
    refine (continuous_fst.fst.prodMk continuous_snd).prodMk ?_
    apply continuous_iff_continuousAt.mpr
    intro y
    apply ((continuous_const_smul (heightOrder y.2)).comp continuous_fst.snd).continuousAt.congr
    filter_upwards [(continuous_snd.continuousAt (x := y)).eventually (eventually_heightOrder_eq y.2)] with x hx
    simp only [Function.comp_apply,hx]

private def normalParameter : (Space d × ReducedValues (d+1) n) ≃L[ℝ] Space (d*n) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    rw [Module.finrank_prod,finrank_euclideanSpace_fin,finrank_reducedValues,finrank_euclideanSpace_fin]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_succ,Nat.add_comm])

/-- One chart for the entire normal model, including every height order. -/
def verticalAssociatedHigherStratum (i₀ : Fin n) :
    VerticalAssociated d n ≃ₜ verticalSet (d*n) n :=
  (((kernelVertical.trans (verticalCoordinates i₀)).prodCongr (Homeomorph.refl _)).trans
    recordNormal).trans (((normalParameter.toHomeomorph).prodCongr (Homeomorph.refl _)).trans
      (verticalCoordinates i₀).symm)

private def heightData (i₀ : Fin n) (u : VerticalKernelConfiguration d n) :=
  verticalCoordinates i₀ (kernelVertical u)

private theorem heightData_relabel (i₀ : Fin n) (g : ConfigurationGroup n)
    (u : VerticalKernelConfiguration d n) :
    heightData i₀ (canonicalEulerThomKernelRelabel g u) =
      ((heightData i₀ u).1,reindexHeight g (heightData i₀ u).2) := by
  apply Prod.ext
  · exact (kernelVertical u).property (g.symm i₀) i₀
  · rfl

theorem verticalAssociatedHigherStratum_relabel (i₀ : Fin n) (g : ConfigurationGroup n)
    (p : VerticalAssociated d n) :
    (verticalAssociatedHigherStratum i₀ (canonicalEulerThomKernelRelabel g p.1,g • p.2)).val =
      g • (verticalAssociatedHigherStratum i₀ p).val := by
  apply Subtype.ext
  funext i
  let h := heightData i₀ p.1
  change (horizontalHeight (d*n)).symm
    (normalParameter ((heightData i₀ (canonicalEulerThomKernelRelabel g p.1)).1,
      (heightOrder (heightData i₀ (canonicalEulerThomKernelRelabel g p.1)).2)⁻¹ • (g • p.2)),
      (heightData i₀ (canonicalEulerThomKernelRelabel g p.1)).2.val i) =
    (horizontalHeight (d*n)).symm
      (normalParameter (h.1,(heightOrder h.2)⁻¹ • p.2), h.2.val (g.symm i))
  rw [heightData_relabel]
  simp only [heightOrder_relabel,mul_inv_rev,mul_smul,inv_smul_smul]
  rfl

/-- The compactification of the closed vertical locus is exactly the minimal skeleton. -/
def verticalOnePointSkeleton (D n : ℕ) :
    OnePoint (verticalSet D n) ≃ₜ minimalSkeleton D n := by
  let f : OnePoint (verticalSet D n) → OnePoint (Configuration (D+1) n) := OnePoint.map Subtype.val
  have hf : Continuous f := OnePoint.continuous_map continuous_subtype_val (by
    simp only [coclosedCompact_eq_cocompact]
    exact (isClosed_verticalSet D n).isClosedEmbedding_subtypeVal.tendsto_cocompact)
  have hr : range f = minimalSkeleton D n := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      induction w using OnePoint.rec with
      | infty => exact Or.inl rfl
      | coe w => exact Or.inr ⟨w.val,w.property,rfl⟩
    · rintro (rfl | ⟨x,hx,rfl⟩)
      · exact ⟨∞,rfl⟩
      · exact ⟨((⟨x,hx⟩ : verticalSet D n) : OnePoint (verticalSet D n)),rfl⟩
  exact ((hf.isClosedEmbedding (Option.map_injective Subtype.val_injective)).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr hr)

def verticalAssociatedMinimalLevel (i₀ : Fin n) :
    OnePoint (VerticalAssociated d n) ≃ₜ compactifiedFuksLevel (d*n) n (d*n) :=
  (verticalAssociatedHigherStratum i₀).onePointCongr.trans
    ((verticalOnePointSkeleton (d*n) n).trans (minimalLevelHomeomorph _ _))

theorem verticalAssociatedMinimalLevel_relabel (i₀ : Fin n) (g : ConfigurationGroup n)
    (z : OnePoint (VerticalAssociated d n)) :
    verticalAssociatedMinimalLevel i₀ (canonicalEulerThomRelabel g z) =
      compactifiedFuksRelabel g (verticalAssociatedMinimalLevel i₀ z) := by
  apply Subtype.ext
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p =>
    exact congrArg ((↑) : Configuration (d*n+1) n → OnePoint (Configuration (d*n+1) n))
      (verticalAssociatedHigherStratum_relabel i₀ g p)

end NRR.PrimePowerTopology
