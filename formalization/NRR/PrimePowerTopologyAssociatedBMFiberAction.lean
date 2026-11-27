import NRR.PrimePowerTopologyEulerThomInclusion
import NRR.PrimePowerTopologyFiberDegree

/-! The reduced fiber permutation acts on bottom ordinary homology of
the genuine associated total space by its computed determinant character.
The closed normal locus generates that degree, so the computation reduces
to the actual Euclidean chambers of the normal locus. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

private def normalVectorChart (d n : ℕ) [NeZero n] :
    (Space d × ReducedValues (d+1) n) ≃L[ℝ] Space (d*n) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_reducedValues,
      finrank_euclideanSpace_fin]
    simp only [Nat.add_sub_cancel]
    simp only [Nat.mul_succ,Nat.add_comm])

private def normalKernelVertical : VerticalKernelConfiguration d n ≃ₜ verticalSet d n where
  toFun u := ⟨⟨u.val.val,u.property⟩,(canonicalSection_zero_iff _).mp u.val.property⟩
  invFun x := ⟨⟨x.val.val,(canonicalSection_zero_iff _).mpr x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

private def normalShuffle :
    ((Space d × LineConfiguration n) × ReducedValues (d+1) n) ≃ₜ
      (Space d × ReducedValues (d+1) n) × LineConfiguration n where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd
  continuous_invFun := (continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd

/-- An unsorted chart is useful for fiber-only permutations: the height
order is retained and all normal coordinates enter the horizontal factor. -/
private def normalUnsortedChart (i₀ : Fin n) :
    VerticalAssociated d n ≃ₜ verticalSet (d*n) n :=
  (((normalKernelVertical.trans (verticalCoordinates i₀)).prodCongr (Homeomorph.refl _)).trans
    normalShuffle).trans (((normalVectorChart d n).toHomeomorph.prodCongr (Homeomorph.refl _)).trans
      (verticalCoordinates i₀).symm)

private def normalUnsortedSkeleton (i₀ : Fin n) :
    OnePoint (VerticalAssociated d n) ≃ₜ minimalSkeleton (d*n) n :=
  (normalUnsortedChart i₀).onePointCongr.trans (verticalOnePointSkeleton (d*n) n)

/-- Change the common horizontal coordinate, retaining each labelled height. -/
private def verticalHorizontalHomeomorph {a : ℕ} (i₀ : Fin n) (e : Space a ≃ₜ Space a) :
    verticalSet a n ≃ₜ verticalSet a n :=
  (verticalCoordinates i₀).trans ((e.prodCongr (Homeomorph.refl _)).trans
    (verticalCoordinates i₀).symm)

private def minimalHorizontalHomeomorph {a : ℕ} (i₀ : Fin n) (e : Space a ≃ₜ Space a) :
    minimalSkeleton a n ≃ₜ minimalSkeleton a n :=
  (verticalOnePointSkeleton a n).symm.trans
    ((verticalHorizontalHomeomorph i₀ e).onePointCongr.trans (verticalOnePointSkeleton a n))

private def cellIntoVertical {a : ℕ} (i₀ : Fin n) (σ : ConfigurationGroup n)
    (p : Space a × heightChamber n σ) : verticalSet a n :=
  ⟨verticalCellEmbedding i₀ σ p,((verticalCellCoordinates i₀ σ).symm p).property.1⟩

omit [NeZero n] in
private theorem minimalCell_eq_verticalSkeleton {a : ℕ} (i₀ : Fin n)
    (σ : ConfigurationGroup n) (z : OnePoint (Space a × heightChamber n σ)) :
    minimalCellInclusion i₀ σ z = verticalOnePointSkeleton a n
      (OnePoint.map (cellIntoVertical i₀ σ) z) := by
  induction z using OnePoint.rec <;> rfl

omit [NeZero n] in
private theorem minimalCell_horizontal_square {a : ℕ} (i₀ : Fin n)
    (e : Space a ≃ₜ Space a) (σ : ConfigurationGroup n) :
    minimalCellInclusionMap (d := a) i₀ σ ≫
        TopCat.ofHom ⟨minimalHorizontalHomeomorph i₀ e,
          (minimalHorizontalHomeomorph i₀ e).continuous⟩ =
      TopCat.ofHom ⟨(e.prodCongr (Homeomorph.refl (heightChamber n σ))).onePointCongr,
        (e.prodCongr (Homeomorph.refl (heightChamber n σ))).onePointCongr.continuous⟩ ≫
          minimalCellInclusionMap (d := a) i₀ σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change minimalHorizontalHomeomorph i₀ e (minimalCellInclusion i₀ σ z) =
    minimalCellInclusion i₀ σ
      ((e.prodCongr (Homeomorph.refl (heightChamber n σ))).onePointCongr z)
  simp only [minimalCell_eq_verticalSkeleton,minimalHorizontalHomeomorph,
    Homeomorph.trans_apply,Homeomorph.symm_apply_apply]
  apply congrArg (verticalOnePointSkeleton a n)
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p =>
    change (((verticalHorizontalHomeomorph i₀ e) (cellIntoVertical i₀ σ p)) :
      OnePoint (verticalSet a n)) =
        ((cellIntoVertical i₀ σ (e p.1,p.2)) : OnePoint (verticalSet a n))
    apply congrArg OnePoint.some
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [cellIntoVertical,verticalCellEmbedding,verticalCellCoordinates,
      verticalHorizontalHomeomorph,verticalCoordinates]

private def normalHorizontalLinear (g : ConfigurationGroup n) :
    Space (d*n) ≃ₗ[ℝ] Space (d*n) :=
  (normalVectorChart d n).symm.toLinearEquiv.trans
    (((LinearEquiv.refl ℝ (Space d)).prodCongr (relabelValues g).toLinearEquiv).trans
      (normalVectorChart d n).toLinearEquiv)

private def normalCellVectorChart :
    (Space (d*n) × (Fin n → ℝ)) ≃ₗ[ℝ]
      (Space d × (Fin n → ℝ)) × ReducedValues (d+1) n where
  toFun p := ((((normalVectorChart d n).symm p.1).1,p.2),
    ((normalVectorChart d n).symm p.1).2)
  invFun p := (normalVectorChart d n (p.1.1,p.2),p.1.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private theorem normalHorizontal_cell_character (R : Type) [Ring R]
    (g σ : ConfigurationGroup n) :
    HabsMap R (d*n+n) (TopCat.ofHom
      ⟨((normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph.prodCongr
          (Homeomorph.refl (heightChamber n σ))).onePointCongr,
        ((normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph.prodCongr
          (Homeomorph.refl (heightChamber n σ))).onePointCongr.continuous⟩) =
      (Equiv.Perm.sign g : ℤ)^d • 𝟙 _ := by
  let V := Space (d*n) × (Fin n → ℝ)
  let e := ((Homeomorph.refl (Space (d*n))).prodCongr
    (heightChamberEuclidean n σ)).onePointCongr
  let E := HabsIsoOfHomotopyEquiv R (d*n+n) e.toHomotopyEquiv
  have hchar : HabsMap R (d*n+n)
      (fiberLinearOnePointMap ((normalHorizontalLinear (d := d) g).prodCongr
        (LinearEquiv.refl ℝ (Fin n → ℝ)))) = (Equiv.Perm.sign g : ℤ)^d • 𝟙 _ := by
    have hdim : d*n+n = Module.finrank ℝ V := by simp [V,Module.finrank_prod]
    rw [hdim]
    apply fiberLinearOnePointMap_conjugate R _ ((Equiv.Perm.sign g : ℤ)^d) _
      ((LinearEquiv.refl ℝ (Space d × (Fin n → ℝ))).prodCongr
        (relabelValues g).toLinearEquiv) normalCellVectorChart
    · intro p
      simp [normalCellVectorChart, normalHorizontalLinear]
    · rw [normalCellVectorChart.finrank_eq]
      exact reducedPermutationOnePointMap_top_finrank R (Space d × (Fin n → ℝ)) g
  apply (cancel_mono E.hom).mp
  change HabsMap R _ _ ≫ HabsMap R _ (TopCat.ofHom e.toHomotopyEquiv.toFun) = _
  rw [← HabsMap_comp]
  have hs : TopCat.ofHom
      ⟨((normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph.prodCongr
          (Homeomorph.refl (heightChamber n σ))).onePointCongr,
        ((normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph.prodCongr
          (Homeomorph.refl (heightChamber n σ))).onePointCongr.continuous⟩ ≫
        TopCat.ofHom e.toHomotopyEquiv.toFun =
      TopCat.ofHom e.toHomotopyEquiv.toFun ≫
        fiberLinearOnePointMap ((normalHorizontalLinear (d := d) g).prodCongr
          (LinearEquiv.refl ℝ (Fin n → ℝ))) := by
    ext z
    induction z using OnePoint.rec <;> rfl
  rw [hs,HabsMap_comp,hchar]
  simp [E,HabsIsoOfHomotopyEquiv]

private theorem minimalHorizontal_normal_character (R : Type) [Ring R]
    (i₀ : Fin n) (g : ConfigurationGroup n) :
    HabsMap R (d*n+n) (TopCat.ofHom
      ⟨minimalHorizontalHomeomorph i₀
          (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph,
        (minimalHorizontalHomeomorph i₀
          (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph).continuous⟩) =
      (Equiv.Perm.sign g : ℤ)^d • 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply (minimalFundamentalBasis R (d := d*n) i₀ (by have := NeZero.pos n; omega)).ext
  intro σ
  simp only [minimalFundamentalBasis_apply]
  change _ = (Equiv.Perm.sign g : ℤ)^d •
    minimalFundamentalClass R i₀ σ (by have := NeZero.pos n; omega)
  have h := congrArg (fun f =>
      ((minimalCellTopHomologyIso R (d*n) n σ (by have := NeZero.pos n; omega)).inv ≫ f)
        (1 : R))
    (congrArg (HabsMap R (d*n+n))
      (minimalCell_horizontal_square i₀
        (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph σ))
  simpa only [HabsMap_comp,normalHorizontal_cell_character,ConcreteCategory.comp_apply,
    ModuleCat.hom_smul,LinearMap.smul_apply,ModuleCat.hom_id,LinearMap.id_apply,
    map_zsmul,
    minimalFundamentalBasis_apply,minimalFundamentalClass,minimalCellGenerator] using h

/-- Fiber-only relabelling, with the actual configuration held fixed. -/
def associatedBMFiberHomeomorph (g : ConfigurationGroup n) :
    AssociatedCover (d+1) n ≃ₜ AssociatedCover (d+1) n :=
  (Homeomorph.refl _).prodCongr (relabelValues g).toHomeomorph

private def normalFiberHomeomorph (g : ConfigurationGroup n) :
    VerticalAssociated d n ≃ₜ VerticalAssociated d n :=
  (Homeomorph.refl _).prodCongr (relabelValues g).toHomeomorph

private theorem normalFiber_unsorted_square (i₀ : Fin n) (g : ConfigurationGroup n) :
    TopCat.ofHom ⟨(normalFiberHomeomorph (d := d) g).onePointCongr,
      (normalFiberHomeomorph (d := d) g).onePointCongr.continuous⟩ ≫
        TopCat.ofHom ⟨normalUnsortedSkeleton i₀,(normalUnsortedSkeleton i₀).continuous⟩ =
      TopCat.ofHom ⟨normalUnsortedSkeleton i₀,(normalUnsortedSkeleton i₀).continuous⟩ ≫
        TopCat.ofHom ⟨minimalHorizontalHomeomorph i₀
            (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph,
          (minimalHorizontalHomeomorph i₀
            (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph).continuous⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change normalUnsortedSkeleton i₀ ((normalFiberHomeomorph (d := d) g).onePointCongr z) =
    minimalHorizontalHomeomorph i₀
      (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph
      (normalUnsortedSkeleton i₀ z)
  simp only [normalUnsortedSkeleton,minimalHorizontalHomeomorph,Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  apply congrArg (verticalOnePointSkeleton (d*n) n)
  induction z using OnePoint.rec with
  | infty => rfl
  | coe p =>
    change ((normalUnsortedChart i₀ (normalFiberHomeomorph (d := d) g p)) :
      OnePoint (verticalSet (d*n) n)) =
      ((verticalHorizontalHomeomorph i₀
        (normalHorizontalLinear (d := d) g).toContinuousLinearEquiv.toHomeomorph
          (normalUnsortedChart i₀ p)) : OnePoint (verticalSet (d*n) n))
    apply congrArg OnePoint.some
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [normalUnsortedChart,normalShuffle,
      normalFiberHomeomorph,normalKernelVertical,normalHorizontalLinear,
      verticalHorizontalHomeomorph,verticalCoordinates]
    exact ⟨⟨rfl,rfl⟩,rfl⟩

/-- On the lowest nonzero ordinary homology group of the actual
associated total space, fiber permutation contributes precisely `sign^d`. -/
theorem associatedBMFiberMap_bottom (R : Type) [CommRing R] (hn : 2 ≤ n)
    (g : ConfigurationGroup n) :
    HabsMap R ((d+1)*n) (TopCat.ofHom
      ⟨(associatedBMFiberHomeomorph (d := d) g).onePointCongr,
        (associatedBMFiberHomeomorph (d := d) g).onePointCongr.continuous⟩) =
      (Equiv.Perm.sign g : ℤ)^d • 𝟙 _ := by
  let i₀ : Fin n := ⟨0,NeZero.pos n⟩
  let e := normalUnsortedSkeleton (d := d) i₀
  let E := HabsIsoOfHomotopyEquiv R ((d+1)*n) e.toHomotopyEquiv
  have hnormal : HabsMap R ((d+1)*n) (TopCat.ofHom
      ⟨(normalFiberHomeomorph (d := d) g).onePointCongr,
        (normalFiberHomeomorph (d := d) g).onePointCongr.continuous⟩) =
        (Equiv.Perm.sign g : ℤ)^d • 𝟙 _ := by
    apply (cancel_mono E.hom).mp
    change HabsMap R _ _ ≫ HabsMap R _ (TopCat.ofHom e.toHomotopyEquiv.toFun) = _
    rw [← HabsMap_comp]
    change HabsMap R ((d+1)*n)
      (TopCat.ofHom ⟨(normalFiberHomeomorph (d := d) g).onePointCongr,
        (normalFiberHomeomorph (d := d) g).onePointCongr.continuous⟩ ≫
          TopCat.ofHom ⟨normalUnsortedSkeleton i₀,(normalUnsortedSkeleton i₀).continuous⟩) = _
    rw [normalFiber_unsorted_square,HabsMap_comp]
    have hchar := minimalHorizontal_normal_character R (d := d) i₀ g
    have hdegree : d*n+n = (d+1)*n := by ring
    rw [hdegree] at hchar
    rw [hchar]
    simp [E,e,HabsIsoOfHomotopyEquiv]
    rfl
  let i := TopCat.ofHom (canonicalEulerThomIncludeCompact (d := d) (n := n))
  letI : Epi (HabsMap R ((d+1)*n) i) := epi_HabsMap_verticalNormalInclude R hn
  apply (cancel_epi (HabsMap R ((d+1)*n) i)).mp
  rw [← HabsMap_comp]
  have hs : i ≫ TopCat.ofHom
      ⟨(associatedBMFiberHomeomorph (d := d) g).onePointCongr,
        (associatedBMFiberHomeomorph (d := d) g).onePointCongr.continuous⟩ =
      TopCat.ofHom ⟨(normalFiberHomeomorph (d := d) g).onePointCongr,
        (normalFiberHomeomorph (d := d) g).onePointCongr.continuous⟩ ≫ i := by
    ext z
    induction z using OnePoint.rec <;> rfl
  rw [hs,HabsMap_comp,hnormal]
  simp

end NRR.PrimePowerTopology
