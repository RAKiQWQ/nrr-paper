import NRR.PrimePowerTopologyTwistedFundamental

/-! The signed sum of actual staircase singular simplices is a relative
cycle whenever the boundary of the cube is in the relative subspace.
Internal faces cancel by an explicit adjacent-transposition involution. -/

noncomputable section
open CategoryTheory Limits Opposite Simplicial
open NRR.SingularHomology NRR.SingularHomology.SimplexGeometry

namespace NRR.PrimePowerTopology

abbrev StaircaseCube (m : ℕ) := Fin m → Set.Icc (0 : ℝ) 1

def staircaseCubeBoundary (m : ℕ) : Set (StaircaseCube m) :=
  {x | ∃ a, (x a).val = 0 ∨ (x a).val = 1}

theorem staircaseUnitCubeSimplex_precomp_eq {m k : ℕ}
    (π ρ : Equiv.Perm (Fin m)) (f : ⦋k⦌ ⟶ ⦋m⦌)
    (hthreshold : ∀ a t, ((π a).val < (f t).val) ↔ ((ρ a).val < (f t).val)) :
    (staircaseUnitCubeSimplex π).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ =
      (staircaseUnitCubeSimplex ρ).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ := by
  ext x a
  change staircaseCoordinate π a (SimplexCategory.toTopMap f x) =
    staircaseCoordinate ρ a (SimplexCategory.toTopMap f x)
  rw [staircaseCoordinate_toTopMap, staircaseCoordinate_toTopMap]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [hthreshold a t]

/-- A continuous image of one actual staircase simplex. -/
def staircaseMappedSimplex {m : ℕ} {X : TopCat.{0}} (c : C(StaircaseCube m,X))
    (π : Equiv.Perm (Fin m)) : (TopCat.toSSet.obj X).obj (op ⦋m⦌) :=
  (TopCat.toSSetObjEquiv X _).symm (c.comp (staircaseUnitCubeSimplex π))

theorem staircaseMappedSimplex_face_eq {q : ℕ} {X : TopCat.{0}}
    (c : C(StaircaseCube (q+1),X)) (π : Equiv.Perm (Fin (q+1)))
    (a b : Fin (q+1)) (hab : b.val = a.val+1) (i : Fin (q+2))
    (hi : i.val = b.val) :
    (TopCat.toSSet.obj X).δ i (staircaseMappedSimplex c (Equiv.swap a b * π)) =
      (TopCat.toSSet.obj X).δ i (staircaseMappedSimplex c π) := by
  apply (TopCat.toSSetObjEquiv X _).injective
  have hf : ∀ t : Fin (q+1), ((SimplexCategory.δ i) t).val ≠ b.val := by
    intro t ht
    have hn := Fin.succAbove_ne i t
    apply hn
    apply Fin.ext
    exact ht.trans hi.symm
  have hs := staircaseUnitCubeSimplex_precomp_eq (Equiv.swap a b * π) π
    (SimplexCategory.δ i) (fun j t =>
      staircaseAdjacentSwap_threshold π a b j hab ((SimplexCategory.δ i) t) (hf t))
  change (c.comp (staircaseUnitCubeSimplex (Equiv.swap a b * π))).comp
      ⟨SimplexCategory.toTopMap (SimplexCategory.δ i),
        SimplexCategory.continuous_toTopMap _⟩ =
    (c.comp (staircaseUnitCubeSimplex π)).comp
      ⟨SimplexCategory.toTopMap (SimplexCategory.δ i),
        SimplexCategory.continuous_toTopMap _⟩
  simpa only [ContinuousMap.comp_assoc] using congrArg (ContinuousMap.comp c) hs

theorem staircaseUnitCubeSimplex_first_face {q : ℕ}
    (π : Equiv.Perm (Fin (q+1))) (x : Simplex q) :
    staircaseUnitCubeSimplex π (SimplexCategory.toTopMap (SimplexCategory.δ 0) x)
      ∈ staircaseCubeBoundary (q+1) := by
  refine ⟨π.symm 0, Or.inr ?_⟩
  change staircaseCoordinate π (π.symm 0)
    (SimplexCategory.toTopMap (SimplexCategory.δ (0 : Fin (q+2))) x) = 1
  rw [staircaseCoordinate_toTopMap]
  have hv (t : Fin (q+1)) : (π (π.symm 0)).val <
      ((SimplexCategory.δ (0 : Fin (q+2))) t).val := by
    change (π (π.symm 0)).val < ((0 : Fin (q+2)).succAbove t).val
    simp
  simp only [hv, if_true]
  exact_mod_cast x.property

theorem staircaseUnitCubeSimplex_last_face {q : ℕ}
    (π : Equiv.Perm (Fin (q+1))) (x : Simplex q) :
    staircaseUnitCubeSimplex π
      (SimplexCategory.toTopMap (SimplexCategory.δ (Fin.last (q+1))) x)
        ∈ staircaseCubeBoundary (q+1) := by
  refine ⟨π.symm (Fin.last q), Or.inl ?_⟩
  change staircaseCoordinate π (π.symm (Fin.last q))
    (SimplexCategory.toTopMap (SimplexCategory.δ (Fin.last (q+1))) x) = 0
  rw [staircaseCoordinate_toTopMap]
  apply Finset.sum_eq_zero
  intro t ht
  have hv : ¬ (π (π.symm (Fin.last q))).val <
      ((SimplexCategory.δ (Fin.last (q+1))) t).val := by
    change ¬ (π (π.symm (Fin.last q))).val < ((Fin.last (q+1)).succAbove t).val
    simp only [Equiv.apply_symm_apply, Fin.val_last, Fin.succAbove_last,
      Fin.coe_castSucc]
    omega
  simp only [if_neg hv]

section Relative

variable (R : Type) [CommRing R] {X : TopCat.{0}} (A : Set X)

/-- The actual relative chain generator of one mapped cube chamber. -/
def staircaseRelativeGenerator {m : ℕ} (c : C(StaircaseCube m,X))
    (π : Equiv.Perm (Fin m)) :
    ModuleCat.of R R ⟶ (relComplex R (subIncl (Y := X) A)).X m :=
  simplexι R (staircaseMappedSimplex c π) ≫
    (relProj R (subIncl (Y := X) A)).f m

/-- The signed sum over every top staircase chamber, with its actual
singular-chain signs. -/
def staircaseRelativeChain {m : ℕ} (c : C(StaircaseCube m,X)) :
    ModuleCat.of R R ⟶ (relComplex R (subIncl (Y := X) A)).X m :=
  ∑ π : Equiv.Perm (Fin m), (Equiv.Perm.sign π : ℤ) •
    staircaseRelativeGenerator R A c π

theorem staircaseRelativeSimplex_zero {q : ℕ}
    (s : (TopCat.toSSet.obj X).obj (op ⦋q⦌))
    (hs : ∀ x, TopCat.toSSetObjEquiv X _ s x ∈ A) :
    simplexι R s ≫ (relProj R (subIncl (Y := X) A)).f q = 0 := by
  let t : C(Simplex q,A) :=
    ⟨fun x => ⟨TopCat.toSSetObjEquiv X _ s x, hs x⟩,
      (TopCat.toSSetObjEquiv X _ s).continuous.subtype_mk _⟩
  let st : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋q⦌) :=
    (TopCat.toSSetObjEquiv (TopCat.of A) (op ⦋q⦌)).symm t
  have he : (TopCat.toSSet.map (subIncl (Y := X) A)).app _ st = s := by
    apply (TopCat.toSSetObjEquiv X _).injective
    ext x
    rfl
  have hmap : simplexι R st ≫ (CsingMap R (subIncl (Y := X) A)).f q =
      simplexι R s := by
    change simplexι R st ≫ (simplicialChainMap R
      (TopCat.toSSet.map (subIncl (Y := X) A))).f q = _
    rw [simplexι_chainMap_f, he]
  rw [← hmap, Category.assoc]
  change simplexι R st ≫ ((CsingMap R (subIncl (Y := X) A)).f q ≫
    (cokernel.π (CsingMap R (subIncl (Y := X) A))).f q) = 0
  rw [← HomologicalComplex.comp_f, cokernel.condition,
    HomologicalComplex.zero_f, comp_zero]

/-- In each internal face degree, the sum cancels by the fixed-point-free
involution swapping the two consecutive coordinate ranks. -/
theorem staircaseRelative_internal_faces_cancel {q : ℕ}
    (c : C(StaircaseCube (q+1),X)) (i : Fin (q+2))
    (a b : Fin (q+1)) (hab : b.val = a.val+1) (hi : i.val = b.val) :
    (∑ π : Equiv.Perm (Fin (q+1)), (Equiv.Perm.sign π : ℤ) •
      (simplexι R ((TopCat.toSSet.obj X).δ i (staircaseMappedSimplex c π)) ≫
        (relProj R (subIncl (Y := X) A)).f q)) = 0 := by
  classical
  have hne : a ≠ b := by intro he; have := congrArg Fin.val he; omega
  apply Finset.sum_ninvolution (fun π => Equiv.swap a b * π)
  · intro π
    rw [staircaseAdjacentSwap_sign π a b hab,
      staircaseMappedSimplex_face_eq c π a b hab i hi]
    simp
  · intro π hπ he
    have hs : Equiv.swap a b = 1 := mul_right_cancel (he.trans (one_mul π).symm)
    have hv := congrArg (fun e : Equiv.Perm (Fin (q+1)) => e a) hs
    exact hne (by simpa using hv.symm)
  · intro π
    exact Finset.mem_univ _
  · intro π
    simp [← mul_assoc]

theorem staircaseRelative_faces_cancel {q : ℕ}
    (c : C(StaircaseCube (q+1),X))
    (hc : ∀ x ∈ staircaseCubeBoundary (q+1), c x ∈ A) (i : Fin (q+2)) :
    (∑ π : Equiv.Perm (Fin (q+1)), (Equiv.Perm.sign π : ℤ) •
      (simplexι R ((TopCat.toSSet.obj X).δ i (staircaseMappedSimplex c π)) ≫
        (relProj R (subIncl (Y := X) A)).f q)) = 0 := by
  classical
  by_cases hi0 : i = 0
  · subst i
    apply Finset.sum_eq_zero
    intro π hπ
    have hz := staircaseRelativeSimplex_zero R A
      ((TopCat.toSSet.obj X).δ (0 : Fin (q+2)) (staircaseMappedSimplex c π))
      (fun x => hc _ (staircaseUnitCubeSimplex_first_face π x))
    rw [hz, smul_zero]
  · by_cases hilast : i = Fin.last (q+1)
    · subst i
      apply Finset.sum_eq_zero
      intro π hπ
      have hz := staircaseRelativeSimplex_zero R A
        ((TopCat.toSSet.obj X).δ (Fin.last (q+1)) (staircaseMappedSimplex c π))
        (fun x => hc _ (staircaseUnitCubeSimplex_last_face π x))
      rw [hz, smul_zero]
    · have hil : i.val < q+1 := by
        have := i.isLt
        have hne : i.val ≠ q+1 := by intro he; exact hilast (Fin.ext he)
        omega
      have hip : 0 < i.val := by
        have hne : i.val ≠ 0 := by intro he; exact hi0 (Fin.ext he)
        omega
      exact staircaseRelative_internal_faces_cancel R A c i
        ⟨i.val-1, by omega⟩ ⟨i.val, hil⟩ (by simp; omega) rfl

theorem staircaseRelativeGenerator_d {q : ℕ}
    (c : C(StaircaseCube (q+1),X)) (π : Equiv.Perm (Fin (q+1))) :
    staircaseRelativeGenerator R A c π ≫
      (relComplex R (subIncl (Y := X) A)).d (q+1) q =
    ∑ i : Fin (q+2), (-1 : ℤ)^i.val •
      (simplexι R ((TopCat.toSSet.obj X).δ i (staircaseMappedSimplex c π)) ≫
        (relProj R (subIncl (Y := X) A)).f q) := by
  unfold staircaseRelativeGenerator
  rw [Category.assoc, (relProj R (subIncl (Y := X) A)).comm (q+1) q,
    ← Category.assoc]
  have hd := simplexι_d R (staircaseMappedSimplex c π)
  change simplexι R (staircaseMappedSimplex c π) ≫ (Csing R X).d (q+1) q = _ at hd
  rw [hd, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]

/-- The actual signed staircase sum is a cycle of the actual relative
singular chain complex. Only the displayed boundary-of-cube condition is
used, and all internal singular faces cancel pairwise. -/
theorem staircaseRelativeChain_cycle {q : ℕ}
    (c : C(StaircaseCube (q+1),X))
    (hc : ∀ x ∈ staircaseCubeBoundary (q+1), c x ∈ A) :
    staircaseRelativeChain R A c ≫
      (relComplex R (subIncl (Y := X) A)).d (q+1) q = 0 := by
  unfold staircaseRelativeChain
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, staircaseRelativeGenerator_d, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  simp_rw [smul_comm (Equiv.Perm.sign _ : ℤ) ((-1 : ℤ)^i.val)]
  rw [← Finset.smul_sum, staircaseRelative_faces_cancel R A c hc i, smul_zero]

end Relative
end NRR.PrimePowerTopology
