import NRR.PrimePowerTopologyOnePointHomology
import NRR.PrimePowerTopologySphereOrientation
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Coordinate reflections and their ordinary one-point homology action. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology Metric CategoryTheory Limits
open scoped OnePoint
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

private def permutationDegreePole (m : ℕ) : EuclideanSpace ℝ (Fin (m+1)) :=
  EuclideanSpace.single (Fin.last m) 1

private theorem permutationDegreePole_norm (m : ℕ) :
    ‖permutationDegreePole m‖ = 1 := by
  simp [permutationDegreePole]

private def permutationDegreeHyperplane (m : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (m+1))) :=
  (ℝ ∙ permutationDegreePole m)ᗮ

private def permutationDegreeSnoc (m : ℕ) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] permutationDegreeHyperplane m where
  toFun x := ⟨snocLp x 0, by
    change snocLp x 0 ∈ (ℝ ∙ permutationDegreePole m)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [permutationDegreePole, EuclideanSpace.inner_toLp_toLp,
      EuclideanSpace.inner_eq_star_dotProduct, snocLp]⟩
  map_add' x y := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    induction i using Fin.lastCases with
    | last => simp [snocLp]
    | cast i => simp [snocLp]
  map_smul' a x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    induction i using Fin.lastCases with
    | last => simp [snocLp]
    | cast i => simp [snocLp]
  norm_map' x := by
    change ‖snocLp x 0‖ = ‖x‖
    have h := norm_snocLp_sq x 0
    nlinarith [norm_nonneg (snocLp x 0), norm_nonneg x]

private theorem permutationDegreeSnoc_surjective (m : ℕ) :
    Function.Surjective (permutationDegreeSnoc m) := by
  intro y
  let x : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 fun i : Fin m => y.val i.castSucc
  have hy : y.val (Fin.last m) = 0 := by
    have hinner : inner ℝ y.val (permutationDegreePole m) = 0 := by
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp y.property
    simpa [permutationDegreePole, EuclideanSpace.inner_toLp_toLp,
      EuclideanSpace.inner_eq_star_dotProduct] using hinner
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply PiLp.ext
  intro i
  induction i using Fin.lastCases with
  | last => simpa [permutationDegreeSnoc, snocLp] using hy.symm
  | cast i => simp [permutationDegreeSnoc, snocLp, x]

private noncomputable def permutationDegreeHyperplaneEquiv (m : ℕ) :
    EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] permutationDegreeHyperplane m :=
  LinearIsometryEquiv.ofSurjective (permutationDegreeSnoc m)
    (permutationDegreeSnoc_surjective m)

private noncomputable def permutationDegreeSphereEquiv (m : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin m)) ≃ₜ Sph m :=
  (permutationDegreeHyperplaneEquiv m).toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (permutationDegreePole_norm m))

private noncomputable def permutationDegreeReflectionLIE (n : ℕ) :
    EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun := reflectFirstVector n
  invFun := reflectFirstVector n
  left_inv x := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0 <;> simp [reflectFirstVector_apply, hi]
  right_inv x := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0 <;> simp [reflectFirstVector_apply, hi]
  map_add' x y := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0 <;> simp [reflectFirstVector_apply, hi] <;> ring
  map_smul' a x := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0 <;> simp [reflectFirstVector_apply, hi]
  norm_map' := norm_reflectFirstVector n

private theorem permutationDegreePole_reflection_fixed (m : ℕ)
    (hm : 0 < m) :
    permutationDegreeReflectionLIE m (permutationDegreePole m) =
      permutationDegreePole m := by
  apply PiLp.ext
  intro i
  have hlast : Fin.last m ≠ (0 : Fin (m+1)) := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
    omega
  by_cases hi : i = 0
  · have hne : i ≠ Fin.last m := by
      intro he
      exact hlast (he.symm.trans hi)
    simp [permutationDegreePole, permutationDegreeReflectionLIE,
      reflectFirstVector_apply, hi, hne, hm.ne']
  · simp [permutationDegreePole, permutationDegreeReflectionLIE,
      reflectFirstVector_apply, hi]

private theorem permutationDegreeHyperplane_mem_iff (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    x ∈ permutationDegreeHyperplane m ↔ x (Fin.last m) = 0 := by
  change x ∈ (ℝ ∙ permutationDegreePole m)ᗮ ↔ _
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [permutationDegreePole, EuclideanSpace.inner_eq_star_dotProduct]

private theorem permutationDegreeHyperplane_map_reflection (m : ℕ)
    (hm : 0 < m) :
    (permutationDegreeHyperplane m).map
        (permutationDegreeReflectionLIE m).toLinearEquiv.toLinearMap =
      permutationDegreeHyperplane m := by
  apply Submodule.ext
  intro y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [permutationDegreeHyperplane_mem_iff m] at hx ⊢
    simpa [permutationDegreeReflectionLIE, reflectFirstVector_apply,
      show Fin.last m ≠ (0 : Fin (m+1)) from by
        intro he
        have hv := congrArg Fin.val he
        simp at hv
        omega] using hx
  · intro hy
    rw [permutationDegreeHyperplane_mem_iff m] at hy
    refine ⟨permutationDegreeReflectionLIE m y, ?_, ?_⟩
    · rw [permutationDegreeHyperplane_mem_iff m]
      simpa [permutationDegreeReflectionLIE, reflectFirstVector_apply,
        show Fin.last m ≠ (0 : Fin (m+1)) from by
          intro he
          have hv := congrArg Fin.val he
          simp at hv
          omega] using hy
    · exact (permutationDegreeReflectionLIE m).apply_symm_apply y

private noncomputable def permutationDegreeHyperplaneReflection (m : ℕ)
    (hm : 0 < m) :
    permutationDegreeHyperplane m ≃ₗᵢ[ℝ] permutationDegreeHyperplane m where
  toFun y := ⟨permutationDegreeReflectionLIE m y.val, by
    rw [permutationDegreeHyperplane_mem_iff m]
    have hy : y.val (Fin.last m) = 0 :=
      (permutationDegreeHyperplane_mem_iff m y.val).mp y.property
    have hlast : Fin.last m ≠ (0 : Fin (m+1)) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
      omega
    simpa [permutationDegreeReflectionLIE, reflectFirstVector_apply, hlast]
      using hy⟩
  invFun y := ⟨permutationDegreeReflectionLIE m y.val, by
    rw [permutationDegreeHyperplane_mem_iff m]
    have hy : y.val (Fin.last m) = 0 :=
      (permutationDegreeHyperplane_mem_iff m y.val).mp y.property
    have hlast : Fin.last m ≠ (0 : Fin (m+1)) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
      omega
    simpa [permutationDegreeReflectionLIE, reflectFirstVector_apply, hlast]
      using hy⟩
  left_inv y := by
    apply Subtype.ext
    exact (permutationDegreeReflectionLIE m).apply_symm_apply y.val
  right_inv y := by
    apply Subtype.ext
    exact (permutationDegreeReflectionLIE m).apply_symm_apply y.val
  map_add' y z := by
    apply Subtype.ext
    exact (permutationDegreeReflectionLIE m).map_add y.val z.val
  map_smul' a y := by
    apply Subtype.ext
    exact (permutationDegreeReflectionLIE m).map_smul a y.val
  norm_map' y := (permutationDegreeReflectionLIE m).norm_map y.val

private theorem stereographic_symm_reflection_commutes (m : ℕ) (hm : 0 < m)
    (z : permutationDegreeHyperplane m) :
    sphereFirstReflectionMap m
        ((stereographic (permutationDegreePole_norm m)).symm z) =
      (stereographic (permutationDegreePole_norm m)).symm
        (permutationDegreeHyperplaneReflection m hm z) := by
  let r := permutationDegreeReflectionLIE m
  apply Subtype.ext
  change r (stereoInvFunAux (permutationDegreePole m) z.val) =
    stereoInvFunAux (permutationDegreePole m) (r z.val)
  rw [stereoInvFunAux_apply, stereoInvFunAux_apply,
    r.map_smul, r.map_add, r.map_smul, r.map_smul, r.norm_map,
    permutationDegreePole_reflection_fixed m hm]

private theorem permutationDegreeSphereEquiv_reflection (k : ℕ)
    (x : OnePoint (EuclideanSpace ℝ (Fin (k+1)))) :
    permutationDegreeSphereEquiv (k+1)
        (OnePoint.map (reflectFirstVector k) x) =
      sphereFirstReflectionMap (k+1) (permutationDegreeSphereEquiv (k+1) x) := by
  have hm : 0 < k+1 := by omega
  induction x using OnePoint.rec with
  | infty =>
      apply Subtype.ext
      simpa [permutationDegreeSphereEquiv, onePointHyperplaneHomeoUnitSphere,
        sphereFirstReflectionMap] using
        (permutationDegreePole_reflection_fixed (k+1) hm).symm
  | coe x =>
      let e := permutationDegreeHyperplaneEquiv (k+1)
      let s := stereographic (permutationDegreePole_norm (k+1))
      have hsplit : e (reflectFirstVector k x) =
          permutationDegreeHyperplaneReflection (k+1) hm (e x) := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        induction i using Fin.lastCases with
        | last =>
            have hlast : Fin.last (k+1) ≠ (0 : Fin (k+2)) := by
              intro h
              have hv := congrArg Fin.val h
              simp at hv
            simp [e, permutationDegreeHyperplaneEquiv, permutationDegreeSnoc,
              permutationDegreeHyperplaneReflection, permutationDegreeReflectionLIE,
              reflectFirstVector_apply, snocLp, hlast]
        | cast i =>
            simp [e, permutationDegreeHyperplaneEquiv, permutationDegreeSnoc,
              permutationDegreeHyperplaneReflection, permutationDegreeReflectionLIE,
              reflectFirstVector_apply, snocLp, Fin.castSucc_eq_zero_iff]
      change s.symm (e (reflectFirstVector k x)) =
        sphereFirstReflectionMap (k+1) (s.symm (e x))
      rw [stereographic_symm_reflection_commutes (k+1) hm, hsplit]

/-- Reflection of the first scalar coordinate on the genuine one-point
compactification of Euclidean space. -/
def euclideanOnePointFirstReflectionMap (m : ℕ) :
    TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (m+1)))) ⟶
      TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (m+1)))) :=
  TopCat.ofHom ⟨(permutationDegreeReflectionLIE m).toHomeomorph.onePointCongr,
    (permutationDegreeReflectionLIE m).toHomeomorph.onePointCongr.continuous⟩

/-- The actual compactified reflection acts as minus the identity in top
singular homology, over every coefficient ring. -/
theorem euclideanOnePointFirstReflectionMap_top (R : Type) [Ring R] (m : ℕ) :
    HabsMap R (m+1) (euclideanOnePointFirstReflectionMap m) = -𝟙 _ := by
  let e := HabsIsoOfHomotopyEquiv R (m+1)
    (permutationDegreeSphereEquiv (m+1)).toHomotopyEquiv
  have h : euclideanOnePointFirstReflectionMap m ≫
      TopCat.ofHom (permutationDegreeSphereEquiv (m+1)).toHomotopyEquiv.toFun =
      TopCat.ofHom (permutationDegreeSphereEquiv (m+1)).toHomotopyEquiv.toFun ≫
        sphereFirstReflectionMap (m+1) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact permutationDegreeSphereEquiv_reflection m
  apply (cancel_mono e.hom).mp
  change HabsMap R (m+1) (euclideanOnePointFirstReflectionMap m) ≫
    HabsMap R (m+1) _ = (-𝟙 _) ≫ _
  rw [← HabsMap_comp, h, HabsMap_comp, sphereFirstReflection_HabsMap_top]
  simp [e, HabsIsoOfHomotopyEquiv]

private def scalarProductEuclideanEquiv (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (ℝ × V) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V+1)) :=
  ((LinearEquiv.refl ℝ ℝ).prodCongr (Module.finBasis ℝ V).equivFun).trans
    ((Fin.consLinearEquiv ℝ (fun _ : Fin (Module.finrank ℝ V+1) => ℝ)).trans
      (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ V+1) → ℝ)).symm)

/-- Reflect the scalar coordinate while retaining every coordinate of `V`. -/
def scalarProductOnePointReflectionMap (V : Type) [TopologicalSpace V] :
    TopCat.of (OnePoint (ℝ × V)) ⟶ TopCat.of (OnePoint (ℝ × V)) :=
  let e := ((Homeomorph.neg ℝ).prodCongr (Homeomorph.refl V)).onePointCongr
  TopCat.ofHom ⟨e,e.continuous⟩

/-- Reflection on a real scalar factor has degree minus one on the actual
compactification of an arbitrary finite-dimensional real vector space. -/
theorem scalarProductOnePointReflectionMap_top (R : Type) [Ring R]
    (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    HabsMap R (Module.finrank ℝ V+1) (scalarProductOnePointReflectionMap V) =
      -𝟙 _ := by
  let e := (scalarProductEuclideanEquiv V).toContinuousLinearEquiv.toHomeomorph.onePointCongr
  let E := HabsIsoOfHomotopyEquiv R (Module.finrank ℝ V+1) e.toHomotopyEquiv
  have hs (p : ℝ × V) : scalarProductEuclideanEquiv V (-p.1,p.2) =
      reflectFirstVector (Module.finrank ℝ V) (scalarProductEuclideanEquiv V p) := by
    apply PiLp.ext
    intro i
    induction i using Fin.cases with
    | zero => simp [scalarProductEuclideanEquiv, reflectFirstVector_apply]
    | succ i => simp [scalarProductEuclideanEquiv, reflectFirstVector_apply]
  have h : scalarProductOnePointReflectionMap V ≫ TopCat.ofHom e.toHomotopyEquiv.toFun =
      TopCat.ofHom e.toHomotopyEquiv.toFun ≫
        euclideanOnePointFirstReflectionMap (Module.finrank ℝ V) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    induction x using OnePoint.rec with
    | infty => rfl
    | coe p => exact congrArg OnePoint.some (hs p)
  apply (cancel_mono E.hom).mp
  change HabsMap R (Module.finrank ℝ V+1) (scalarProductOnePointReflectionMap V) ≫
    HabsMap R (Module.finrank ℝ V+1) _ = (-𝟙 _) ≫ _
  rw [← HabsMap_comp, h, HabsMap_comp, euclideanOnePointFirstReflectionMap_top]
  simp [E, HabsIsoOfHomotopyEquiv]

section HeightTransposition

variable {n : ℕ} (i j : Fin n) (hij : i ≠ j)

/-- The fixed subspace of a coordinate transposition. -/
def heightTranspositionFixed : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | v i = v j}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change v i = v j at hv
    change w i = w j at hw
    change v i + w i = v j + w j
    rw [hv, hw]
  smul_mem' := by
    intro a v hv
    change v i = v j at hv
    change a * v i = a * v j
    rw [hv]

/-- Coordinates adapted to a transposition: the antisymmetric coordinate
and the fixed hyperplane. The factor `2` chooses a particularly simple
inverse while working over `ℝ`. -/
def heightTranspositionSplit :
    (Fin n → ℝ) ≃ₗ[ℝ] ℝ × heightTranspositionFixed i j where
  toFun v :=
    ((v i - v j) / 2,
      ⟨fun k => if k = i then (v i + v j) / 2
        else if k = j then (v i + v j) / 2 else v k, by
          change (if i = i then (v i + v j) / 2 else
            if i = j then (v i + v j) / 2 else v i) =
            (if j = i then (v i + v j) / 2 else
              if j = j then (v i + v j) / 2 else v j)
          simp [hij, hij.symm]⟩)
  invFun p := fun k =>
    if k = i then p.1 + p.2.1 i
    else if k = j then -p.1 + p.2.1 j else p.2.1 k
  left_inv v := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [hij]
      field_simp
      ring
    · by_cases hkj : k = j
      · subst k
        have hji := hij.symm
        simp [hij, hji]
        field_simp
        ring
      · simp [hki, hkj]
  right_inv p := by
    have hfix : p.2.1 i = p.2.1 j := p.2.property
    apply Prod.ext
    · simp [hij, hij.symm]
      rw [hfix]
      field_simp <;> ring
    · apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        simp [hij, hij.symm]
        rw [hfix]
        field_simp <;> ring
      · by_cases hkj : k = j
        · subst k
          simp [hij, hij.symm]
          rw [hfix]
          field_simp <;> ring
        · simp [hki, hkj]
  map_add' v w := by
    apply Prod.ext
    · simp [Pi.add_apply]
      field_simp
      ring
    · apply Subtype.ext
      funext k
      by_cases hk : k = i <;> by_cases hk' : k = j <;>
        simp [hk, hk'] <;> ring
  map_smul' a v := by
    apply Prod.ext
    · simp [Pi.smul_apply, smul_eq_mul]
      field_simp <;> ring
    · apply Subtype.ext
      funext k
      by_cases hk : k = i <;> by_cases hk' : k = j <;>
        simp [hk, hk'] <;> ring

/-- Under this linear equivalence, swapping the two height coordinates is
exactly negation on one real coordinate and the identity on the fixed
hyperplane. -/
theorem heightTranspositionSplit_intertwines (v : Fin n → ℝ) :
    heightTranspositionSplit i j hij (labelPermutationLinear (Equiv.swap i j) v) =
      (- (heightTranspositionSplit i j hij v).1,
        (heightTranspositionSplit i j hij v).2) := by
  apply Prod.ext
  · simp [heightTranspositionSplit, labelPermutationLinear, Equiv.swap_apply_def,
      Equiv.swap_comm, hij, hij.symm] <;> field_simp <;> ring
  · apply Subtype.ext
    funext k
    by_cases hki : k = i
    · subst k
      simp [heightTranspositionSplit, labelPermutationLinear, Equiv.swap_apply_def,
        Equiv.swap_comm, hij, hij.symm] <;> field_simp <;> ring
    · by_cases hkj : k = j
      · subst k
        simp [heightTranspositionSplit, labelPermutationLinear, Equiv.swap_apply_def,
          Equiv.swap_comm, hij, hij.symm] <;> field_simp <;> ring
      · simp [heightTranspositionSplit, labelPermutationLinear, Equiv.swap_apply_def,
          Equiv.swap_comm, hki, hkj, hij, hij.symm]

/-- The coordinate split is unchanged when an arbitrary base space is
carried along as a product factor. -/
noncomputable def heightTranspositionProductSplitHomeomorph
    {X : Type*} [TopologicalSpace X] :
    X × (Fin n → ℝ) ≃ₜ X × (ℝ × heightTranspositionFixed i j) :=
  (Homeomorph.refl X).prodCongr
    (heightTranspositionSplit i j hij).toContinuousLinearEquiv.toHomeomorph

def heightTranspositionProductAction {X : Type*} (p : X × (Fin n → ℝ)) :
    X × (Fin n → ℝ) :=
  (p.1, labelPermutationLinear (Equiv.swap i j) p.2)

def heightTranspositionSplitAction {X : Type*}
    (p : X × (ℝ × heightTranspositionFixed i j)) :
    X × (ℝ × heightTranspositionFixed i j) :=
  (p.1, (-p.2.1, p.2.2))

/-- The swap on the full product conjugates to a reflection of one scalar
coordinate, with the base and the remaining fixed coordinates unchanged. -/
theorem heightTranspositionProductSplit_intertwines {X : Type*}
    [TopologicalSpace X] (p : X × (Fin n → ℝ)) :
    heightTranspositionProductSplitHomeomorph i j hij
        (heightTranspositionProductAction i j p) =
      heightTranspositionSplitAction i j
        (heightTranspositionProductSplitHomeomorph i j hij p) := by
  rcases p with ⟨x, v⟩
  simp [heightTranspositionProductSplitHomeomorph, heightTranspositionProductAction,
    heightTranspositionSplitAction, heightTranspositionSplit_intertwines]

/-- The same conjugacy holds on the actual one-point compactifications,
including their points at infinity. -/
theorem heightTranspositionOnePointSplit_intertwines {X : Type*}
    [TopologicalSpace X] (p : OnePoint (X × (Fin n → ℝ))) :
    OnePoint.map (heightTranspositionProductSplitHomeomorph i j hij)
        (OnePoint.map (heightTranspositionProductAction i j) p) =
      OnePoint.map (heightTranspositionSplitAction i j)
        (OnePoint.map (heightTranspositionProductSplitHomeomorph i j hij) p) := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe p =>
      simp only [OnePoint.map_some]
      exact congrArg (fun z : X × (ℝ × heightTranspositionFixed i j) =>
        (z : OnePoint (X × (ℝ × heightTranspositionFixed i j))))
        (heightTranspositionProductSplit_intertwines i j hij p)

private def heightTranspositionReflectionSplit (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    (X × (Fin n → ℝ)) ≃ₗ[ℝ] ℝ × (X × heightTranspositionFixed i j) :=
  ((LinearEquiv.refl ℝ X).prodCongr (heightTranspositionSplit i j hij)).trans
    ((LinearEquiv.prodAssoc ℝ X ℝ (heightTranspositionFixed i j)).symm.trans
      (((LinearEquiv.prodComm ℝ X ℝ).prodCongr
        (LinearEquiv.refl ℝ (heightTranspositionFixed i j))).trans
          (LinearEquiv.prodAssoc ℝ ℝ X (heightTranspositionFixed i j))))

end HeightTransposition

/-- The genuine compactified action on all labelled height coordinates,
with an arbitrary base vector-space factor held fixed. -/
def heightPermutationOnePointMap (X : Type) [TopologicalSpace X]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (X × (Fin n → ℝ))) ⟶
      TopCat.of (OnePoint (X × (Fin n → ℝ))) :=
  let e := ((Homeomorph.refl X).prodCongr
    (labelPermutationLinear σ).toContinuousLinearEquiv.toHomeomorph).onePointCongr
  TopCat.ofHom ⟨e,e.continuous⟩

/-- A transposition of two genuine height coordinates acts by minus one
on top singular homology, including when other base coordinates are present. -/
theorem heightPermutationOnePointMap_swap_top (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    HabsMap R (Module.finrank ℝ X+n) (heightPermutationOnePointMap X (Equiv.swap i j)) =
      -𝟙 _ := by
  let V := X × heightTranspositionFixed i j
  let e := (heightTranspositionReflectionSplit i j hij X).toContinuousLinearEquiv.toHomeomorph.onePointCongr
  have hd : Module.finrank ℝ V+1 = Module.finrank ℝ X+n := by
    have h := (heightTranspositionSplit i j hij).finrank_eq
    simp at h
    simp only [V, Module.finrank_prod]
    omega
  have h : heightPermutationOnePointMap X (Equiv.swap i j) ≫
      TopCat.ofHom e.toHomotopyEquiv.toFun =
      TopCat.ofHom e.toHomotopyEquiv.toFun ≫ scalarProductOnePointReflectionMap V := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    induction x using OnePoint.rec with
    | infty => rfl
    | coe p =>
      apply congrArg OnePoint.some
      change ((heightTranspositionSplit i j hij
          (labelPermutationLinear (Equiv.swap i j) p.2)).1,
        (p.1,(heightTranspositionSplit i j hij
          (labelPermutationLinear (Equiv.swap i j) p.2)).2)) = _
      rw [heightTranspositionSplit_intertwines]
      rfl
  let E := HabsIsoOfHomotopyEquiv R (Module.finrank ℝ X+n) e.toHomotopyEquiv
  apply (cancel_mono E.hom).mp
  change HabsMap R (Module.finrank ℝ X+n) (heightPermutationOnePointMap X (Equiv.swap i j)) ≫
    HabsMap R (Module.finrank ℝ X+n) _ = (-𝟙 _) ≫ _
  rw [← HabsMap_comp, h, HabsMap_comp]
  have hr : HabsMap R (Module.finrank ℝ X+n) (scalarProductOnePointReflectionMap V) = -𝟙 _ := by
    rw [← hd]
    exact scalarProductOnePointReflectionMap_top R V
  rw [hr]
  simp [V, E, HabsIsoOfHomotopyEquiv]

@[simp] theorem heightPermutationOnePointMap_one (X : Type) [TopologicalSpace X]
    (n : ℕ) : heightPermutationOnePointMap X (1 : Equiv.Perm (Fin n)) = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe p => rfl

theorem heightPermutationOnePointMap_mul (X : Type) [TopologicalSpace X]
    {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    heightPermutationOnePointMap X (σ*τ) =
      heightPermutationOnePointMap X τ ≫ heightPermutationOnePointMap X σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe p => rfl

/-- Every actual permutation of labelled heights acts by its integral sign
on top singular homology. This is deduced from geometric reflections and
the genuine composition law, rather than from a determinant assumption. -/
theorem heightPermutationOnePointMap_top (R : Type) [Ring R]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HabsMap R (Module.finrank ℝ X+n) (heightPermutationOnePointMap X σ) =
      (Equiv.Perm.sign σ : ℤ) • 𝟙 _ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul σ i j hij ih =>
    rw [heightPermutationOnePointMap_mul, HabsMap_comp, ih,
      heightPermutationOnePointMap_swap_top R X i j hij]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul]

end NRR.PrimePowerTopology
