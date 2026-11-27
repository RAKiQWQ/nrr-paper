import NRR.PrimePowerTopologyDiskHomology
import NRR.SingularHomologyMayerVietorisMap

/-! Coordinate reflection on genuine sphere and disk fundamental classes. -/

noncomputable section
set_option maxHeartbeats 200000
open Set Topology Metric CategoryTheory Limits AlgebraicTopology
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

def reflectFirstVector (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (fun i => if i = 0 then -(x i) else x i)

@[simp] theorem reflectFirstVector_apply (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1))) (i : Fin (n+1)) :
    reflectFirstVector n x i = if i = 0 then -(x i) else x i := rfl

theorem norm_reflectFirstVector (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    ‖reflectFirstVector n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = 0 <;> simp [hi]

theorem continuous_reflectFirstVector (n : ℕ) : Continuous (reflectFirstVector n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i = 0 <;> simp only [reflectFirstVector, hi, ↓reduceIte] <;> fun_prop

def sphereFirstReflectionMap (n : ℕ) : TopCat.of (Sph n) ⟶ TopCat.of (Sph n) :=
  TopCat.ofHom ⟨fun z => ⟨reflectFirstVector n z.val, by
    rw [mem_sphere_zero_iff_norm, norm_reflectFirstVector]
    exact mem_sphere_zero_iff_norm.mp z.property⟩,
    ((continuous_reflectFirstVector n).comp continuous_subtype_val).subtype_mk _⟩

theorem sphereFirstReflectionMap_zero : sphereFirstReflectionMap 0 = sphereAntipodalMap 0 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simp [sphereFirstReflectionMap, sphereAntipodalMap, sphereAntipodalHomeo]

theorem reflectFirstVector_snoc (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (z : ℝ) :
    reflectFirstVector (n+1) (snocLp x z) = snocLp (reflectFirstVector n x) z := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h : Fin.last (n+1) ≠ (0 : Fin (n+2)) := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_zero] at hv
      omega
    simp [reflectFirstVector_apply, h, snocLp_last]
  · simp only [reflectFirstVector_apply, snocLp_castSucc]
    by_cases h : j = 0
    · subst j
      simp
    · have hc : j.castSucc ≠ (0 : Fin (n+2)) := by
        intro he
        apply h
        exact Fin.ext (congrArg (fun k : Fin (n+2) => k.val) he)
      simp [h, hc]

theorem reflectFirstVector_smul (n : ℕ) (a : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    reflectFirstVector n (a • x) = a • reflectFirstVector n x := by
  apply PiLp.ext
  intro i
  by_cases hi : i = 0 <;> simp [reflectFirstVector_apply, hi]

@[simp] theorem sphHeight_firstReflection (n : ℕ) (z : Sph (n+1)) :
    sphHeight (sphereFirstReflectionMap (n+1) z) = sphHeight z := by
  have h : Fin.last (n+1) ≠ (0 : Fin (n+2)) := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  simp [sphereFirstReflectionMap, sphHeight, h]

theorem firstReflection_lower (n : ℕ) :
    MapsTo (sphereFirstReflectionMap (n+1)) (sphLowerCap n) (sphLowerCap n) := by
  intro z hz
  rw [mem_sphLowerCap, sphHeight_firstReflection]
  exact mem_sphLowerCap.mp hz

theorem firstReflection_upper (n : ℕ) :
    MapsTo (sphereFirstReflectionMap (n+1)) (sphUpperCap n) (sphUpperCap n) := by
  intro z hz
  rw [mem_sphUpperCap, sphHeight_firstReflection]
  exact mem_sphUpperCap.mp hz

def beltFirstReflectionMap (n : ℕ) : TopCat.of (sphBelt n) ⟶ TopCat.of (sphBelt n) :=
  mvIntersectionMap (sphLowerCap n) (sphUpperCap n) (sphLowerCap n) (sphUpperCap n)
    (sphereFirstReflectionMap (n+1)) (firstReflection_lower n) (firstReflection_upper n)

theorem firstReflection_beltOfProd (n : ℕ)
    (p : Sph n × Icc (-(1/3) : ℝ) (1/3)) :
    beltFirstReflectionMap n (beltOfProd p) =
      beltOfProd (sphereFirstReflectionMap n p.1, p.2) := by
  apply Subtype.ext
  apply Subtype.ext
  change reflectFirstVector (n+1) (beltVec p) =
    beltVec (sphereFirstReflectionMap n p.1, p.2)
  simp only [beltVec, reflectFirstVector_snoc, reflectFirstVector_smul]
  rfl

theorem sphBeltHomotopyEquiv_apply (n : ℕ) (z : sphBelt n) :
    (sphBeltHomotopyEquiv n).toFun z = ((sphBeltHomeo n) z).1 := rfl

theorem beltFirstReflection_naturality (n : ℕ) :
    beltFirstReflectionMap n ≫ TopCat.ofHom (sphBeltHomotopyEquiv n).toFun =
      TopCat.ofHom (sphBeltHomotopyEquiv n).toFun ≫ sphereFirstReflectionMap n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨p, rfl⟩ := beltOfProd_bijective.surjective z
  change (sphBeltHomotopyEquiv n).toFun (beltFirstReflectionMap n (beltOfProd p)) =
    sphereFirstReflectionMap n ((sphBeltHomotopyEquiv n).toFun (beltOfProd p))
  rw [firstReflection_beltOfProd, sphBeltHomotopyEquiv_apply, sphBeltHomotopyEquiv_apply]
  have inv (q : Sph n × Icc (-(1/3) : ℝ) (1/3)) :
      sphBeltHomeo n (beltOfProd q) = q := (sphBeltHomeo n).apply_symm_apply q
  rw [inv, inv]


variable (R : Type) [Ring R]

theorem beltFirstReflection_homology_naturality (n k : ℕ) :
    HabsMap R k (beltFirstReflectionMap n) ≫ (sphereBeltHomologyIso R n k).hom =
      (sphereBeltHomologyIso R n k).hom ≫ HabsMap R k (sphereFirstReflectionMap n) := by
  change HabsMap R k (beltFirstReflectionMap n) ≫
      HabsMap R k (TopCat.ofHom (sphBeltHomotopyEquiv n).toFun) =
    HabsMap R k (TopCat.ofHom (sphBeltHomotopyEquiv n).toFun) ≫
      HabsMap R k (sphereFirstReflectionMap n)
  rw [← HabsMap_comp, ← HabsMap_comp, beltFirstReflection_naturality]

def sphereSmallFirstReflection (n : ℕ) :
    mvSmallComplex (R := R) (X := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) ⟶
      mvSmallComplex (R := R) (X := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) :=
  mvSmallChainMap R (X := TopCat.of (Sph (n+1))) (Y := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) (sphLowerCap n) (sphUpperCap n)
    (sphereFirstReflectionMap (n+1)) (firstReflection_lower n) (firstReflection_upper n)

theorem sphereSmallFirstReflection_comparison (n k : ℕ) :
    HomologicalComplex.homologyMap (sphereSmallFirstReflection R n) k ≫
        (sphereSmallComparisonIso R n k).hom =
      (sphereSmallComparisonIso R n k).hom ≫
        HabsMap R k (sphereFirstReflectionMap (n+1)) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g k)
    (mvSmallChainMap_incl R (X := TopCat.of (Sph (n+1))) (Y := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) (sphLowerCap n) (sphUpperCap n)
      (sphereFirstReflectionMap (n+1)) (firstReflection_lower n) (firstReflection_upper n))
  exact (HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    (h.trans (HomologicalComplex.homologyMap_comp _ _ k))

theorem sphereSmallFirstReflection_delta (n k : ℕ) :
    mvSmallDelta R (X := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) k ≫
        HabsMap R k (beltFirstReflectionMap n) =
      HomologicalComplex.homologyMap (sphereSmallFirstReflection R n) (k+1) ≫
        mvSmallDelta R (X := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) k :=
  mvSmallDelta_naturality R (X := TopCat.of (Sph (n+1))) (Y := TopCat.of (Sph (n+1))) (sphLowerCap n) (sphUpperCap n) (sphLowerCap n) (sphUpperCap n)
    (sphereFirstReflectionMap (n+1)) (firstReflection_lower n) (firstReflection_upper n) k

private theorem firstReflection_eq_neg_of_small (n k : ℕ)
    (hs : HomologicalComplex.homologyMap (sphereSmallFirstReflection R n) k = -𝟙 _) :
    HabsMap R k (sphereFirstReflectionMap (n+1)) = -𝟙 _ := by
  apply (cancel_epi (sphereSmallComparisonIso R n k).hom).mp
  calc
    _ = HomologicalComplex.homologyMap (sphereSmallFirstReflection R n) k ≫
        (sphereSmallComparisonIso R n k).hom :=
      (sphereSmallFirstReflection_comparison R n k).symm
    _ = (-𝟙 _) ≫ (sphereSmallComparisonIso R n k).hom := by rw [hs]
    _ = _ := by simp

theorem firstReflection_smallHomology_one :
    HomologicalComplex.homologyMap (sphereSmallFirstReflection R 0) 1 = -𝟙 _ := by
  let δ := mvSmallDelta R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0
  have hzA := isZero_Habs_of_contractible R 1 (by omega) (TopCat.of (sphLowerCap 0))
  have hzB := isZero_Habs_of_contractible R 1 (by omega) (TopCat.of (sphUpperCap 0))
  have hk : mvSmallKappa R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 1 = 0 :=
    (isZero_mvSum R (X := TopCat.of (Sph 1)) _ _ 1 hzA hzB).eq_zero_of_src _
  letI : Mono δ := (mvSmall_exact_kappa_delta R (X := TopCat.of (Sph 1)) _ _ 0).mono_g hk
  have collapse : δ ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of (sphBelt 0))) = 0 := by
    let m := biprod.lift (HabsZeroCollapseIso R (TopCat.of (sphLowerCap 0))).inv
      (HabsZeroCollapseIso R (TopCat.of (sphUpperCap 0))).inv
    letI : Mono m := mono_mvIota_zero_factor R (X := TopCat.of (Sph 1)) _ _
    apply (cancel_mono m).mp
    rw [zero_comp, Category.assoc]
    change δ ≫ (HabsMap R 0 (homologyPointCollapse (TopCat.of (sphBelt 0))) ≫ m) = 0
    simpa only [mvIota_zero_factor] using
      (mvSmallDelta_comp_mvIota R (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0) 0)
  have negδ : δ ≫ HabsMap R 0 (beltFirstReflectionMap 0) = -δ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (ModuleCat.mono_iff_injective (sphereBeltHomologyIso R 0 0).hom).mp inferInstance
    have hc := congrArg (fun g => g z) collapse
    have haug := congrArg (fun g => g (δ z)) (sphereBeltHomologyIso_comp_collapse R 0)
    change HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0)))
      ((sphereBeltHomologyIso R 0 0).hom (δ z)) =
      HabsMap R 0 (homologyPointCollapse (TopCat.of (sphBelt 0))) (δ z) at haug
    have hz : HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0)))
        ((sphereBeltHomologyIso R 0 0).hom (δ z)) = 0 := haug.trans hc
    have hn := congrArg (fun g => g (δ z)) (beltFirstReflection_homology_naturality R 0 0)
    change (sphereBeltHomologyIso R 0 0).hom
      (HabsMap R 0 (beltFirstReflectionMap 0) (δ z)) =
        HabsMap R 0 (sphereFirstReflectionMap 0) ((sphereBeltHomologyIso R 0 0).hom (δ z)) at hn
    rw [sphereFirstReflectionMap_zero] at hn
    change (sphereBeltHomologyIso R 0 0).hom
      (HabsMap R 0 (beltFirstReflectionMap 0) (δ z)) =
        (sphereBeltHomologyIso R 0 0).hom (-(δ z))
    rw [map_neg]
    exact hn.trans (sphereZeroReducedHomology_antipodal R _ hz)
  apply (cancel_mono δ).mp
  calc
    _ = δ ≫ HabsMap R 0 (beltFirstReflectionMap 0) :=
      (sphereSmallFirstReflection_delta R 0 0).symm
    _ = -δ := negδ
    _ = _ := by simp

/-- Reflection of a single coordinate acts by -1 on every actual positive
sphere's top singular homology group. -/
theorem sphereFirstReflection_HabsMap_top (n : ℕ) :
    HabsMap R (n+1) (sphereFirstReflectionMap (n+1)) = -𝟙 _ := by
  induction n with
  | zero => exact firstReflection_eq_neg_of_small R 0 1 (firstReflection_smallHomology_one R)
  | succ n ih =>
    apply firstReflection_eq_neg_of_small R (n+1) (n+2)
    let δ := mvSmallDelta R (X := TopCat.of (Sph (n+2)))
      (sphLowerCap (n+1)) (sphUpperCap (n+1)) (n+1)
    letI : IsIso δ := isIso_mvSmallDelta R (X := TopCat.of (Sph (n+2)))
      (sphLowerCap (n+1)) (sphUpperCap (n+1)) (n+1)
      (isZero_Habs_of_contractible R (n+1+1) (by omega) (TopCat.of (sphLowerCap (n+1))))
      (isZero_Habs_of_contractible R (n+1+1) (by omega) (TopCat.of (sphUpperCap (n+1))))
      (isZero_Habs_of_contractible R (n+1) (by omega) (TopCat.of (sphLowerCap (n+1))))
      (isZero_Habs_of_contractible R (n+1) (by omega) (TopCat.of (sphUpperCap (n+1))))
    have hb : HabsMap R (n+1) (beltFirstReflectionMap (n+1)) = -𝟙 _ := by
      apply (cancel_mono (sphereBeltHomologyIso R (n+1) (n+1)).hom).mp
      rw [beltFirstReflection_homology_naturality, ih]
      simp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (ModuleCat.mono_iff_injective δ).mp inferInstance
    change δ (HomologicalComplex.homologyMap (sphereSmallFirstReflection R (n+1)) (n+2) z) = δ (-z)
    rw [map_neg]
    have hnat := congrArg (fun g => g z) (sphereSmallFirstReflection_delta R (n+1) (n+1))
    change HabsMap R (n+1) (beltFirstReflectionMap (n+1)) (δ z) =
      δ (HomologicalComplex.homologyMap (sphereSmallFirstReflection R (n+1)) (n+2) z) at hnat
    have hneg := congrArg (fun g => g (δ z)) hb
    change HabsMap R (n+1) (beltFirstReflectionMap (n+1)) (δ z) = -(δ z) at hneg
    exact hnat.symm.trans hneg

theorem sphereFundamentalClass_firstReflection (n : ℕ) :
    HabsMap R (n+1) (sphereFirstReflectionMap (n+1)) (sphereFundamentalClass R n) =
      -sphereFundamentalClass R n := by
  rw [sphereFirstReflection_HabsMap_top]
  rfl

end NRR.PrimePowerTopology
