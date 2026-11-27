/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The Mayer-Vietoris kernel comparison follows the strategy of
Submission/Homology/SphereOne.lean in akopjan/toptverbert-nandakumar,
revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
This implementation uses arbitrary ring coefficients, the already computed
pole-difference generator, and the local Lean 4.24 singular-chain model.
-/
import NRR.SingularHomologyMayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Analysis.NormedSpace.Connected

/-! Sphere calculations on the actual two-cap small-chain complex.
Comparison with all singular chains is kept separate until established. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

variable (R : Type) [Ring R]

@[reassoc (attr := simp)]
theorem comp_homologyPointCollapse {X Y : TopCat.{0}} (f : X ⟶ Y) :
    f ≫ homologyPointCollapse Y = homologyPointCollapse X := by
  ext

def sphereBeltHomologyIso (m k : ℕ) :
    Habs R k (TopCat.of (sphBelt m)) ≅ Habs R k (TopCat.of (Sph m)) :=
  HabsIsoOfHomotopyEquiv R k (sphBeltHomotopyEquiv m)

def sphereSmallStepIso (m k : ℕ) :
    (mvSmallComplex (R := R) (X := TopCat.of (Sph (m+1))) (sphLowerCap m) (sphUpperCap m)).homology (k+2) ≅
      Habs R (k+1) (TopCat.of (Sph m)) :=
  mvSmallDeltaIso_of_contractible R (X := TopCat.of (Sph (m+1))) (sphLowerCap m) (sphUpperCap m) k ≪≫
    sphereBeltHomologyIso R m (k+1)

theorem mvIota_zero_factor {X : TopCat.{0}} (A B : Set X)
    [PathConnectedSpace A] [PathConnectedSpace B] :
    mvIota R A B 0 = HabsMap R 0 (homologyPointCollapse (TopCat.of (A ∩ B : Set X))) ≫
      biprod.lift (HabsZeroCollapseIso R (TopCat.of A)).inv
        (HabsZeroCollapseIso R (TopCat.of B)).inv := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.lift_fst]
    simp only [mvIota, biprod.lift_fst]
    rw [Iso.eq_comp_inv]
    change HabsMap R 0 (mvInclLeft A B) ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of A)) = _
    rw [← HabsMap_comp, comp_homologyPointCollapse]
  · rw [Category.assoc, biprod.lift_snd]
    simp only [mvIota, biprod.lift_snd]
    rw [Iso.eq_comp_inv]
    change HabsMap R 0 (mvInclRight A B) ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of B)) = _
    rw [← HabsMap_comp, comp_homologyPointCollapse]

theorem mono_mvIota_zero_factor {X : TopCat.{0}} (A B : Set X)
    [PathConnectedSpace A] [PathConnectedSpace B] :
    Mono (biprod.lift (HabsZeroCollapseIso R (TopCat.of A)).inv
      (HabsZeroCollapseIso R (TopCat.of B)).inv) :=
  mono_of_mono_fac (biprod.lift_fst _ _)

private theorem exact_comp_mono {S : ShortComplex (ModuleCat R)} (hS : S.Exact)
    {T : ModuleCat R} (m : S.X₃ ⟶ T) [Mono m] :
    (ShortComplex.mk S.f (S.g ≫ m) (by rw [← Category.assoc, S.zero, zero_comp])).Exact := by
  have hm := (ModuleCat.mono_iff_injective m).mp inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x hx
  apply hS x
  apply hm
  simpa only [ConcreteCategory.comp_apply, map_zero] using hx

def sphereOneBeltGenerator :
    ModuleCat.of R R ⟶ Habs R 0 (TopCat.of (sphBelt 0)) :=
  sphereZeroGenerator R ≫ (sphereBeltHomologyIso R 0 0).inv

theorem sphereBeltHomologyIso_comp_collapse (m : ℕ) :
    (sphereBeltHomologyIso R m 0).hom ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph m))) =
    HabsMap R 0 (homologyPointCollapse (TopCat.of (sphBelt m))) := by
  change HabsMap R 0 (TopCat.ofHom (sphBeltHomotopyEquiv m).toFun) ≫
    HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph m))) = _
  rw [← HabsMap_comp, comp_homologyPointCollapse]

theorem sphereOneBeltGenerator_comp_iso :
    sphereOneBeltGenerator R ≫ (sphereBeltHomologyIso R 0 0).hom = sphereZeroGenerator R := by
  simp [sphereOneBeltGenerator, Category.assoc]

instance mono_sphereOneBeltGenerator : Mono (sphereOneBeltGenerator R) := by
  have h : sphereOneBeltGenerator R ≫
      ((sphereBeltHomologyIso R 0 0).hom ≫
        discreteHomologyCoefficient R (TopCat.of (Sph 0)) sphereZeroNorth) = 𝟙 _ := by
    rw [← Category.assoc, sphereOneBeltGenerator_comp_iso,
      sphereZeroGenerator_northCoefficient]
  exact mono_of_mono_fac h

theorem sphereOneBeltGenerator_comp_collapse :
    sphereOneBeltGenerator R ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of (sphBelt 0))) = 0 := by
  rw [← sphereBeltHomologyIso_comp_collapse R 0, ← Category.assoc,
    sphereOneBeltGenerator_comp_iso, sphereZeroGenerator_collapse]

theorem sphereOneBeltGenerator_exact_collapse :
    (ShortComplex.mk (sphereOneBeltGenerator R)
      (HabsMap R 0 (homologyPointCollapse (TopCat.of (sphBelt 0))))
      (sphereOneBeltGenerator_comp_collapse R)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hnat := congrArg (fun f : Habs R 0 (TopCat.of (sphBelt 0)) ⟶
      Habs R 0 (TopCat.of Unit) => f z) (sphereBeltHomologyIso_comp_collapse R 0)
  have hzero : HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0)))
      ((sphereBeltHomologyIso R 0 0).hom z) = 0 := hnat.trans hz
  obtain ⟨r, hr, _⟩ := sphereZeroGenerator_kernel_existsUnique R
    ((sphereBeltHomologyIso R 0 0).hom z) hzero
  refine ⟨r, ?_⟩
  apply (ModuleCat.mono_iff_injective (sphereBeltHomologyIso R 0 0).hom).mp inferInstance
  have hgen := congrArg (fun f : ModuleCat.of R R ⟶ Habs R 0 (TopCat.of (Sph 0)) =>
    f r) (sphereOneBeltGenerator_comp_iso R)
  exact hgen.trans hr

theorem sphereOneBeltGenerator_comp_mvIota :
    sphereOneBeltGenerator R ≫ mvIota R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0 = 0 := by
  rw [mvIota_zero_factor, ← Category.assoc]
  have h := sphereOneBeltGenerator_comp_collapse R
  change sphereOneBeltGenerator R ≫ HabsMap R 0
    (homologyPointCollapse (TopCat.of (sphLowerCap 0 ∩ sphUpperCap 0 : Set (Sph 1)))) = 0 at h
  rw [h, zero_comp]

theorem sphereOneBeltGenerator_exact_mvIota :
    (ShortComplex.mk (sphereOneBeltGenerator R)
      (mvIota R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0)
      (sphereOneBeltGenerator_comp_mvIota R)).Exact := by
  letI := mono_mvIota_zero_factor R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)
  simpa only [mvIota_zero_factor] using
    exact_comp_mono R (sphereOneBeltGenerator_exact_collapse R)
      (biprod.lift (HabsZeroCollapseIso R (TopCat.of (sphLowerCap 0))).inv
        (HabsZeroCollapseIso R (TopCat.of (sphUpperCap 0))).inv)

/-- The actual small-chain first homology for the two caps of the circle
is freely generated by the connecting lift of north minus south. -/
def sphereOneSmallHomologyIso :
    (mvSmallComplex (R := R) (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)).homology 1 ≅
      ModuleCat.of R R := by
  have hzA := isZero_Habs_of_contractible R 1 (by omega) (TopCat.of (sphLowerCap 0))
  have hzB := isZero_Habs_of_contractible R 1 (by omega) (TopCat.of (sphUpperCap 0))
  have hk : mvSmallKappa R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 1 = 0 :=
    (isZero_mvSum R (X := TopCat.of (Sph 1)) _ _ 1 hzA hzB).eq_zero_of_src _
  letI : Mono (mvSmallDelta R (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0) :=
    (mvSmall_exact_kappa_delta R (X := TopCat.of (Sph 1)) _ _ 0).mono_g hk
  exact IsLimit.conePointUniqueUpToIso
    (mvSmall_exact_delta_iota R (X := TopCat.of (Sph 1)) _ _ 0).fIsKernel
    (sphereOneBeltGenerator_exact_mvIota R).fIsKernel



/-- Every positive-dimensional actual metric sphere is path connected. -/
theorem pathConnectedSpace_positiveSphere (m : ℕ) : PathConnectedSpace (Sph (m+1)) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (show 1 < m+2 by omega)

theorem pathConnectedSpace_positiveBelt (m : ℕ) : PathConnectedSpace (sphBelt (m+1)) := by
  letI : PathConnectedSpace (Sph (m+1)) := pathConnectedSpace_positiveSphere m
  letI : ContractibleSpace (Icc (-(1/3) : ℝ) (1/3)) :=
    (convex_Icc _ _).contractibleSpace ⟨0, by constructor <;> norm_num⟩
  letI : PathConnectedSpace (Sph (m+1) × Icc (-(1/3) : ℝ) (1/3)) :=
    ⟨inferInstance, fun x y => ⟨(PathConnectedSpace.somePath x.1 y.1).prod
      (PathConnectedSpace.somePath x.2 y.2)⟩⟩
  exact (sphBeltHomeo (m+1)).symm.surjective.pathConnectedSpace
    (sphBeltHomeo (m+1)).symm.continuous

/-- Higher-dimensional sphere caps have zero small-chain first homology,
because their connected belt injects into either cap in degree zero. -/
theorem isZero_sphereSmallHomology_one (m : ℕ) :
    IsZero ((mvSmallComplex (R := R) (X := TopCat.of (Sph (m+2)))
      (sphLowerCap (m+1)) (sphUpperCap (m+1))).homology 1) := by
  let A : Set (Sph (m+2)) := sphLowerCap (m+1)
  let B : Set (Sph (m+2)) := sphUpperCap (m+1)
  letI : ContractibleSpace A := instContractibleSpaceSphLowerCap (m+1)
  letI : ContractibleSpace B := instContractibleSpaceSphUpperCap (m+1)
  letI : PathConnectedSpace (A ∩ B : Set (Sph (m+2))) :=
    pathConnectedSpace_positiveBelt m
  letI : IsIso (HabsMap R 0 (mvInclLeft (X := TopCat.of (Sph (m+2))) A B)) :=
    isIso_HabsMap_zero_of_pathConnected R _
  have hm : Mono (mvIota R (X := TopCat.of (Sph (m+2))) A B 0) :=
    mono_of_mono_fac (biprod.lift_fst
      (HabsMap R 0 (mvInclLeft (X := TopCat.of (Sph (m+2))) A B))
      (HabsMap R 0 (mvInclRight (X := TopCat.of (Sph (m+2))) A B)))
  have hzA := isZero_Habs_of_contractible R 1 (by omega) (TopCat.of A)
  have hzB := isZero_Habs_of_contractible R 1 (by omega) (TopCat.of B)
  have hk : mvSmallKappa R (X := TopCat.of (Sph (m+2))) A B 1 = 0 :=
    (isZero_mvSum R (X := TopCat.of (Sph (m+2))) A B 1 hzA hzB).eq_zero_of_src _
  letI : Mono (mvSmallDelta R (X := TopCat.of (Sph (m+2))) A B 0) :=
    (mvSmall_exact_kappa_delta R (X := TopCat.of (Sph (m+2))) A B 0).mono_g hk
  have hd : mvSmallDelta R (X := TopCat.of (Sph (m+2))) A B 0 = 0 :=
    (mvSmall_exact_delta_iota R (X := TopCat.of (Sph (m+2))) A B 0).mono_g_iff.mp hm
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (mvSmallDelta R (X := TopCat.of (Sph (m+2))) A B 0)).mp
  rw [hd, comp_zero, comp_zero]


end NRR.PrimePowerTopology
