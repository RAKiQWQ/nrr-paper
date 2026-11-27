import NRR.PrimePowerTopologySphereSmall
import NRR.SingularHomologySmallQuasiIso

/-! Actual singular homology of every metric sphere, with arbitrary ring
coefficients, obtained from the proved small-chain comparison and the
two-cap Mayer-Vietoris connecting maps. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology CategoryTheory Limits AlgebraicTopology
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

variable (R : Type) [Ring R]

def sphereSmallComparisonIso (m k : ℕ) :
    (mvSmallComplex (R := R) (X := TopCat.of (Sph (m+1)))
      (sphLowerCap m) (sphUpperCap m)).homology k ≅
      Habs R k (TopCat.of (Sph (m+1))) := by
  letI := isIso_mvSmallIncl_homologyMap R (X := TopCat.of (Sph (m+1)))
    (sphLowerCap m) (sphUpperCap m) (sphCap_interior_union m) k
  exact asIso (HomologicalComplex.homologyMap
    (mvSmallIncl (R := R) (X := TopCat.of (Sph (m+1)))
      (sphLowerCap m) (sphUpperCap m)) k)

/-- The actual suspension step, with no small-chain comparison hypothesis. -/
def sphereStepIso (m k : ℕ) :
    Habs R (k+2) (TopCat.of (Sph (m+1))) ≅
      Habs R (k+1) (TopCat.of (Sph m)) :=
  (sphereSmallComparisonIso R m (k+2)).symm ≪≫ sphereSmallStepIso R m k

/-- The circle's actual first singular homology is the coefficient module. -/
def sphereOneHomologyIso :
    Habs R 1 (TopCat.of (Sph 1)) ≅ ModuleCat.of R R :=
  (sphereSmallComparisonIso R 0 1).symm ≪≫ sphereOneSmallHomologyIso R

theorem isZero_Habs_positiveSphere_one (m : ℕ) :
    IsZero (Habs R 1 (TopCat.of (Sph (m+2)))) :=
  IsZero.of_iso (isZero_sphereSmallHomology_one R m)
    (sphereSmallComparisonIso R (m+1) 1).symm

theorem isZero_Habs_sphere_above (k : ℕ) :
    ∀ n : ℕ, n < k → IsZero (Habs R k (TopCat.of (Sph n))) := by
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    match n, k with
    | 0, k => exact isZero_Habs_of_totallyDisconnected R (k+1) (by omega) _
    | _+1, 0 => omega
    | n+1, k+1 => exact IsZero.of_iso (ih n (by omega)) (sphereStepIso R n k)

theorem isZero_Habs_sphere_below (k : ℕ) :
    ∀ n : ℕ, 1 ≤ k → k < n → IsZero (Habs R k (TopCat.of (Sph n))) := by
  induction k with
  | zero => intro n hk; omega
  | succ k ih =>
    intro n hk hn
    match k, n with
    | 0, n+2 => exact isZero_Habs_positiveSphere_one R n
    | 0, 0 => omega
    | 0, 1 => omega
    | k+1, 0 => omega
    | k+1, n+1 => exact IsZero.of_iso (ih n (by omega) (by omega)) (sphereStepIso R n k)

/-- Every actual positive-degree sphere homology group off the top degree vanishes. -/
theorem isZero_Habs_sphere_off_top (k n : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (Habs R k (TopCat.of (Sph n))) := by
  rcases lt_or_gt_of_ne hkn with h | h
  · exact isZero_Habs_sphere_below R k n (Nat.one_le_iff_ne_zero.mpr hk) h
  · exact isZero_Habs_sphere_above R k n h

/-- The actual top homology of every positive-dimensional metric sphere. -/
def sphereTopHomologyIso (n : ℕ) :
    Habs R (n+1) (TopCat.of (Sph (n+1))) ≅ ModuleCat.of R R := by
  induction n with
  | zero => exact sphereOneHomologyIso R
  | succ n ih => exact sphereStepIso R (n+1) n ≪≫ ih

def sphereFundamentalGenerator (n : ℕ) :
    ModuleCat.of R R ⟶ Habs R (n+1) (TopCat.of (Sph (n+1))) :=
  (sphereTopHomologyIso R n).inv

def sphereFundamentalClass (n : ℕ) : Habs R (n+1) (TopCat.of (Sph (n+1))) :=
  sphereFundamentalGenerator R n 1

theorem sphereFundamentalGenerator_apply_eq_smul (n : ℕ) (r : R) :
    sphereFundamentalGenerator R n r = r • sphereFundamentalClass R n := by
  simpa [sphereFundamentalClass] using (sphereFundamentalGenerator R n).hom.map_smul r (1 : R)

theorem sphereFundamentalClass_ne_zero [Nontrivial R] (n : ℕ) :
    sphereFundamentalClass R n ≠ 0 := by
  have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
    (sphereTopHomologyIso R n).inv_hom_id
  change (sphereTopHomologyIso R n).hom (sphereFundamentalClass R n) = 1 at h
  intro hz
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- The genuine top fundamental class freely generates every actual top
singular homology class, not an abstract replacement chain group. -/
theorem sphereFundamentalClass_existsUnique (n : ℕ)
    (z : Habs R (n+1) (TopCat.of (Sph (n+1)))) :
    ∃! r : R, r • sphereFundamentalClass R n = z := by
  let e := sphereTopHomologyIso R n
  refine ⟨e.hom z, ?_, ?_⟩
  · change (e.hom z) • sphereFundamentalClass R n = z
    rw [← sphereFundamentalGenerator_apply_eq_smul]
    exact congrArg (fun f : Habs R (n+1) (TopCat.of (Sph (n+1))) ⟶
      Habs R (n+1) (TopCat.of (Sph (n+1))) => f z) e.hom_inv_id
  · intro r hr
    rw [← sphereFundamentalGenerator_apply_eq_smul] at hr
    have h := congrArg e.hom hr
    have hleft := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f r) e.inv_hom_id
    exact hleft.symm.trans h

end NRR.PrimePowerTopology
