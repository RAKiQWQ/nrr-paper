import NRR.PrimePowerTopologySphereOrientation

/-! The genuine single-coordinate reflection acts by minus one on the
actual relative fundamental class of each unit disk-boundary pair. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology Metric CategoryTheory Limits
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

def diskFirstReflectionMap (n : ℕ) : TopCat.of (UnitDisk n) ⟶ TopCat.of (UnitDisk n) :=
  TopCat.ofHom ⟨fun z => ⟨reflectFirstVector n z.val, by
    rw [mem_closedBall_zero_iff, norm_reflectFirstVector]
    exact mem_closedBall_zero_iff.mp z.property⟩,
    ((continuous_reflectFirstVector n).comp continuous_subtype_val).subtype_mk _⟩

theorem diskFirstReflection_pair_comm (n : ℕ) :
    diskBoundaryIncl n ≫ diskFirstReflectionMap n =
      sphereFirstReflectionMap n ≫ diskBoundaryIncl n := rfl

def diskFirstReflectionRelativeMap (R : Type) [Ring R] (n q : ℕ) :
    Hrel R q (diskBoundaryIncl n) ⟶ Hrel R q (diskBoundaryIncl n) :=
  HrelMap R q (diskBoundaryIncl n) (diskBoundaryIncl n) (diskFirstReflection_pair_comm n)

variable (R : Type) [Ring R]

theorem diskFirstReflection_relative_delta (n k : ℕ) :
    diskFirstReflectionRelativeMap R n (k+1) ≫ relδ R k (diskBoundaryIncl n) =
      relδ R k (diskBoundaryIncl n) ≫ HabsMap R k (sphereFirstReflectionMap n) :=
  (relδ_naturality R k (diskBoundaryIncl n) (diskBoundaryIncl n)
    (diskFirstReflection_pair_comm n)).symm

theorem diskFirstReflectionRelativeMap_top (n : ℕ) :
    diskFirstReflectionRelativeMap R n (n+1) = -𝟙 _ := by
  cases n with
  | zero =>
    let δ := relδ R 0 (diskBoundaryIncl 0)
    have hj : relJ R 1 (diskBoundaryIncl 0) = 0 :=
      (isZero_Habs_of_contractible R 1 (by omega)
        (TopCat.of (UnitDisk 0))).eq_zero_of_src _
    letI : Mono δ := (pair_exact_j_δ R 0 (diskBoundaryIncl 0)).mono_g hj
    have collapse : δ ≫
        HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) = 0 := by
      rw [← comp_homologyPointCollapse (diskBoundaryIncl 0), HabsMap_comp,
        ← Category.assoc]
      have hzero : δ ≫ HabsMap R 0 (diskBoundaryIncl 0) = 0 :=
        (relShortComplex_shortExact R (diskBoundaryIncl 0)).δ_comp 1 0 rfl
      rw [hzero, zero_comp]
    have negative : δ ≫ HabsMap R 0 (sphereFirstReflectionMap 0) = -δ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have hz := congrArg (fun g => g z) collapse
      change HabsMap R 0 (sphereFirstReflectionMap 0) (δ z) = -(δ z)
      rw [sphereFirstReflectionMap_zero]
      exact sphereZeroReducedHomology_antipodal R _ hz
    apply (cancel_mono δ).mp
    calc
      _ = δ ≫ HabsMap R 0 (sphereFirstReflectionMap 0) :=
        diskFirstReflection_relative_delta R 0 0
      _ = -δ := negative
      _ = _ := by simp
  | succ n =>
    letI : IsIso (relδ R (n+1) (diskBoundaryIncl (n+1))) :=
      isIso_relδ_of_contractible R (n+1) (by omega) (diskBoundaryIncl (n+1))
    apply (cancel_mono (relδ R (n+1) (diskBoundaryIncl (n+1)))).mp
    rw [diskFirstReflection_relative_delta, sphereFirstReflection_HabsMap_top]
    simp

theorem diskFundamentalClass_firstReflection (n : ℕ) :
    diskFirstReflectionRelativeMap R n (n+1) (diskFundamentalClass R n) =
      -diskFundamentalClass R n := by
  rw [diskFirstReflectionRelativeMap_top]
  rfl

end NRR.PrimePowerTopology
