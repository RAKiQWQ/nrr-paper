import NRR.PrimePowerTopologySphereHomology

/-! Actual relative singular homology of the closed unit disk and its boundary.
The disk in dimension n+1 and its boundary metric n-sphere are the genuine
subspaces of Euclidean space. The connecting maps, including the interval
case, freely generate the unique nonzero relative homology group. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology Metric CategoryTheory Limits AlgebraicTopology
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

abbrev UnitDisk (n : ℕ) := closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1

instance contractibleSpace_UnitDisk (n : ℕ) : ContractibleSpace (UnitDisk n) :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1).contractibleSpace
    ⟨0, mem_closedBall_self (by norm_num)⟩

/-- The actual boundary inclusion of the (n+1)-dimensional closed unit disk. -/
def diskBoundaryIncl (n : ℕ) : TopCat.of (Sph n) ⟶ TopCat.of (UnitDisk n) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

instance mono_diskBoundaryIncl (n : ℕ) : Mono (diskBoundaryIncl n) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  exact Subtype.ext (congrArg (fun z : UnitDisk n => z.val) h)

variable (R : Type) [Ring R]

/-- The ordinary connecting isomorphism in every degree at least two. -/
def diskBoundaryHomologyIso (n k : ℕ) :
    Hrel R (k+2) (diskBoundaryIncl n) ≅ Habs R (k+1) (TopCat.of (Sph n)) := by
  letI := isIso_relδ_of_contractible R (k+1) (by omega) (diskBoundaryIncl n)
  exact asIso (relδ R (k+1) (diskBoundaryIncl n))

theorem sphereZeroGenerator_comp_diskBoundary :
    sphereZeroGenerator R ≫ HabsMap R 0 (diskBoundaryIncl 0) = 0 := by
  letI : IsIso (HabsMap R 0 (homologyPointCollapse (TopCat.of (UnitDisk 0)))) := by
    change IsIso (HabsZeroCollapseIso R (TopCat.of (UnitDisk 0))).hom
    infer_instance
  apply (cancel_mono (HabsMap R 0
    (homologyPointCollapse (TopCat.of (UnitDisk 0))))).mp
  rw [zero_comp, Category.assoc, ← HabsMap_comp, comp_homologyPointCollapse,
    sphereZeroGenerator_collapse]

theorem sphereZeroGenerator_exact_diskBoundary :
    (ShortComplex.mk (sphereZeroGenerator R) (HabsMap R 0 (diskBoundaryIncl 0))
      (sphereZeroGenerator_comp_diskBoundary R)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hc : HabsMap R 0 (diskBoundaryIncl 0) ≫
      HabsMap R 0 (homologyPointCollapse (TopCat.of (UnitDisk 0))) =
      HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) := by
    rw [← HabsMap_comp, comp_homologyPointCollapse]
  have he := congrArg (fun f => f z) hc
  change HabsMap R 0 (homologyPointCollapse (TopCat.of (UnitDisk 0)))
    (HabsMap R 0 (diskBoundaryIncl 0) z) =
      HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) z at he
  rw [hz, map_zero] at he
  obtain ⟨r, hr, _⟩ := sphereZeroGenerator_kernel_existsUnique R z he.symm
  exact ⟨r, hr⟩

/-- In dimension one the pair connecting map has image the pole-difference
kernel. This gives the interval's generator without replacing H_0 by R. -/
def diskOneHomologyIso : Hrel R 1 (diskBoundaryIncl 0) ≅ ModuleCat.of R R := by
  have zeroDisk : IsZero (Habs R 1 (TopCat.of (UnitDisk 0))) :=
    isZero_Habs_of_contractible R 1 (by omega) _
  have hj : relJ R 1 (diskBoundaryIncl 0) = 0 := zeroDisk.eq_zero_of_src _
  letI : Mono (relδ R 0 (diskBoundaryIncl 0)) :=
    (pair_exact_j_δ R 0 (diskBoundaryIncl 0)).mono_g hj
  letI : Mono (sphereZeroGenerator R) :=
    mono_of_mono_fac (sphereZeroGenerator_northCoefficient R)
  exact IsLimit.conePointUniqueUpToIso
    (pair_exact_δ_iota R 0 (diskBoundaryIncl 0)).fIsKernel
    (sphereZeroGenerator_exact_diskBoundary R).fIsKernel

/-- The actual relative top homology is freely generated over every ring. -/
def diskTopHomologyIso (n : ℕ) :
    Hrel R (n+1) (diskBoundaryIncl n) ≅ ModuleCat.of R R := by
  cases n with
  | zero => exact diskOneHomologyIso R
  | succ n => exact diskBoundaryHomologyIso R (n+1) n ≪≫ sphereTopHomologyIso R n

theorem isZero_diskRelative_zero (n : ℕ) :
    IsZero (Hrel R 0 (diskBoundaryIncl n)) := by
  let f := HabsMap R 0 (homologyPointIncl (X := TopCat.of (Sph n)) (sphereBasepoint n))
  let g := HabsMap R 0 (diskBoundaryIncl n)
  let h := HabsMap R 0 (homologyPointIncl (X := TopCat.of (UnitDisk n)) (diskBoundaryIncl n (sphereBasepoint n)))
  have fac : f ≫ g = h := by
    rw [← HabsMap_comp]
    rfl
  letI : IsIso h := isIso_HabsMap_zero_of_pathConnected R _
  letI : Epi g := epi_of_epi_fac fac
  have hj : relJ R 0 (diskBoundaryIncl n) = 0 :=
    (pair_exact_iota_j R 0 (diskBoundaryIncl n)).epi_f_iff.mp (by
      change Epi g
      infer_instance)
  letI : Epi ((relProj R (diskBoundaryIncl n)).f 0) :=
    (relShortComplex_degreewise_shortExact R (diskBoundaryIncl n) 0).epi_g
  letI : Epi (relJ R 0 (diskBoundaryIncl n)) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
      (relProj R (diskBoundaryIncl n)) 0 (by intro j; simp)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (relJ R 0 (diskBoundaryIncl n))).mp
  rw [hj, zero_comp, zero_comp]

theorem isZero_diskRelative_one (n : ℕ) :
    IsZero (Hrel R 1 (diskBoundaryIncl (n+1))) := by
  letI : PathConnectedSpace (Sph (n+1)) := pathConnectedSpace_positiveSphere n
  letI : IsIso (HabsMap R 0 (diskBoundaryIncl (n+1))) :=
    isIso_HabsMap_zero_of_pathConnected R _
  have hj : relJ R 1 (diskBoundaryIncl (n+1)) = 0 :=
    (isZero_Habs_of_contractible R 1 (by omega)
      (TopCat.of (UnitDisk (n+1)))).eq_zero_of_src _
  letI : Mono (relδ R 0 (diskBoundaryIncl (n+1))) :=
    (pair_exact_j_δ R 0 (diskBoundaryIncl (n+1))).mono_g hj
  have hd : relδ R 0 (diskBoundaryIncl (n+1)) = 0 :=
    (pair_exact_δ_iota R 0 (diskBoundaryIncl (n+1))).mono_g_iff.mp inferInstance
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (relδ R 0 (diskBoundaryIncl (n+1)))).mp
  rw [hd, comp_zero, comp_zero]

/-- All off-top relative groups vanish, including degree zero and the
low-dimensional edge case, for every honest unit disk-boundary pair. -/
theorem isZero_diskRelative_off_top (q n : ℕ) (hqn : q ≠ n+1) :
    IsZero (Hrel R q (diskBoundaryIncl n)) := by
  match q, n with
  | 0, n => exact isZero_diskRelative_zero R n
  | 1, 0 => exact (hqn rfl).elim
  | 1, n+1 => exact isZero_diskRelative_one R n
  | k+2, n =>
    exact IsZero.of_iso
      (isZero_Habs_sphere_off_top R (k+1) n (by omega) (by omega))
      (diskBoundaryHomologyIso R n k)

def diskFundamentalGenerator (n : ℕ) :
    ModuleCat.of R R ⟶ Hrel R (n+1) (diskBoundaryIncl n) :=
  (diskTopHomologyIso R n).inv

def diskFundamentalClass (n : ℕ) : Hrel R (n+1) (diskBoundaryIncl n) :=
  diskFundamentalGenerator R n 1

theorem diskFundamentalGenerator_apply_eq_smul (n : ℕ) (r : R) :
    diskFundamentalGenerator R n r = r • diskFundamentalClass R n := by
  simpa [diskFundamentalClass] using (diskFundamentalGenerator R n).hom.map_smul r (1 : R)

theorem diskFundamentalClass_ne_zero [Nontrivial R] (n : ℕ) :
    diskFundamentalClass R n ≠ 0 := by
  have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
    (diskTopHomologyIso R n).inv_hom_id
  change (diskTopHomologyIso R n).hom (diskFundamentalClass R n) = 1 at h
  intro hz
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem diskFundamentalClass_existsUnique (n : ℕ)
    (z : Hrel R (n+1) (diskBoundaryIncl n)) :
    ∃! r : R, r • diskFundamentalClass R n = z := by
  let e := diskTopHomologyIso R n
  refine ⟨e.hom z, ?_, ?_⟩
  · change (e.hom z) • diskFundamentalClass R n = z
    rw [← diskFundamentalGenerator_apply_eq_smul]
    exact congrArg (fun f : Hrel R (n+1) (diskBoundaryIncl n) ⟶
      Hrel R (n+1) (diskBoundaryIncl n) => f z) e.hom_inv_id
  · intro r hr
    rw [← diskFundamentalGenerator_apply_eq_smul] at hr
    have h := congrArg e.hom hr
    have hleft := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f r) e.inv_hom_id
    exact hleft.symm.trans h

end NRR.PrimePowerTopology
