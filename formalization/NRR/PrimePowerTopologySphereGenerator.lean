import NRR.PrimePowerTopologySphereZeroHomology
import NRR.TopologyPort.SphereCaps

/-! The generator of the reduced zeroth singular homology of the actual
metric zero-sphere, with arbitrary ring coefficients. -/

noncomputable section

set_option maxHeartbeats 800000

open Set Topology Metric CategoryTheory Limits AlgebraicTopology
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

local instance sphereGeneratorPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The positive pole of the actual unit sphere in one-dimensional Euclidean space. -/
def sphereZeroNorth : Sph 0 := sphereBasepoint 0

/-- The negative pole of the actual unit sphere in one-dimensional Euclidean space. -/
def sphereZeroSouth : Sph 0 :=
  ⟨-(sphereZeroNorth : EuclideanSpace ℝ (Fin 1)), by
    simpa only [mem_sphere_zero_iff_norm, norm_neg] using sphereZeroNorth.property⟩

@[simp] theorem sphereZeroNorth_coordinate :
    (sphereZeroNorth : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  simp [sphereZeroNorth, sphereBasepoint]

@[simp] theorem sphereZeroSouth_coordinate :
    (sphereZeroSouth : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  simp [sphereZeroSouth]

theorem sphereZeroNorth_ne_south : sphereZeroNorth ≠ sphereZeroSouth := by
  intro h
  have := congrArg (fun z : Sph 0 => (z : EuclideanSpace ℝ (Fin 1)) 0) h
  norm_num at this

/-- The actual metric zero-sphere consists of its two poles. -/
theorem sphereZero_eq_north_or_south (z : Sph 0) :
    z = sphereZeroNorth ∨ z = sphereZeroSouth := by
  have hz : ‖(z : EuclideanSpace ℝ (Fin 1))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp z.property
  have hsq : ((z : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq (z : EuclideanSpace ℝ (Fin 1))
    simpa [hz, Real.norm_eq_abs, sq_abs] using h.symm
  have hc : (z : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨
      (z : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    exact sq_eq_one_iff.mp hsq
  rcases hc with hc | hc
  · left
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    simpa using hc
  · right
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    simpa using hc

instance instFiniteSphereZero : Finite (Sph 0) := by
  apply Finite.of_surjective (fun b : Bool => if b then sphereZeroNorth else sphereZeroSouth)
  intro z
  rcases sphereZero_eq_north_or_south z with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

/-- The genuine antipodal homeomorphism of the metric sphere. -/
def sphereAntipodalHomeo (n : ℕ) : Sph n ≃ₜ Sph n where
  toFun z := ⟨-z.val, by simpa only [mem_sphere_zero_iff_norm, norm_neg] using z.property⟩
  invFun z := ⟨-z.val, by simpa only [mem_sphere_zero_iff_norm, norm_neg] using z.property⟩
  left_inv z := Subtype.ext (neg_neg z.val)
  right_inv z := Subtype.ext (neg_neg z.val)
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _

@[simp] theorem sphereAntipodalHomeo_north :
    sphereAntipodalHomeo 0 sphereZeroNorth = sphereZeroSouth := rfl

@[simp] theorem sphereAntipodalHomeo_south :
    sphereAntipodalHomeo 0 sphereZeroSouth = sphereZeroNorth :=
  Subtype.ext (neg_neg _)

/-- The antipodal map, as a morphism of actual topological spaces. -/
def sphereAntipodalMap (n : ℕ) : TopCat.of (Sph n) ⟶ TopCat.of (Sph n) :=
  TopCat.ofHom ⟨sphereAntipodalHomeo n, (sphereAntipodalHomeo n).continuous_toFun⟩

variable (R : Type) [Ring R]

/-- The difference of the two normalized point classes in actual singular homology. -/
def sphereZeroGenerator : ModuleCat.of R R ⟶ Habs R 0 (TopCat.of (Sph 0)) :=
  homologyPointClass R _ sphereZeroNorth - homologyPointClass R _ sphereZeroSouth

theorem sphereZeroGenerator_ne_zero [Nontrivial R] : sphereZeroGenerator R ≠ 0 :=
  pointClass_sub_ne_zero R _ _ _ sphereZeroNorth_ne_south

/-- Antipodal reflection acts by minus one on the pole-difference class. -/
theorem sphereZeroGenerator_antipodal :
    sphereZeroGenerator R ≫ HabsMap R 0 (sphereAntipodalMap 0) =
      -sphereZeroGenerator R := by
  unfold sphereZeroGenerator
  rw [Preadditive.sub_comp, homologyPointClass_naturality, homologyPointClass_naturality]
  rw [show sphereAntipodalMap 0 sphereZeroNorth = sphereZeroSouth from sphereAntipodalHomeo_north,
    show sphereAntipodalMap 0 sphereZeroSouth = sphereZeroNorth from sphereAntipodalHomeo_south]
  exact (neg_sub _ _).symm

/-- Extract the coefficient of a point in the canonical basis of discrete zeroth homology. -/
def discreteHomologyCoefficient (X : TopCat.{0}) [TotallyDisconnectedSpace X] (x : X) :
    Habs R 0 X ⟶ ModuleCat.of R R :=
  (HabsZeroDiscreteIso R X).hom ≫ freePointEvaluation R X x

@[reassoc (attr := simp)]
theorem homologyPointClass_coefficient (X : TopCat.{0}) [TotallyDisconnectedSpace X]
    (x y : X) :
    homologyPointClass R X y ≫ discreteHomologyCoefficient R X x =
      if y = x then 𝟙 (ModuleCat.of R R) else 0 :=
  pointClass_evaluation R X x y

/-- On a two-point space every actual zeroth homology class is the sum of its two coordinates. -/
theorem twoPoint_homology_decomposition (X : TopCat.{0}) [TotallyDisconnectedSpace X]
    (x y : X) (hne : x ≠ y) (hxy : ∀ z : X, z = x ∨ z = y) :
    discreteHomologyCoefficient R X x ≫ homologyPointClass R X x +
      discreteHomologyCoefficient R X y ≫ homologyPointClass R X y = 𝟙 (Habs R 0 X) := by
  classical
  apply (cancel_epi (HabsZeroDiscreteIso R X).inv).mp
  apply Sigma.hom_ext
  intro z
  rcases hxy z with rfl | rfl <;>
    simp [discreteHomologyCoefficient, homologyPointClass_eq_discrete,
      discretePointClass, freePointEvaluation, Category.assoc, hne, Ne.symm hne]

/-- The scalar augmentation is the sum of the two point coordinates. -/
theorem twoPoint_homology_augmentation (X : TopCat.{0}) [TotallyDisconnectedSpace X]
    (x y : X) (hne : x ≠ y) (hxy : ∀ z : X, z = x ∨ z = y) :
    HabsMap R 0 (homologyPointCollapse X) ≫
        discreteHomologyCoefficient R (TopCat.of Unit) () =
      discreteHomologyCoefficient R X x + discreteHomologyCoefficient R X y := by
  conv_lhs => rw [← Category.id_comp (HabsMap R 0 (homologyPointCollapse X))]
  rw [← twoPoint_homology_decomposition R X x y hne hxy]
  simp only [Preadditive.add_comp, Category.assoc, homologyPointClass_naturality]
  simp [homologyPointCollapse]

/-- The pole-difference lies in the kernel of the actual map to the one-point space. -/
theorem sphereZeroGenerator_collapse :
    sphereZeroGenerator R ≫ HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) = 0 := by
  unfold sphereZeroGenerator
  rw [Preadditive.sub_comp, homologyPointClass_naturality, homologyPointClass_naturality]
  exact sub_self _

@[reassoc (attr := simp)]
theorem sphereZeroGenerator_northCoefficient :
    sphereZeroGenerator R ≫ discreteHomologyCoefficient R (TopCat.of (Sph 0)) sphereZeroNorth =
      𝟙 (ModuleCat.of R R) := by
  classical
  unfold sphereZeroGenerator
  rw [Preadditive.sub_comp, homologyPointClass_coefficient, homologyPointClass_coefficient]
  simp [Ne.symm sphereZeroNorth_ne_south]

/-- Every element killed by the actual map to a point is a unique pole-difference multiple. -/
theorem sphereZeroGenerator_kernel_existsUnique
    (z : Habs R 0 (TopCat.of (Sph 0)))
    (hz : HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) z = 0) :
    ∃! r : R, sphereZeroGenerator R r = z := by
  let a := discreteHomologyCoefficient R (TopCat.of (Sph 0)) sphereZeroNorth
  let b := discreteHomologyCoefficient R (TopCat.of (Sph 0)) sphereZeroSouth
  have hab : a z + b z = 0 := by
    have h := congrArg (fun f : Habs R 0 (TopCat.of (Sph 0)) ⟶ ModuleCat.of R R => f z)
      (twoPoint_homology_augmentation R (TopCat.of (Sph 0))
        sphereZeroNorth sphereZeroSouth sphereZeroNorth_ne_south sphereZero_eq_north_or_south)
    change discreteHomologyCoefficient R (TopCat.of Unit) ()
      (HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) z) = a z + b z at h
    simpa [hz] using h.symm
  have hb : b z = -(a z) := eq_neg_of_add_eq_zero_right hab
  have hdec : homologyPointClass R (TopCat.of (Sph 0)) sphereZeroNorth (a z) +
      homologyPointClass R (TopCat.of (Sph 0)) sphereZeroSouth (b z) = z :=
    congrArg (fun f : Habs R 0 (TopCat.of (Sph 0)) ⟶ Habs R 0 (TopCat.of (Sph 0)) => f z)
      (twoPoint_homology_decomposition R (TopCat.of (Sph 0))
        sphereZeroNorth sphereZeroSouth sphereZeroNorth_ne_south sphereZero_eq_north_or_south)
  refine ⟨a z, ?_, ?_⟩
  · simpa [sphereZeroGenerator, hb, sub_eq_add_neg] using hdec
  · intro r hr
    have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f r)
      (sphereZeroGenerator_northCoefficient R)
    change a (sphereZeroGenerator R r) = r at h
    exact h.symm.trans (congrArg a hr)

/-- Reduced zeroth homology, realized as the kernel of the actual map to a point. -/
abbrev sphereZeroReducedHomology :=
  LinearMap.ker (HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0)))).hom

/-- The generator map into reduced zeroth homology. -/
def sphereZeroGeneratorToKernel : R →ₗ[R] sphereZeroReducedHomology R :=
  (sphereZeroGenerator R).hom.codRestrict _ fun r => by
    have h := congrArg (fun f : ModuleCat.of R R ⟶ Habs R 0 (TopCat.of Unit) => f r)
      (sphereZeroGenerator_collapse R)
    exact h

/-- Actual reduced zeroth singular homology of the metric zero-sphere is the coefficient module. -/
def sphereZeroReducedHomologyEquiv : R ≃ₗ[R] sphereZeroReducedHomology R :=
  LinearEquiv.ofBijective (sphereZeroGeneratorToKernel R) (by
    constructor
    · intro r s h
      have h' := congrArg Subtype.val h
      exact (sphereZeroGenerator_kernel_existsUnique R (sphereZeroGenerator R s)
        (by
          have hs := (sphereZeroGeneratorToKernel R s).property
          exact hs)).unique h' rfl
    · intro z
      obtain ⟨r, hr, _⟩ := sphereZeroGenerator_kernel_existsUnique R z.val z.property
      exact ⟨r, Subtype.ext hr⟩)

@[simp] theorem sphereZeroReducedHomologyEquiv_apply (r : R) :
    ((sphereZeroReducedHomologyEquiv R r : sphereZeroReducedHomology R) :
      Habs R 0 (TopCat.of (Sph 0))) = sphereZeroGenerator R r := rfl

/-- The corresponding genuine isomorphism in the category of coefficient modules. -/
def sphereZeroReducedHomologyIso :
    ModuleCat.of R R ≅ ModuleCat.of R (sphereZeroReducedHomology R) :=
  (sphereZeroReducedHomologyEquiv R).toModuleIso

/-- The normalized fundamental class `[north] - [south]` as an element. -/
def sphereZeroFundamentalClass : Habs R 0 (TopCat.of (Sph 0)) :=
  sphereZeroGenerator R 1

theorem sphereZeroFundamentalClass_ne_zero [Nontrivial R] :
    sphereZeroFundamentalClass R ≠ 0 := by
  intro hz
  have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
    (sphereZeroGenerator_northCoefficient R)
  change discreteHomologyCoefficient R (TopCat.of (Sph 0)) sphereZeroNorth
    (sphereZeroFundamentalClass R) = 1 at h
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem sphereZeroGenerator_apply_eq_smul (r : R) :
    sphereZeroGenerator R r = r • sphereZeroFundamentalClass R := by
  simpa [sphereZeroFundamentalClass] using (sphereZeroGenerator R).hom.map_smul r (1 : R)

/-- The fundamental class freely generates the kernel, in the usual scalar-multiple formulation. -/
theorem sphereZeroFundamentalClass_kernel_existsUnique
    (z : Habs R 0 (TopCat.of (Sph 0)))
    (hz : HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) z = 0) :
    ∃! r : R, r • sphereZeroFundamentalClass R = z := by
  obtain ⟨r, hr, hu⟩ := sphereZeroGenerator_kernel_existsUnique R z hz
  refine ⟨r, (sphereZeroGenerator_apply_eq_smul R r).symm.trans hr, ?_⟩
  intro s hs
  exact hu s ((sphereZeroGenerator_apply_eq_smul R s).trans hs)

/-- The antipodal action on every scalar multiple of the fundamental class. -/
theorem sphereZeroGenerator_antipodal_apply (r : R) :
    HabsMap R 0 (sphereAntipodalMap 0) (sphereZeroGenerator R r) =
      -(sphereZeroGenerator R r) :=
  congrArg (fun f : ModuleCat.of R R ⟶ Habs R 0 (TopCat.of (Sph 0)) => f r)
    (sphereZeroGenerator_antipodal R)

theorem sphereZeroFundamentalClass_antipodal :
    HabsMap R 0 (sphereAntipodalMap 0) (sphereZeroFundamentalClass R) =
      -sphereZeroFundamentalClass R :=
  sphereZeroGenerator_antipodal_apply R 1

/-- On the whole actual reduced zeroth homology the antipodal action is minus the identity. -/
theorem sphereZeroReducedHomology_antipodal
    (z : Habs R 0 (TopCat.of (Sph 0)))
    (hz : HabsMap R 0 (homologyPointCollapse (TopCat.of (Sph 0))) z = 0) :
    HabsMap R 0 (sphereAntipodalMap 0) z = -z := by
  obtain ⟨r, rfl, _⟩ := sphereZeroGenerator_kernel_existsUnique R z hz
  exact sphereZeroGenerator_antipodal_apply R r

end NRR.PrimePowerTopology
