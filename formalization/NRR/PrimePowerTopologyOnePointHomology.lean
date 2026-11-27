import NRR.PrimePowerTopologySphereHomology
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-! Genuine fundamental classes of one-point compactified real vector
spaces and their pairs with the actual point at infinity. All relative
comparisons are the canonical maps of the singular pair sequence. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.SingularHomology NRR.SphereGeometry

namespace NRR.PrimePowerTopology

instance mono_homologyPointIncl {X : TopCat.{0}} (x : X) :
    Mono (homologyPointIncl x) := by
  rw [TopCat.mono_iff_injective]
  intro a b _
  exact Subsingleton.elim a b

variable (R : Type) [Ring R]

/-- The inclusion of a point is split injective on actual zeroth homology,
without any connectedness assumption on the ambient space. -/
theorem mono_HabsMap_pointIncl_zero {X : TopCat.{0}} (x : X) :
    Mono (HabsMap R 0 (homologyPointIncl x)) := by
  have h : HabsMap R 0 (homologyPointIncl x) ≫
      HabsMap R 0 (homologyPointCollapse X) = 𝟙 _ := by
    rw [← HabsMap_comp]
    convert HabsMap_id R 0 (TopCat.of Unit) using 1
  exact mono_of_mono_fac h

/-- Every point-pair connecting map is zero, including its degree-zero
target. The latter uses the split injection on H_0, rather than a false
vanishing assertion for H_0 of the point. -/
theorem relδ_point_eq_zero (k : ℕ) {X : TopCat.{0}} (x : X) :
    relδ R k (homologyPointIncl x) = 0 := by
  cases k with
  | zero =>
    letI := mono_HabsMap_pointIncl_zero R x
    exact (pair_exact_δ_iota R 0 (homologyPointIncl x)).mono_g_iff.mp
      (by change Mono (HabsMap R 0 (homologyPointIncl x)); infer_instance)
  | succ k =>
    exact (isZero_Habs_of_contractible R (k+1) (by omega)
      (TopCat.of Unit)).eq_zero_of_tgt _

/-- Actual absolute and point-relative homology agree canonically in
every positive degree, including degree one. -/
def pointRelativePositiveIso (k : ℕ) {X : TopCat.{0}} (x : X) :
    Habs R (k+1) X ≅ Hrel R (k+1) (homologyPointIncl x) := by
  have hi : relIota R (k+1) (homologyPointIncl x) = 0 :=
    (isZero_Habs_of_contractible R (k+1) (by omega)
      (TopCat.of Unit)).eq_zero_of_src _
  letI : Mono (relJ R (k+1) (homologyPointIncl x)) :=
    (pair_exact_iota_j R (k+1) (homologyPointIncl x)).mono_g hi
  letI : Epi (relJ R (k+1) (homologyPointIncl x)) :=
    (pair_exact_j_δ R k (homologyPointIncl x)).epi_f (relδ_point_eq_zero R k x)
  letI : IsIso (relJ R (k+1) (homologyPointIncl x)) := isIso_of_mono_of_epi _
  exact asIso (relJ R (k+1) (homologyPointIncl x))

@[simp] theorem pointRelativePositiveIso_hom (k : ℕ) {X : TopCat.{0}} (x : X) :
    (pointRelativePositiveIso R k x).hom = relJ R (k+1) (homologyPointIncl x) := rfl

section VectorSpace

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The actual one-point compactification of any finite-dimensional real
normed vector space is the metric sphere of its precise real dimension. -/
def vectorOnePointSphere (q : ℕ) (hdim : Module.finrank ℝ V = q) :
    OnePoint V ≃ₜ Sph q :=
  onePointEquivSphereOfFinrankEq (by simp [hdim])

def vectorOnePointHomologyIso (q k : ℕ) (hdim : Module.finrank ℝ V = q) :
    Habs R k (TopCat.of (OnePoint V)) ≅ Habs R k (TopCat.of (Sph q)) :=
  HabsIsoOfHomotopyEquiv R k (vectorOnePointSphere V q hdim).toHomotopyEquiv

/-- Top singular homology of the actual compactification, over every ring. -/
def vectorOnePointTopHomologyIso (q : ℕ) (hdim : Module.finrank ℝ V = q)
    (hq : 0 < q) : Habs R q (TopCat.of (OnePoint V)) ≅ ModuleCat.of R R := by
  cases q with
  | zero => omega
  | succ q => exact vectorOnePointHomologyIso R V (q+1) (q+1) hdim ≪≫
      sphereTopHomologyIso R q

theorem isZero_vectorOnePoint_off_top (q k : ℕ) (hdim : Module.finrank ℝ V = q)
    (hk : k ≠ 0) (hkq : k ≠ q) :
    IsZero (Habs R k (TopCat.of (OnePoint V))) :=
  IsZero.of_iso (isZero_Habs_sphere_off_top R k q hk hkq)
    (vectorOnePointHomologyIso R V q k hdim)

def vectorOnePointFundamentalGenerator (q : ℕ) (hdim : Module.finrank ℝ V = q)
    (hq : 0 < q) : ModuleCat.of R R ⟶ Habs R q (TopCat.of (OnePoint V)) :=
  (vectorOnePointTopHomologyIso R V q hdim hq).inv

def vectorOnePointFundamentalClass (q : ℕ) (hdim : Module.finrank ℝ V = q)
    (hq : 0 < q) : Habs R q (TopCat.of (OnePoint V)) :=
  vectorOnePointFundamentalGenerator R V q hdim hq 1

theorem vectorOnePointFundamentalClass_ne_zero [Nontrivial R]
    (q : ℕ) (hdim : Module.finrank ℝ V = q) (hq : 0 < q) :
    vectorOnePointFundamentalClass R V q hdim hq ≠ 0 := by
  have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
    (vectorOnePointTopHomologyIso R V q hdim hq).inv_hom_id
  change (vectorOnePointTopHomologyIso R V q hdim hq).hom
    (vectorOnePointFundamentalClass R V q hdim hq) = 1 at h
  intro hz
  rw [hz,map_zero] at h
  exact zero_ne_one h

/-- The actual inclusion of the point at infinity. -/
def vectorInfinityIncl : TopCat.of Unit ⟶ TopCat.of (OnePoint V) :=
  homologyPointIncl ∞

instance mono_vectorInfinityIncl : Mono (vectorInfinityIncl V) :=
  mono_homologyPointIncl _

/-- Absolute to infinity-relative comparison, with no missing circle case. -/
def vectorInfinityRelativeIso (k : ℕ) :
    Habs R (k+1) (TopCat.of (OnePoint V)) ≅ Hrel R (k+1) (vectorInfinityIncl V) :=
  pointRelativePositiveIso R k (X := TopCat.of (OnePoint V)) (∞ : OnePoint V)

def vectorInfinityRelativeTopHomologyIso (q : ℕ) (hdim : Module.finrank ℝ V = q)
    (hq : 0 < q) : Hrel R q (vectorInfinityIncl V) ≅ ModuleCat.of R R := by
  cases q with
  | zero => omega
  | succ q => exact (vectorInfinityRelativeIso R V q).symm ≪≫
      vectorOnePointTopHomologyIso R V (q+1) hdim hq

def vectorInfinityFundamentalGenerator (q : ℕ) (hdim : Module.finrank ℝ V = q)
    (hq : 0 < q) : ModuleCat.of R R ⟶ Hrel R q (vectorInfinityIncl V) :=
  (vectorInfinityRelativeTopHomologyIso R V q hdim hq).inv

def vectorInfinityFundamentalClass (q : ℕ) (hdim : Module.finrank ℝ V = q)
    (hq : 0 < q) : Hrel R q (vectorInfinityIncl V) :=
  vectorInfinityFundamentalGenerator R V q hdim hq 1

theorem vectorInfinityFundamentalClass_eq_relJ (q : ℕ)
    (hdim : Module.finrank ℝ V = q) (hq : 0 < q) :
    vectorInfinityFundamentalClass R V q hdim hq =
      relJ R q (vectorInfinityIncl V) (vectorOnePointFundamentalClass R V q hdim hq) := by
  cases q with
  | zero => omega
  | succ q => rfl

theorem vectorInfinityFundamentalClass_ne_zero [Nontrivial R]
    (q : ℕ) (hdim : Module.finrank ℝ V = q) (hq : 0 < q) :
    vectorInfinityFundamentalClass R V q hdim hq ≠ 0 := by
  have h := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
    (vectorInfinityRelativeTopHomologyIso R V q hdim hq).inv_hom_id
  change (vectorInfinityRelativeTopHomologyIso R V q hdim hq).hom
    (vectorInfinityFundamentalClass R V q hdim hq) = 1 at h
  intro hz
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem vectorInfinityFundamentalClass_existsUnique
    (q : ℕ) (hdim : Module.finrank ℝ V = q) (hq : 0 < q)
    (z : Hrel R q (vectorInfinityIncl V)) :
    ∃! r : R, r • vectorInfinityFundamentalClass R V q hdim hq = z := by
  let e := vectorInfinityRelativeTopHomologyIso R V q hdim hq
  have scalar (r : R) : vectorInfinityFundamentalGenerator R V q hdim hq r =
      r • vectorInfinityFundamentalClass R V q hdim hq := by
    simpa [vectorInfinityFundamentalClass] using
      (vectorInfinityFundamentalGenerator R V q hdim hq).hom.map_smul r (1 : R)
  refine ⟨e.hom z,?_,?_⟩
  · change (e.hom z) • vectorInfinityFundamentalClass R V q hdim hq = z
    rw [← scalar]
    exact congrArg (fun f : Hrel R q (vectorInfinityIncl V) ⟶
      Hrel R q (vectorInfinityIncl V) => f z) e.hom_inv_id
  · intro r hr
    rw [← scalar] at hr
    have h := congrArg e.hom hr
    have hleft := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f r) e.inv_hom_id
    exact hleft.symm.trans h

end VectorSpace
end NRR.PrimePowerTopology
