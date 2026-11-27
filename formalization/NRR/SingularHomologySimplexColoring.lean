import NRR.SingularHomologySimplexFundamental
import NRR.SingularHomologySmallQuasiIso
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A concrete barycentric coloring and its determinant cocycle. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open NRR.SingularHomology.SimplexGeometry

namespace NRR.SingularHomology.SimplexFundamental

theorem exists_large_coordinate {n : ℕ} (x : GeometricSimplex n) :
    ∃ i : Fin (n+1), (1 : ℝ) / (n+1) ≤ (x i : ℝ) := by
  by_contra h
  push_neg at h
  have hs : ∑ i : Fin (n+1), (x i : ℝ) < ∑ _i : Fin (n+1), (1 : ℝ)/(n+1) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h i)
  have hx : ∑ i : Fin (n+1), (x i : ℝ) = 1 := by
    exact_mod_cast x.property
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hs
  rw [hx] at hs
  have hp : (n+1 : ℝ) ≠ 0 := by positivity
  rw [mul_one_div_cancel hp] at hs
  exact lt_irrefl _ hs

def barycentricColor {n : ℕ} (x : GeometricSimplex n) : Fin (n+1) :=
  (exists_large_coordinate x).choose

theorem barycentricColor_large {n : ℕ} (x : GeometricSimplex n) :
    (1 : ℝ)/(n+1) ≤ (x (barycentricColor x) : ℝ) :=
  (exists_large_coordinate x).choose_spec

theorem barycentricColor_ne_of_small {n : ℕ} (x : GeometricSimplex n) (i : Fin (n+1))
    (hi : (x i : ℝ) < (1 : ℝ)/(n+1)) : barycentricColor x ≠ i := by
  intro he
  have h := barycentricColor_large x
  rw [he] at h
  exact (not_lt_of_ge h) hi

@[simp] theorem barycentricColor_vertex (n : ℕ) (i : Fin (n+1)) :
    barycentricColor (vertex n i) = i := by
  by_contra h
  have hc := barycentricColor_large (vertex n i)
  simp only [vertex_apply, if_neg h, NNReal.coe_zero] at hc
  have hp : 0 < (1 : ℝ)/(n+1) := by positivity
  exact (not_lt_of_ge hc) hp

variable (R : Type) [CommRing R]

def colorOrientation {n : ℕ} (v : Fin (n+1) → Fin (n+1)) : R :=
  Matrix.det (fun i j => if v j = i then (1 : R) else 0)

@[simp] theorem colorOrientation_id (n : ℕ) : colorOrientation R (id : Fin (n+1) → Fin (n+1)) = 1 := by
  have h : (fun i j : Fin (n+1) => if id j = i then (1 : R) else 0) =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) R) := by
    ext i j
    simp [Matrix.one_apply, eq_comm]
  rw [colorOrientation, h, Matrix.det_one]

theorem colorOrientation_eq_zero_of_omitted {n : ℕ}
    (v : Fin (n+1) → Fin (n+1)) (i : Fin (n+1)) (hi : ∀ j, v j ≠ i) :
    colorOrientation R v = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  simp [hi j]

theorem colorOrientation_cocycle {n : ℕ} (v : Fin (n+2) → Fin (n+1)) :
    (∑ i : Fin (n+2), (-1 : R)^i.val * colorOrientation R (fun j => v (i.succAbove j))) = 0 := by
  classical
  let A : Matrix (Fin (n+2)) (Fin (n+2)) R :=
    fun i j => Fin.cases 1 (fun k => if v j = k then 1 else 0) i
  let c : Fin (n+2) → R := Fin.cases 0 (fun _ => 1)
  have hrow : (∑ i, c i • A i) = A 0 := by
    ext j
    simp [c, A, Fin.sum_univ_succ]
  have hz : Matrix.det A = 0 := by
    have h := Matrix.det_updateRow_sum A 0 c
    rw [hrow, Matrix.updateRow_eq_self] at h
    simpa [c] using h
  rw [Matrix.det_succ_row_zero] at hz
  simpa only [A, Fin.cases_zero, mul_one, Matrix.submatrix_apply, Fin.cases_succ,
    colorOrientation] using hz

def simplexVertexColors {m n : ℕ}
    (s : (TopCat.toSSet.obj (TopCat.of (GeometricSimplex n))).obj (op ⦋m⦌)) :
    Fin (m+1) → Fin (n+1) :=
  fun i => barycentricColor (TopCat.toSSetObjEquiv _ _ s (vertex m i))

theorem simplexVertexColors_delta {m n : ℕ}
    (s : (TopCat.toSSet.obj (TopCat.of (GeometricSimplex n))).obj (op ⦋m+1⦌))
    (i : Fin (m+2)) :
    simplexVertexColors ((TopCat.toSSet.obj (TopCat.of (GeometricSimplex n))).δ i s) =
      fun j => simplexVertexColors s (i.succAbove j) := by
  funext j
  apply congrArg barycentricColor
  change TopCat.toSSetObjEquiv _ _ s
    (SimplexCategory.toTopMap (SimplexCategory.δ i) (vertex m j)) = _
  congr 1
  apply Subtype.ext
  funext k
  have hδ : (SimplexCategory.δ i) j = i.succAbove j := rfl
  simp [SimplexCategory.coe_toTopMap, vertex, Pi.single_apply, eq_comm]
  rfl

def coloringCochain (n : ℕ) : (Csing R (TopCat.of (GeometricSimplex n))).X n ⟶ ModuleCat.of R R :=
  ccDesc R fun s => ModuleCat.ofHom ((colorOrientation R (simplexVertexColors s)) • LinearMap.id)

@[simp] theorem simplexι_coloringCochain (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of (GeometricSimplex n))).obj (op ⦋n⦌)) :
    simplexι R s ≫ coloringCochain R n =
      ModuleCat.ofHom ((colorOrientation R (simplexVertexColors s)) • LinearMap.id) :=
  ι_ccDesc R _ s

theorem coloringCochain_cocycle (n : ℕ) :
    (Csing R (TopCat.of (GeometricSimplex n))).d (n+1) n ≫ coloringCochain R n = 0 := by
  apply simplicialChain_hom_ext R
  intro s
  change simplexι R s ≫ (CsingSSet R (TopCat.toSSet.obj (TopCat.of (GeometricSimplex n)))).d (n+1) n ≫
    coloringCochain R n = simplexι R s ≫ 0
  rw [simplexι_d_assoc, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, simplexι_coloringCochain, comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, ModuleCat.hom_ofHom, LinearMap.id_apply, smul_eq_mul, mul_one,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  change (∑ i : Fin (n+2), (-1 : ℤ)^i.val •
    colorOrientation R (simplexVertexColors ((TopCat.toSSet.obj (TopCat.of (GeometricSimplex n))).δ i s))) = 0
  simp only [simplexVertexColors_delta, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact colorOrientation_cocycle R (simplexVertexColors s)

@[simp] theorem identityChain_coloringCochain (n : ℕ) :
    identityChain R n ≫ coloringCochain R n = 𝟙 _ := by
  rw [identityChain, simplexι_coloringCochain]
  have h : simplexVertexColors (identitySingularSimplex n) = id := by
    funext i
    exact barycentricColor_vertex n i
  simp only [h, colorOrientation_id, one_smul]
  rfl

end NRR.SingularHomology.SimplexFundamental
