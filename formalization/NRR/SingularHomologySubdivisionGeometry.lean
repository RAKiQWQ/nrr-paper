/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NRR.SingularHomologySimplicial
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Concrete affine barycentric maps on Mathlib 4.24's actual topological
simplices. These maps use the same `toTopObj` as `TopCat.toSSet`.
-/
noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped NNReal
namespace NRR.SingularHomology.SimplexGeometry

abbrev Simplex (n : ℕ) := SimplexCategory.toTopObj ⦋n⦌

/-- The `i`th actual vertex of the standard topological simplex. -/
def vertex (n : ℕ) (i : Fin (n + 1)) : Simplex n :=
  ⟨Pi.single i 1, by
    change ∑ j : Fin (n + 1), Pi.single i (1 : ℝ≥0) j = 1
    simp⟩

@[simp] theorem vertex_apply (n : ℕ) (i j : Fin (n + 1)) :
    vertex n i j = if j = i then 1 else 0 := by
  simp [vertex, Pi.single_apply, eq_comm]

/-- The affine simplex with specified vertices, as an actual continuous map
between the standard topological simplices. -/
def affine {n m : ℕ} (v : Fin (n + 1) → Simplex m) : C(Simplex n, Simplex m) where
  toFun x := ⟨fun j => ∑ i, x i * v i j, by
    change ∑ j : Fin (m + 1), ∑ i : Fin (n + 1), x i * v i j = 1
    rw [Finset.sum_comm]
    calc
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1), x i * v i j =
          ∑ i : Fin (n + 1), x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
        have hv : ∑ j : Fin (m + 1), v i j = 1 := (v i).2
        rw [hv, mul_one]
      _ = 1 := x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

@[simp] theorem affine_apply {n m : ℕ} (v : Fin (n + 1) → Simplex m)
    (x : Simplex n) (j : Fin (m + 1)) : affine v x j = ∑ i, x i * v i j := rfl

@[simp] theorem affine_vertex {n m : ℕ} (v : Fin (n + 1) → Simplex m)
    (i : Fin (n + 1)) : affine v (vertex n i) = v i := by
  apply Subtype.ext
  funext j
  simp [affine_apply, vertex_apply]

@[simp] theorem affine_vertices (n : ℕ) : affine (vertex n) = ContinuousMap.id (Simplex n) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  simp [affine_apply, vertex_apply]

/-- Composition of affine barycentric maps is determined by their vertices. -/
theorem affine_comp {n m k : ℕ} (v : Fin (n + 1) → Simplex m)
    (w : Fin (m + 1) → Simplex k) :
    (affine w).comp (affine v) = affine (fun i => affine w (v i)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  change ∑ a : Fin (m + 1), (∑ i : Fin (n + 1), x i * v i a) * w a j =
    ∑ i : Fin (n + 1), x i * ∑ a : Fin (m + 1), v i a * w a j
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The center of a nonempty face, in the actual standard simplex. -/
def faceCenter {n : ℕ} (S : Finset (Fin (n + 1))) (hS : S.Nonempty) : Simplex n :=
  ⟨fun j => if j ∈ S then (S.card : ℝ≥0)⁻¹ else 0, by
    change ∑ j : Fin (n + 1), (if j ∈ S then (S.card : ℝ≥0)⁻¹ else 0) = 1
    rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (show (S.card : ℝ≥0) ≠ 0 by exact_mod_cast hS.card_ne_zero)⟩

@[simp] theorem faceCenter_apply {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) (j : Fin (n + 1)) :
    faceCenter S hS j = if j ∈ S then (S.card : ℝ≥0)⁻¹ else 0 := rfl

@[simp] theorem faceCenter_singleton {n : ℕ} (i : Fin (n + 1)) :
    faceCenter {i} (by simp) = vertex n i := by
  apply Subtype.ext
  funext j
  simp [faceCenter_apply, vertex_apply]

/-- The center of the terminal face in the flag specified by a permutation. -/
def flagCenter {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) : Simplex n :=
  faceCenter {j | i ≤ σ⁻¹ j} ⟨σ i, by simp⟩

/-- One actual barycentric subsimplex, as a continuous self-map of the simplex. -/
def barycentricSimplex {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : C(Simplex n, Simplex n) :=
  affine (flagCenter σ)

@[simp] theorem barycentricSimplex_vertex {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : barycentricSimplex σ (vertex n i) = flagCenter σ i :=
  affine_vertex _ _

/-- The standard simplex functor map is the affine map prescribed on vertices. -/
theorem toTopMap_eq_affine {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ :
      C(Simplex n, Simplex m)) = affine (fun i => vertex m (f i)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  change (SimplexCategory.toTopMap f x) j = ∑ i, x i * vertex m (f i) j
  simp only [SimplexCategory.coe_toTopMap, vertex_apply,
    Finset.sum_filter, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eq_comm]

/-- Affine interpolation commutes with the actual face and degeneracy maps. -/
theorem affine_precomp_toTopMap {n m k : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (v : Fin (m + 1) → Simplex k) :
    (affine v).comp ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ =
      affine (fun i => v (f i)) := by
  rw [toTopMap_eq_affine, affine_comp]
  simp

end NRR.SingularHomology.SimplexGeometry
