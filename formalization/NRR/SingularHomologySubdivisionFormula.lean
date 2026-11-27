/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

The recursive affine cone homotopy underlying the formula below was adapted in
NRR/SingularHomologyAffineSubdivision.lean from Hatcher/Excision/AffineChains.lean
in akopjan/toptverbert-nandakumar, revision
d98f6f87bb60b9e5b3a57370f393ade1397189bc.  This file proves its compatibility
with the actual singular-chain subdivision on Mathlib 4.24's singular simplices.
-/
import NRR.SingularHomologySubdivision

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
namespace NRR.SingularHomology
open SimplexGeometry

/-- Affine realization commutes with affine maps between standard simplices. -/
theorem affineToSingular_naturality {m k : ℕ} (w : Fin (m + 1) → Simplex k) :
    vertexMap (affine w) ≫ affineToSingular k =
      affineToSingular m ≫ TopCat.toSSet.map (TopCat.ofHom (affine w)) := by
  ext n v
  apply (TopCat.toSSetObjEquiv _ n).injective
  change affine (affine w ∘ v) = (affine w).comp (affine v)
  exact (affine_comp v w).symm

@[simp] theorem simplexTopMap_affineToSingular {m n : ℕ}
    (v : Fin (n + 1) → Simplex m) :
    simplexTopMap ((affineToSingular m).app _ v) = TopCat.ofHom (affine v) := by
  exact congrArg (fun f : C(Simplex n, Simplex m) => TopCat.ofHom f)
    ((TopCat.toSSetObjEquiv (TopCat.of (Simplex m)) (op ⦋n⦌)).apply_symm_apply (affine v))

variable (R : Type) [Ring R]

/-- Realization carries the actual affine cone homotopy to the singular one. -/
@[reassoc] theorem affineToSingular_subdivisionAux (m n : ℕ) :
    (simplicialChainMap R (affineToSingular m)).f n ≫
        singularSubdivisionAux R (TopCat.of (Simplex m)) n =
      affineSubdivisionAux R m n ≫
        (simplicialChainMap R (affineToSingular m)).f (n + 1) := by
  apply simplicialChain_hom_ext R
  intro v
  simp only [simplexι_chainMap_f_assoc, simplexι_singularSubdivisionAux,
    simplexTopMap_affineToSingular, universalSubdivisionAux, Category.assoc]
  have hmap : simplicialChainMap R (vertexMap (affine v)) ≫
        simplicialChainMap R (affineToSingular m) =
      simplicialChainMap R (affineToSingular n) ≫
        CsingMap R (TopCat.ofHom (affine v)) := by
    change (CsingSSetFunctor R).map (vertexMap (affine v)) ≫
        (CsingSSetFunctor R).map (affineToSingular m) =
      (CsingSSetFunctor R).map (affineToSingular n) ≫
        (CsingSSetFunctor R).map (TopCat.toSSet.map (TopCat.ofHom (affine v)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((CsingSSetFunctor R).map)
      (affineToSingular_naturality (m := n) (k := m) v)
  rw [← HomologicalComplex.comp_f, ← hmap, HomologicalComplex.comp_f]
  simpa only [Category.assoc, simplexι_chainMap_f_assoc, vertexMap_app,
    Function.comp_def, affine_vertex] using
    congrArg (fun f => simplexι R (Y := vertexSSet (Simplex n)) (vertex n) ≫ f ≫
      (simplicialChainMap R (affineToSingular m)).f (n + 1))
      (affineSubdivisionAux_naturality R (m := n) (k := m) v n).symm

/-- Compatibility of every component of the two actual subdivision homotopies. -/
@[reassoc] theorem affineToSingular_subdivisionComponent (m n k : ℕ) :
    (simplicialChainMap R (affineToSingular m)).f n ≫
        singularSubdivisionComponent R (TopCat.of (Simplex m)) n k =
      affineSubdivisionComponent R m n k ≫
        (simplicialChainMap R (affineToSingular m)).f k := by
  by_cases h : n + 1 = k
  · subst k
    simp only [singularSubdivisionComponent_eq, affineSubdivisionComponent_eq,
      affineToSingular_subdivisionAux]
  · simp [singularSubdivisionComponent_zero, affineSubdivisionComponent_zero, h]

/-- The affine chain formula realizes to the genuine singular subdivision map. -/
theorem affineToSingular_chainSubdivision (m : ℕ) :
    simplicialChainMap R (affineToSingular m) ≫
        singularChainSubdivision R (TopCat.of (Simplex m)) =
      affineChainSubdivision R m ≫ simplicialChainMap R (affineToSingular m) := by
  simp only [singularChainSubdivision, affineChainSubdivision, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.id_comp]
  congr 1
  rw [Homotopy.comp_nullHomotopicMap, Homotopy.nullHomotopicMap_comp]
  congr 1
  funext n k
  exact affineToSingular_subdivisionComponent R m n k

/-- The signed affine formula after realization in the actual singular chains. -/
@[reassoc] theorem simplexι_affineToSingular_chainSubdivision_eq_sum {m n : ℕ}
    (v : Fin (n + 1) → Simplex m) :
    simplexι R ((affineToSingular m).app _ v) ≫
        (singularChainSubdivision R (TopCat.of (Simplex m))).f n =
      ∑ a : SubdivisionIndex n, subdivisionSign n a •
        simplexι R ((affineToSingular m).app _ (subdivisionVertices n v a)) := by
  rw [← simplexι_chainMap_f_assoc, ← HomologicalComplex.comp_f,
    affineToSingular_chainSubdivision, HomologicalComplex.comp_f,
    simplexι_affineChainSubdivision_eq_sum_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, simplexι_chainMap_f]

/-- A singular simplex is the image of the universal affine simplex. -/
@[simp] theorem affineToSingular_vertex_postcomp {X : TopCat.{0}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.map (simplexTopMap (n := n) s)).app (op ⦋n⦌)
      ((affineToSingular n).app (op ⦋n⦌) (vertex n)) = s := by
  apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective
  change (TopCat.toSSetObjEquiv X (op ⦋n⦌) s).comp (affine (vertex n)) =
    TopCat.toSSetObjEquiv X (op ⦋n⦌) s
  simp only [affine_vertices, ContinuousMap.comp_id]

/-- The actual singular subsimplex obtained by precomposing with the affine map
whose vertices are the recursively specified barycentric vertices. -/
def subdivisionSimplex {X : TopCat.{0}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (a : SubdivisionIndex n) :
    TopCat.toSSet.obj X _⦋n⦌ :=
  (TopCat.toSSet.map (simplexTopMap s)).app _
    ((affineToSingular n).app _ (subdivisionVertices n (vertex n) a))

/-- Each term in the signed formula is the original continuous simplex
precomposed with the indicated actual affine barycentric map. -/
@[simp] theorem simplexTopMap_subdivisionSimplex {X : TopCat.{0}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (a : SubdivisionIndex n) :
    simplexTopMap (subdivisionSimplex s a) =
      TopCat.ofHom (affine (subdivisionVertices n (vertex n) a)) ≫ simplexTopMap s := by
  rw [subdivisionSimplex, simplexTopMap_postcomp, simplexTopMap_affineToSingular]

/-- Every simplex appearing in subdivision is supported in the original
singular simplex. This uses the actual continuous affine maps. -/
theorem subdivisionSimplex_range_subset {X : TopCat.{0}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (a : SubdivisionIndex n) :
    Set.range (TopCat.toSSetObjEquiv X _ (subdivisionSimplex s a)) ⊆
      Set.range (TopCat.toSSetObjEquiv X _ s) := by
  change Set.range (simplexTopMap (subdivisionSimplex s a)) ⊆
    Set.range (simplexTopMap s)
  rw [simplexTopMap_subdivisionSimplex]
  rintro y ⟨x, rfl⟩
  exact ⟨affine (subdivisionVertices n (vertex n) a) x, rfl⟩

/-- The finite signed sum formula for genuine singular-chain subdivision on
every singular-simplex generator, with arbitrary ring coefficients. -/
@[reassoc] theorem simplexι_singularChainSubdivision_eq_sum {X : TopCat.{0}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    simplexι R s ≫ (singularChainSubdivision R X).f n =
      ∑ a : SubdivisionIndex n,
        subdivisionSign n a • simplexι R (subdivisionSimplex s a) := by
  have h := congrArg (fun f =>
    simplexι R ((affineToSingular n).app _ (vertex n)) ≫ f.f n)
    (singularChainSubdivision_naturality R (simplexTopMap s))
  simp only [HomologicalComplex.comp_f, simplexι_CsingMap_f_assoc,
    simplexι_affineToSingular_chainSubdivision_eq_sum_assoc,
    Preadditive.sum_comp, Preadditive.zsmul_comp, simplexι_CsingMap_f] at h
  rw [affineToSingular_vertex_postcomp (n := n) s] at h
  exact h

end NRR.SingularHomology
