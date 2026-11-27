/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NRR.SingularHomologySubdivisionGeometry
import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-! The simplicial set of ordered vertex lists, its actual affine singular
realization, and its chain contraction by adjoining an initial vertex. -/
noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
namespace NRR.SingularHomology
open SimplexGeometry

/-- All ordered vertex lists form a simplicial set, including repeated vertices. -/
def vertexSSet (Y : Type) : SSet.{0} where
  obj n := Fin (n.unop.len + 1) → Y
  map f v := fun i => v (f.unop i)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem vertexSSet_delta {Y : Type} {n : ℕ} (v : Fin (n + 2) → Y)
    (i : Fin (n + 2)) :
    (vertexSSet Y).δ i v = fun j => v (i.succAbove j) := rfl

/-- A function on vertices acts simplicially on vertex lists. -/
def vertexMap {Y Z : Type} (φ : Y → Z) : vertexSSet Y ⟶ vertexSSet Z where
  app _ v := φ ∘ v
  naturality _ _ _ := rfl

@[simp] theorem vertexMap_app {Y Z : Type} (φ : Y → Z)
    {n : SimplexCategoryᵒᵖ} (v : (vertexSSet Y).obj n) :
    (vertexMap φ).app n v = φ ∘ v := rfl

/-- The actual singular simplex obtained by affine interpolation. -/
def affineToSingular (m : ℕ) :
    vertexSSet (Simplex m) ⟶ TopCat.toSSet.obj (TopCat.of (Simplex m)) where
  app n v := (TopCat.toSSetObjEquiv _ n).symm (affine v)
  naturality n k f := by
    funext v
    apply (TopCat.toSSetObjEquiv _ k).injective
    change affine (fun i => v (f.unop i)) =
      (affine v).comp ⟨SimplexCategory.toTopMap f.unop,
        SimplexCategory.continuous_toTopMap f.unop⟩
    exact (affine_precomp_toTopMap (n := k.unop.len) (m := n.unop.len) f.unop v).symm

/-- Vertex lists augmented to a point. -/
abbrev vertexAugmented (Y : Type) : SSet.Augmented where
  left := vertexSSet Y
  right := PUnit
  hom.app _ _ := PUnit.unit

/-- Adjoining the distinguished vertex is an actual simplicial extra degeneracy. -/
def vertexExtraDegeneracy {Y : Type} (y : Y) :
    (vertexAugmented Y).ExtraDegeneracy where
  s' _ := fun _ => y
  s _ v := Fin.cases (motive := fun _ => Y) y v
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    funext v i
    fin_cases i
    rfl
  s_comp_δ₀ _ := rfl
  s_comp_δ n i := by
    funext v j
    change Fin.cases (motive := fun _ => Y) y v (i.succ.succAbove j) =
      Fin.cases (motive := fun _ => Y) y (fun k => v (i.succAbove k)) j
    cases j using Fin.cases <;> simp
  s_comp_σ n i := by
    funext v j
    change Fin.cases (motive := fun _ => Y) y v (i.succ.predAbove j) =
      Fin.cases (motive := fun _ => Y) y (fun k => v (i.predAbove k)) j
    cases j using Fin.cases <;> simp

variable (R : Type) [Ring R]

/-- The chain cone sends a vertex list to the list with initial vertex `y`. -/
def vertexChainCone {Y : Type} (y : Y) (n : ℕ) :
    (CsingSSet R (vertexSSet Y)).X n ⟶ (CsingSSet R (vertexSSet Y)).X (n + 1) :=
  ((vertexExtraDegeneracy y).map (sigmaConst.obj (ModuleCat.of R R))).s n

@[reassoc (attr := simp)] theorem simplexι_vertexChainCone {Y : Type} (y : Y)
    {n : ℕ} (v : Fin (n + 1) → Y) :
    simplexι R (Y := vertexSSet Y) v ≫ vertexChainCone R y n =
      simplexι R (Y := vertexSSet Y) (Fin.cases (motive := fun _ => Y) y v) := by
  simp [vertexChainCone, vertexExtraDegeneracy,
    SimplicialObject.Augmented.ExtraDegeneracy.map, simplexι]

/-- The chain cone commutes with every function on the vertices. -/
@[reassoc] theorem vertexChainCone_naturality {Y Z : Type} (φ : Y → Z)
    (y : Y) (n : ℕ) :
    (simplicialChainMap R (vertexMap φ)).f n ≫ vertexChainCone R (φ y) n =
      vertexChainCone R y n ≫ (simplicialChainMap R (vertexMap φ)).f (n + 1) := by
  apply simplicialChain_hom_ext R
  intro v
  rw [simplexι_chainMap_f_assoc, simplexι_vertexChainCone,
    simplexι_vertexChainCone_assoc, simplexι_chainMap_f]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

end NRR.SingularHomology
