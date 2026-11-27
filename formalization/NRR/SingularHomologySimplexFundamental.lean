/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NRR.SingularHomologySimplicial
import NRR.SingularHomologyPair
import NRR.SingularHomologySubdivisionGeometry
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! Actual relative singular chains carried by the identity simplex. -/

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

namespace NRR.SingularHomology.SimplexFundamental

open SimplexGeometry

abbrev GeometricSimplex (n : Nat) := Simplex n

/-- The actual continuous map of the `i`th face of a geometric simplex. -/
def faceMapC (n : Nat) (i : Fin (n + 2)) : C(GeometricSimplex n, GeometricSimplex (n + 1)) :=
  ⟨SimplexCategory.toTopMap
      (SimplexCategory.mkHom (Fin.succAboveOrderEmb i).toOrderHom),
    SimplexCategory.continuous_toTopMap _⟩

def faceMap (n : Nat) (i : Fin (n + 2)) :
    TopCat.of (GeometricSimplex n) ⟶ TopCat.of (GeometricSimplex (n + 1)) :=
  TopCat.ofHom (faceMapC n i)

/-- The geometric boundary, as the union of the images of the standard faces. -/
def boundary : (n : Nat) -> Set (GeometricSimplex n)
  | 0 => ∅
  | n + 1 => ⋃ i : Fin (n + 2), Set.range (faceMapC n i)

/-- The inclusion of the actual boundary into the geometric simplex. -/
def boundaryIncl (n : Nat) : TopCat.of (boundary n) ⟶ TopCat.of (GeometricSimplex n) :=
  subIncl (Y := TopCat.of (GeometricSimplex n)) (boundary n)

instance mono_boundaryIncl (n : Nat) : Mono (boundaryIncl n) := by
  dsimp [boundaryIncl]
  infer_instance

/-- A face map with codomain restricted to the actual boundary. -/
def faceToBoundary (n : Nat) (i : Fin (n + 2)) :
    C(GeometricSimplex n, boundary (n + 1)) where
  toFun x := ⟨faceMapC n i x, Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨x, rfl⟩⟩⟩
  continuous_toFun := (faceMapC n i).continuous.subtype_mk _

@[simp] theorem boundaryIncl_faceToBoundary (n : Nat) (i : Fin (n + 2)) :
    TopCat.ofHom (faceToBoundary n i) ≫ boundaryIncl (n + 1) = faceMap n i := by
  ext x
  rfl

/-- The identity continuous map, regarded as an actual singular simplex. -/
def identitySingularSimplex (n : Nat) :
    (TopCat.toSSet.obj (TopCat.of (GeometricSimplex n))).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of (GeometricSimplex n)) (op ⦋n⦌)).symm
    (ContinuousMap.id (GeometricSimplex n))

/-- A face, regarded as a singular simplex with values in the boundary. -/
def faceSingularSimplex (n : Nat) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (boundary (n + 1)))).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of (boundary (n + 1))) (op ⦋n⦌)).symm
    (faceToBoundary n i)

theorem faceSingularSimplex_inclusion (n : Nat) (i : Fin (n + 2)) :
    (TopCat.toSSet.map (boundaryIncl (n + 1))).app (op ⦋n⦌)
        (faceSingularSimplex n i) =
      (TopCat.toSSet.obj (TopCat.of (GeometricSimplex (n + 1)))).δ i
        (identitySingularSimplex (n + 1)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (GeometricSimplex (n + 1)))
    (op ⦋n⦌)).injective
  change (faceMapC n i) = (ContinuousMap.id (GeometricSimplex (n + 1))).comp
    ⟨SimplexCategory.toTopMap (SimplexCategory.δ i), SimplexCategory.continuous_toTopMap _⟩
  rfl

/-- The identity simplex as a generator of the actual singular chain complex. -/
def identityChain (R : Type) [Ring R] (n : Nat) :
    ModuleCat.of R R ⟶ (Csing R (TopCat.of (GeometricSimplex n))).X n :=
  simplexι R (identitySingularSimplex n)

/-- The identity simplex projected to the actual relative singular chains. -/
def identityRelativeChain (R : Type) [Ring R] (n : Nat) :
    ModuleCat.of R R ⟶ (relComplex R (boundaryIncl n)).X n :=
  identityChain R n ≫ (relProj R (boundaryIncl n)).f n

/-- The alternating face chain, with values in the geometric boundary. -/
def boundaryChain (R : Type) [Ring R] (n : Nat) :
    ModuleCat.of R R ⟶ (Csing R (TopCat.of (boundary (n + 1)))).X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexι R (faceSingularSimplex n i)

/-- The boundary of the actual identity generator factors through the
actual singular chains of the geometric boundary. -/
theorem identityChain_boundary (R : Type) [Ring R] (n : Nat) :
    identityChain R (n + 1) ≫
      (Csing R (TopCat.of (GeometricSimplex (n + 1)))).d (n + 1) n =
      boundaryChain R n ≫ (CsingMap R (boundaryIncl (n + 1))).f n := by
  change simplexι R (identitySingularSimplex (n + 1)) ≫
      (CsingSSet R (TopCat.toSSet.obj (TopCat.of (GeometricSimplex (n + 1))))).d (n + 1) n = _
  rw [simplexι_d, boundaryChain, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  congr 1
  change simplexι R _ =
    simplexι R _ ≫ (simplicialChainMap R (TopCat.toSSet.map (boundaryIncl (n + 1)))).f n
  rw [simplexι_chainMap_f, faceSingularSimplex_inclusion]

/-- The projection kills all actual singular chains of the boundary. -/
theorem boundaryChain_projection (R : Type) [Ring R] (n : Nat) :
    (CsingMap R (boundaryIncl (n + 1))).f n ≫
      (relProj R (boundaryIncl (n + 1))).f n = 0 := by
  exact congrArg (fun f => f.f n) (cokernel.condition (CsingMap R (boundaryIncl (n + 1))))

/-- The identity simplex is an actual cycle in the actual relative chain
complex of the geometric simplex and its boundary. -/
theorem identityRelativeChain_cycle_succ (R : Type) [Ring R] (n : Nat) :
    identityRelativeChain R (n + 1) ≫
      (relComplex R (boundaryIncl (n + 1))).d (n + 1) n = 0 := by
  rw [identityRelativeChain, Category.assoc, HomologicalComplex.Hom.comm,
    ← Category.assoc, identityChain_boundary, Category.assoc, boundaryChain_projection,
    comp_zero]

theorem identityRelativeChain_cycle (R : Type) [Ring R] (n : Nat) :
    identityRelativeChain R n ≫ (relComplex R (boundaryIncl n)).d n (n - 1) = 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using identityRelativeChain_cycle_succ R n

/-- The concrete relative cycle represented by the identity simplex. -/
def identityRelativeCycle (R : Type) [Ring R] (n : Nat) :
    ModuleCat.of R R ⟶ (relComplex R (boundaryIncl n)).cycles n :=
  (relComplex R (boundaryIncl n)).liftCycles (identityRelativeChain R n) (n - 1)
    (by cases n <;> simp) (identityRelativeChain_cycle R n)

@[reassoc (attr := simp)] theorem identityRelativeCycle_i (R : Type) [Ring R] (n : Nat) :
    identityRelativeCycle R n ≫ (relComplex R (boundaryIncl n)).iCycles n =
      identityRelativeChain R n :=
  (relComplex R (boundaryIncl n)).liftCycles_i _ _ _ _

/-- The homology morphism induced by the actual identity relative cycle. -/
def identityClassMap (R : Type) [Ring R] (n : Nat) :
    ModuleCat.of R R ⟶ Hrel R n (boundaryIncl n) :=
  identityRelativeCycle R n ≫ (relComplex R (boundaryIncl n)).homologyπ n

/-- The class of the genuine identity singular simplex with coefficient one. -/
def identityClass (R : Type) [Ring R] (n : Nat) : Hrel R n (boundaryIncl n) :=
  identityClassMap R n 1

theorem identityClassMap_apply (R : Type) [Ring R] (n : Nat) (r : R) :
    identityClassMap R n r = r • identityClass R n := by
  simpa [identityClass] using (identityClassMap R n).hom.map_smul r (1 : R)

end NRR.SingularHomology.SimplexFundamental
