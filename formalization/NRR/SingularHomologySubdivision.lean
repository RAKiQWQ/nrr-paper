/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NRR.SingularHomologyAffineSubdivision

/-! Actual singular-chain subdivision and its natural cone homotopy, on
Mathlib 4.24's singular chain complex with arbitrary ring coefficients. -/
noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
namespace NRR.SingularHomology
open SimplexGeometry

/-- The continuous map underlying an actual singular simplex. -/
def simplexTopMap {X : TopCat.{0}} {n : ℕ} (s : TopCat.toSSet.obj X _⦋n⦌) :
    TopCat.of (Simplex n) ⟶ X := TopCat.ofHom (TopCat.toSSetObjEquiv X _ s)

@[simp] theorem simplexTopMap_postcomp {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    simplexTopMap ((TopCat.toSSet.map f).app _ s) = simplexTopMap s ≫ f := rfl

variable (R : Type) [Ring R]

@[reassoc (attr := simp)] theorem simplexι_CsingMap_f {X Y : TopCat.{0}} (f : X ⟶ Y)
    {n : ℕ} (s : TopCat.toSSet.obj X _⦋n⦌) :
    simplexι R s ≫ (CsingMap R f).f n =
      simplexι R ((TopCat.toSSet.map f).app _ s) :=
  simplexι_chainMap_f R (TopCat.toSSet.map f) s

/-- The universal degree-raising affine cone chain on the actual `n`-simplex. -/
def universalSubdivisionAux (n : ℕ) :
    ModuleCat.of R R ⟶ (Csing R (TopCat.of (Simplex n))).X (n + 1) :=
  simplexι R (Y := vertexSSet (Simplex n)) (vertex n) ≫
    affineSubdivisionAux R n n ≫
      (simplicialChainMap R (affineToSingular n)).f (n + 1)

@[simp] theorem universalSubdivisionAux_zero : universalSubdivisionAux R 0 = 0 := by
  simp [universalSubdivisionAux]

/-- Transport of the universal affine cone homotopy along every actual singular simplex. -/
def singularSubdivisionAux (X : TopCat.{0}) (n : ℕ) :
    (Csing R X).X n ⟶ (Csing R X).X (n + 1) :=
  ccDesc R (Y := TopCat.toSSet.obj X) fun s =>
    universalSubdivisionAux R n ≫ (CsingMap R (simplexTopMap s)).f (n + 1)

@[reassoc (attr := simp)] theorem simplexι_singularSubdivisionAux {X : TopCat.{0}}
    {n : ℕ} (s : TopCat.toSSet.obj X _⦋n⦌) :
    simplexι R s ≫ singularSubdivisionAux R X n =
      universalSubdivisionAux R n ≫ (CsingMap R (simplexTopMap s)).f (n + 1) :=
  ι_ccDesc R _ _

@[simp] theorem singularSubdivisionAux_zero (X : TopCat.{0}) :
    singularSubdivisionAux R X 0 = 0 := by
  apply simplicialChain_hom_ext R
  intro s
  simp

/-- Naturality of the actual singular cone operator. -/
@[reassoc] theorem singularSubdivisionAux_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    (CsingMap R f).f n ≫ singularSubdivisionAux R Y n =
      singularSubdivisionAux R X n ≫ (CsingMap R f).f (n + 1) := by
  apply simplicialChain_hom_ext R
  intro s
  simp only [simplexι_CsingMap_f_assoc, simplexι_singularSubdivisionAux,
    simplexι_singularSubdivisionAux_assoc, simplexTopMap_postcomp,
    CsingMap_comp, HomologicalComplex.comp_f, Category.assoc]

/-- The singular cone homotopy, with zero components outside adjacent degrees. -/
def singularSubdivisionComponent (X : TopCat.{0}) (n k : ℕ) :
    (Csing R X).X n ⟶ (Csing R X).X k :=
  if h : n + 1 = k then singularSubdivisionAux R X n ≫ eqToHom (by rw [h]) else 0

@[simp] theorem singularSubdivisionComponent_eq (X : TopCat.{0}) (n : ℕ) :
    singularSubdivisionComponent R X n (n + 1) = singularSubdivisionAux R X n := by
  simp [singularSubdivisionComponent]

theorem singularSubdivisionComponent_zero (X : TopCat.{0}) (n k : ℕ) (h : n + 1 ≠ k) :
    singularSubdivisionComponent R X n k = 0 := by simp [singularSubdivisionComponent, h]

@[reassoc] theorem singularSubdivisionComponent_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n k : ℕ) :
    (CsingMap R f).f n ≫ singularSubdivisionComponent R Y n k =
      singularSubdivisionComponent R X n k ≫ (CsingMap R f).f k := by
  by_cases h : n + 1 = k
  · subst h
    simp only [singularSubdivisionComponent_eq, singularSubdivisionAux_naturality]
  · simp [singularSubdivisionComponent_zero, h]

/-- The actual singular subdivision chain map. -/
def singularChainSubdivision (X : TopCat.{0}) : Csing R X ⟶ Csing R X :=
  𝟙 _ - Homotopy.nullHomotopicMap (singularSubdivisionComponent R X)

/-- The actual chain homotopy between the identity and singular subdivision. -/
def singularChainHomotopyIdSubdivision (X : TopCat.{0}) :
    Homotopy (𝟙 _) (singularChainSubdivision R X) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [singularChainSubdivision]))
      (.nullHomotopy (singularSubdivisionComponent R X)
        (singularSubdivisionComponent_zero R X)))

/-- Subdivision commutes with all continuous maps. -/
theorem singularChainSubdivision_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    CsingMap R f ≫ singularChainSubdivision R Y =
      singularChainSubdivision R X ≫ CsingMap R f := by
  simp only [singularChainSubdivision, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp]
  congr 1
  rw [Homotopy.comp_nullHomotopicMap, Homotopy.nullHomotopicMap_comp]
  congr 1
  funext n k
  exact singularSubdivisionComponent_naturality R f n k

/-- The actual subdivision map induces the identity on singular homology. -/
theorem singularChainSubdivision_homologyMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (singularChainSubdivision R X) n = 𝟙 _ := by
  rw [← (singularChainHomotopyIdSubdivision R X).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

end NRR.SingularHomology
