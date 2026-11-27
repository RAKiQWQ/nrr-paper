import NRR.PrimePowerTopologySphereGenerator
import NRR.SingularHomologySimplicial

/-! Actual zeroth singular homology of path-connected spaces over any ring.
The proof uses generation by actual zero-simplices and paths between points. -/

noncomputable section
open Set Topology CategoryTheory Limits AlgebraicTopology Opposite Simplicial
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [Ring R]

/-- Every zero-chain is a cycle, using the genuine cycle object. -/
def zeroCyclesIso (X : TopCat.{0}) : (Csing R X).X 0 ≅ (Csing R X).cycles 0 where
  hom := (Csing R X).liftCycles (𝟙 _) 0 (by simp) (by simp)
  inv := (Csing R X).iCycles 0
  hom_inv_id := by simp
  inv_hom_id := by
    apply (cancel_mono ((Csing R X).iCycles 0)).mp
    simp [Category.assoc]

/-- The canonical epimorphism from actual zero-chains to zeroth homology. -/
def zeroChainProjection (X : TopCat.{0}) : (Csing R X).X 0 ⟶ Habs R 0 X :=
  (zeroCyclesIso R X).hom ≫ (Csing R X).homologyπ 0

instance epi_zeroChainProjection (X : TopCat.{0}) : Epi (zeroChainProjection R X) := by
  dsimp [zeroChainProjection]
  infer_instance

@[reassoc]
theorem zeroChainProjection_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (CsingMap R f).f 0 ≫ zeroChainProjection R Y =
      zeroChainProjection R X ≫ HabsMap R 0 f := by
  have hc : (CsingMap R f).f 0 ≫ (zeroCyclesIso R Y).hom =
      (zeroCyclesIso R X).hom ≫ HomologicalComplex.cyclesMap (CsingMap R f) 0 := by
    apply (cancel_mono ((Csing R Y).iCycles 0)).mp
    simp [zeroCyclesIso, Category.assoc]
  unfold zeroChainProjection
  rw [← Category.assoc, hc, Category.assoc,
    ← HomologicalComplex.homologyπ_naturality]
  simp [Category.assoc]

/-- The actual class of the constant zero-simplex at a point. -/
def zeroSimplexClass (X : TopCat.{0}) (x : X) : ModuleCat.of R R ⟶ Habs R 0 X :=
  simplexι R ((zeroSimplexEquiv X).symm x) ≫ zeroChainProjection R X

@[reassoc]
theorem zeroSimplexClass_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    zeroSimplexClass R X x ≫ HabsMap R 0 f = zeroSimplexClass R Y (f x) := by
  unfold zeroSimplexClass
  rw [Category.assoc, ← zeroChainProjection_naturality, ← Category.assoc]
  have hmap := simplexι_chainMap_f R (TopCat.toSSet.map f) ((zeroSimplexEquiv X).symm x)
  change simplexι R ((zeroSimplexEquiv X).symm x) ≫ (CsingMap R f).f 0 = _ at hmap
  rw [hmap]
  congr 2

/-- Point classes generate all of actual zeroth homology. -/
theorem HabsZero_hom_ext {X : TopCat.{0}} {T : ModuleCat R} {f g : Habs R 0 X ⟶ T}
    (h : ∀ x : X, zeroSimplexClass R X x ≫ f = zeroSimplexClass R X x ≫ g) :
    f = g := by
  apply (cancel_epi (zeroChainProjection R X)).mp
  apply simplicialChain_hom_ext R
  intro s
  simpa only [zeroSimplexClass, Equiv.symm_apply_apply, Category.assoc] using
    h (zeroSimplexEquiv X s)

/-- A genuine path gives a homotopy of the two point inclusions. -/
def pointInclHomotopy {X : TopCat.{0}} {x y : X} (p : Path x y) :
    (homologyPointIncl x).hom.Homotopy (homologyPointIncl y).hom where
  toFun q := p q.1
  continuous_toFun := p.continuous.comp continuous_fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

theorem HabsMap_pointIncl_eq_of_path {X : TopCat.{0}} {x y : X} (p : Path x y) :
    HabsMap R 0 (homologyPointIncl x) = HabsMap R 0 (homologyPointIncl y) :=
  HabsMap_eq_of_homotopy R 0 (pointInclHomotopy p)

/-- On a path-connected space, the actual collapse and point inclusion
are inverse on zeroth homology. -/
theorem HabsMap_collapse_pointIncl {X : TopCat.{0}} [PathConnectedSpace X] (x₀ : X) :
    HabsMap R 0 (homologyPointCollapse X) ≫ HabsMap R 0 (homologyPointIncl x₀) =
      𝟙 (Habs R 0 X) := by
  apply HabsZero_hom_ext R
  intro x
  have hc : zeroSimplexClass R X x =
      zeroSimplexClass R (TopCat.of Unit) () ≫ HabsMap R 0 (homologyPointIncl x) :=
    (zeroSimplexClass_naturality R (homologyPointIncl x) ()).symm
  rw [hc]
  simp only [Category.assoc, Category.comp_id]
  have hi : HabsMap R 0 (homologyPointIncl x) ≫
      HabsMap R 0 (homologyPointCollapse X) = 𝟙 _ := by
    rw [← HabsMap_comp]
    convert HabsMap_id R 0 (TopCat.of Unit) using 1
  rw [← Category.assoc (HabsMap R 0 (homologyPointIncl x))
    (HabsMap R 0 (homologyPointCollapse X)) (HabsMap R 0 (homologyPointIncl x₀)), hi]
  simp only [Category.id_comp]
  rw [HabsMap_pointIncl_eq_of_path R (PathConnectedSpace.somePath x₀ x)]

/-- The canonical map to the point is an isomorphism on actual zeroth
singular homology of every path-connected space. -/
def HabsZeroCollapseIso (X : TopCat.{0}) [PathConnectedSpace X] :
    Habs R 0 X ≅ Habs R 0 (TopCat.of Unit) where
  hom := HabsMap R 0 (homologyPointCollapse X)
  inv := HabsMap R 0 (homologyPointIncl (Classical.choice (inferInstance : Nonempty X)))
  hom_inv_id := HabsMap_collapse_pointIncl R _
  inv_hom_id := by
    rw [← HabsMap_comp]
    convert HabsMap_id R 0 (TopCat.of Unit) using 1

theorem isIso_HabsMap_zero_of_pathConnected {X Y : TopCat.{0}}
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y) :
    IsIso (HabsMap R 0 f) := by
  have hn : HabsMap R 0 f ≫ (HabsZeroCollapseIso R Y).hom =
      (HabsZeroCollapseIso R X).hom := by
    rw [show (HabsZeroCollapseIso R Y).hom =
        HabsMap R 0 (homologyPointCollapse Y) from rfl, ← HabsMap_comp]
    congr 1
  letI : IsIso (HabsMap R 0 f ≫ (HabsZeroCollapseIso R Y).hom) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (HabsZeroCollapseIso R Y).hom

end NRR.PrimePowerTopology
