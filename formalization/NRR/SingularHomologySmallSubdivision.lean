import NRR.SingularHomologyExcisionSmall
import NRR.SingularHomologySubdivisionFormula

/-! Actual subdivision and its cone homotopy restrict to arbitrary covering
small-chain complexes. No openness or covering hypothesis is needed for
support preservation. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

namespace NRR.SingularHomology

variable (R : Type) [Ring R]
variable {X : TopCat.{0}} {ι : Type} (U : ι → Set X)

abbrev smallChainComplex : ChainComplex (ModuleCat R) ℕ :=
  CsingSSet R (smallSubcomplex U)

def smallChainIncl : smallChainComplex R U ⟶ Csing R X :=
  simplicialChainMap R (smallSubcomplex U).ι

def smallChainFromSet (i : ι) :
    Csing R (TopCat.of (U i)) ⟶ smallChainComplex R U :=
  simplicialChainMap R
    (Subpresheaf.lift (TopCat.toSSet.map (subIncl (U i)))
      (le_iSup (fun j => smallSubcomplexOfSet (U j)) i))

@[reassoc (attr := simp)]
theorem smallChainFromSet_incl (i : ι) :
    smallChainFromSet R U i ≫ smallChainIncl R U =
      CsingMap R (subIncl (U i)) := by
  exact ((CsingSSetFunctor R).map_comp _ _).symm

/-- Restrict any natural degree-changing singular-chain operator. Each small
simplex is lifted to an actual member of the covering family. -/
def smallChainOperator (n k : ℕ)
    (θ : ∀ Y : TopCat.{0}, (Csing R Y).X n ⟶ (Csing R Y).X k) :
    (smallChainComplex R U).X n ⟶ (smallChainComplex R U).X k :=
  ccDesc R fun s =>
    let h := (mem_smallSubcomplex_iff_exists_lift (U := U) s.val).mp s.property
    simplexι R h.choose_spec.choose ≫ θ (TopCat.of (U h.choose)) ≫
      (smallChainFromSet R U h.choose).f k

@[reassoc]
theorem smallChainOperator_incl (n k : ℕ)
    (θ : ∀ Y : TopCat.{0}, (Csing R Y).X n ⟶ (Csing R Y).X k)
    (natural : ∀ {Y Z : TopCat.{0}} (f : Y ⟶ Z),
      (CsingMap R f).f n ≫ θ Z = θ Y ≫ (CsingMap R f).f k) :
    smallChainOperator R U n k θ ≫ (smallChainIncl R U).f k =
      (smallChainIncl R U).f n ≫ θ X := by
  apply simplicialChain_hom_ext R
  intro s
  let h := (mem_smallSubcomplex_iff_exists_lift (U := U) s.val).mp s.property
  have hs := h.choose_spec.choose_spec
  simp only [smallChainOperator, ι_ccDesc_assoc, Category.assoc]
  rw [← HomologicalComplex.comp_f, smallChainFromSet_incl,
    ← natural, simplexι_CsingMap_f_assoc]
  simpa only [smallChainIncl, simplexι_chainMap_f_assoc] using
    congrArg (fun t => simplexι R t ≫ θ X) hs

def smallSubdivisionComponent (n k : ℕ) :
    (smallChainComplex R U).X n ⟶ (smallChainComplex R U).X k :=
  smallChainOperator R U n k (fun Y => singularSubdivisionComponent R Y n k)

theorem smallSubdivisionComponent_zero (n k : ℕ) (h : n+1 ≠ k) :
    smallSubdivisionComponent R U n k = 0 := by
  apply simplicialChain_hom_ext R
  intro s
  simp [smallSubdivisionComponent, smallChainOperator,
    singularSubdivisionComponent_zero, h]

@[reassoc]
theorem smallSubdivisionComponent_incl (n k : ℕ) :
    smallSubdivisionComponent R U n k ≫ (smallChainIncl R U).f k =
      (smallChainIncl R U).f n ≫ singularSubdivisionComponent R X n k :=
  smallChainOperator_incl R U n k _
    (fun f => singularSubdivisionComponent_naturality R f n k)

def smallChainSubdivision : smallChainComplex R U ⟶ smallChainComplex R U :=
  𝟙 _ - Homotopy.nullHomotopicMap (smallSubdivisionComponent R U)

def smallChainHomotopyIdSubdivision :
    Homotopy (𝟙 _) (smallChainSubdivision R U) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [smallChainSubdivision]))
      (.nullHomotopy (smallSubdivisionComponent R U)
        (smallSubdivisionComponent_zero R U)))

theorem smallChainSubdivision_incl :
    smallChainSubdivision R U ≫ smallChainIncl R U =
      smallChainIncl R U ≫ singularChainSubdivision R X := by
  simp only [smallChainSubdivision, singularChainSubdivision,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Category.comp_id]
  congr 1
  rw [Homotopy.comp_nullHomotopicMap, Homotopy.nullHomotopicMap_comp]
  congr 1
  funext n k
  exact smallSubdivisionComponent_incl R U n k

theorem smallChainSubdivision_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (smallChainSubdivision R U) n = 𝟙 _ := by
  rw [← (smallChainHomotopyIdSubdivision R U).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

end NRR.SingularHomology
