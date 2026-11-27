import NRR.SingularHomologyMayerVietorisMap
import NRR.SingularHomologyExcision

/-! The Mayer--Vietoris sequence on actual singular homology for a cover
by interiors, obtained from the proved small-chain comparison. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology

namespace NRR.SingularHomology
variable (R : Type) [Ring R]
variable {X : TopCat.{0}} (A B : Set X)

/-- The actual small-chain inclusion, viewed as a homology isomorphism. -/
def mvSmallHomologyIso (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSmallComplex (R := R) A B).homology n ≅ Habs R n X := by
  letI := isIso_mvSmallIncl_homologyMap R A B cover n
  exact asIso (HomologicalComplex.homologyMap (mvSmallIncl (R := R) A B) n)

@[simp]
theorem mvSmallHomologyIso_hom (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSmallHomologyIso R A B cover n).hom =
      HomologicalComplex.homologyMap (mvSmallIncl (R := R) A B) n := rfl

/-- The signed map from the two parts to the actual homology of the ambient space. -/
def mvKappa (n : ℕ) : mvSum R A B n ⟶ Habs R n X :=
  mvSmallKappa R A B n ≫
    HomologicalComplex.homologyMap (mvSmallIncl (R := R) A B) n

/-- The connecting morphism in the actual singular-homology Mayer--Vietoris sequence. -/
def mvDelta (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    Habs R (n+1) X ⟶ Habs R n (TopCat.of (A ∩ B : Set X)) :=
  (mvSmallHomologyIso R A B cover (n+1)).inv ≫ mvSmallDelta R A B n

@[reassoc]
theorem mvSmallHomologyIso_hom_comp_mvDelta
    (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSmallHomologyIso R A B cover (n+1)).hom ≫ mvDelta R A B cover n =
      mvSmallDelta R A B n := by
  simp only [mvDelta, Iso.hom_inv_id_assoc]

@[reassoc]
theorem mvSmallKappa_comp_mvSmallHomologyIso_hom
    (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvSmallKappa R A B n ≫ (mvSmallHomologyIso R A B cover n).hom =
      mvKappa R A B n := rfl

/-- The transported map is precisely the usual signed pair of inclusion maps. -/
theorem mvKappa_eq_desc (n : ℕ) :
    mvKappa R A B n =
      biprod.desc (HabsMap R n (subIncl A)) (-HabsMap R n (subIncl B)) := by
  unfold mvKappa mvSmallKappa mvSumIso additiveBiprodIso
  apply biprod.hom_ext'
  · simp only [Category.assoc, biprod.inl_desc_assoc, ← HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap biprod.inl n ≫
      HomologicalComplex.homologyMap ((mvSC (R := R) A B).g ≫
        mvSmallIncl (R := R) A B) n = _
    rw [← HomologicalComplex.homologyMap_comp]
    simp [mvSC_g_eq, mvPa_smallIncl]
  · simp only [Category.assoc, biprod.inr_desc_assoc, ← HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap biprod.inr n ≫
      HomologicalComplex.homologyMap ((mvSC (R := R) A B).g ≫
        mvSmallIncl (R := R) A B) n = _
    rw [← HomologicalComplex.homologyMap_comp]
    simp [mvSC_g_eq, mvPb_smallIncl]

theorem mvIota_comp_mvSmallKappa (n : ℕ) :
    mvIota R A B n ≫ mvSmallKappa R A B n = 0 := by
  rw [← homologyMap_mvSC_f]
  simp only [mvSmallKappa, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp, (mvSC (R := R) A B).zero,
    HomologicalComplex.homologyMap_zero]

theorem mvSmall_exact_iota_kappa (n : ℕ) :
    (ShortComplex.mk (mvIota R A B n) (mvSmallKappa R A B n)
      (mvIota_comp_mvSmallKappa R A B n)).Exact := by
  have hex := (mvSC_shortExact (R := R) A B).homology_exact₂ n
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (mvSumIso R A B n) (Iso.refl _) ?_ ?_
  · exact (Category.id_comp _).trans (homologyMap_mvSC_f R A B n).symm
  · simp [mvSmallKappa]

theorem mvIota_comp_mvKappa (n : ℕ) :
    mvIota R A B n ≫ mvKappa R A B n = 0 := by
  simp [mvKappa, ← Category.assoc, mvIota_comp_mvSmallKappa]

theorem mvKappa_comp_mvDelta (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvKappa R A B (n+1) ≫ mvDelta R A B cover n = 0 := by
  rw [← mvSmallKappa_comp_mvSmallHomologyIso_hom R A B cover (n+1),
    Category.assoc, mvSmallHomologyIso_hom_comp_mvDelta]
  exact mvSmallKappa_comp_mvSmallDelta R A B n

theorem mvDelta_comp_mvIota (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvDelta R A B cover n ≫ mvIota R A B n = 0 := by
  simp [mvDelta, Category.assoc, mvSmallDelta_comp_mvIota]

/-- Exactness at the intersection, including degree zero. -/
theorem mv_exact_delta_iota (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvDelta R A B cover n) (mvIota R A B n)
      (mvDelta_comp_mvIota R A B cover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvSmall_exact_delta_iota R A B n)
  refine ShortComplex.isoMk (mvSmallHomologyIso R A B cover (n+1))
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id] using
      mvSmallHomologyIso_hom_comp_mvDelta R A B cover n
  · simp

/-- Exactness at the homology of the union in every positive degree. -/
theorem mv_exact_kappa_delta (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvKappa R A B (n+1)) (mvDelta R A B cover n)
      (mvKappa_comp_mvDelta R A B cover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvSmall_exact_kappa_delta R A B n)
  refine ShortComplex.isoMk (Iso.refl _) (mvSmallHomologyIso R A B cover (n+1))
    (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simpa only [Iso.refl_hom, Category.comp_id] using
      mvSmallHomologyIso_hom_comp_mvDelta R A B cover n

/-- Exactness at the direct sum, including degree zero. -/
theorem mv_exact_iota_kappa (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvIota R A B n) (mvKappa R A B n)
      (mvIota_comp_mvKappa R A B n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvSmall_exact_iota_kappa R A B n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (mvSmallHomologyIso R A B cover n) ?_ ?_
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl

/-- Vanishing in the two pieces makes the connecting morphism injective. -/
theorem mono_mvDelta (cover : interior A ∪ interior B = Set.univ) (n : ℕ)
    (hA : IsZero (Habs R (n+1) (TopCat.of A)))
    (hB : IsZero (Habs R (n+1) (TopCat.of B))) :
    Mono (mvDelta R A B cover n) := by
  exact (mv_exact_kappa_delta R A B cover n).mono_g
    ((isZero_mvSum R A B (n+1) hA hB).eq_zero_of_src _)

/-- Vanishing in the two pieces makes the connecting morphism surjective. -/
theorem epi_mvDelta (cover : interior A ∪ interior B = Set.univ) (n : ℕ)
    (hA : IsZero (Habs R n (TopCat.of A)))
    (hB : IsZero (Habs R n (TopCat.of B))) :
    Epi (mvDelta R A B cover n) := by
  exact (mv_exact_delta_iota R A B cover n).epi_f
    ((isZero_mvSum R A B n hA hB).eq_zero_of_tgt _)

theorem isIso_mvDelta (cover : interior A ∪ interior B = Set.univ) (n : ℕ)
    (hA1 : IsZero (Habs R (n+1) (TopCat.of A)))
    (hB1 : IsZero (Habs R (n+1) (TopCat.of B)))
    (hA0 : IsZero (Habs R n (TopCat.of A)))
    (hB0 : IsZero (Habs R n (TopCat.of B))) :
    IsIso (mvDelta R A B cover n) := by
  letI := mono_mvDelta R A B cover n hA1 hB1
  letI := epi_mvDelta R A B cover n hA0 hB0
  exact isIso_of_mono_of_epi _

/-- The suspension-step isomorphism supplied by an actual contractible cover. -/
def mvDeltaIso_of_contractible (cover : interior A ∪ interior B = Set.univ)
    (n : ℕ) [ContractibleSpace A] [ContractibleSpace B] :
    Habs R (n+2) X ≅ Habs R (n+1) (TopCat.of (A ∩ B : Set X)) := by
  letI := isIso_mvDelta R A B cover (n+1)
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1+1) (by omega) (TopCat.of A))
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1+1) (by omega) (TopCat.of B))
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega) (TopCat.of A))
    (NRR.PrimePowerTopology.isZero_Habs_of_contractible R (n+1) (by omega) (TopCat.of B))
  exact asIso (mvDelta R A B cover (n+1))

section Naturality
variable {Y : TopCat.{0}} (C D : Set Y)
variable (f : X ⟶ Y) (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)

/-- The homology map of an ordered map of covers on the direct-sum term. -/
def mvSumMap (n : ℕ) : mvSum R A B n ⟶ mvSum R C D n :=
  biprod.map (HabsMap R n (mvRestrictMap A C f hA))
    (HabsMap R n (mvRestrictMap B D f hB))

@[reassoc]
theorem mvIota_naturality (n : ℕ) :
    mvIota R A B n ≫ mvSumMap R A B C D f hA hB n =
      HabsMap R n (mvIntersectionMap A B C D f hA hB) ≫ mvIota R C D n := by
  apply biprod.hom_ext <;>
    simp [mvIota, mvSumMap, ← HabsMap_comp]

@[reassoc]
theorem mvKappa_naturality (n : ℕ) :
    mvKappa R A B n ≫ HabsMap R n f =
      mvSumMap R A B C D f hA hB n ≫ mvKappa R C D n := by
  rw [mvKappa_eq_desc, mvKappa_eq_desc]
  apply biprod.hom_ext' <;>
    simp [mvSumMap, ← HabsMap_comp]

@[reassoc]
theorem mvSmallHomologyIso_naturality
    (coverX : interior A ∪ interior B = Set.univ)
    (coverY : interior C ∪ interior D = Set.univ) (n : ℕ) :
    HomologicalComplex.homologyMap (mvSmallChainMap R A B C D f hA hB) n ≫
        (mvSmallHomologyIso R C D coverY n).hom =
      (mvSmallHomologyIso R A B coverX n).hom ≫ HabsMap R n f := by
  simp only [mvSmallHomologyIso_hom, ← HomologicalComplex.homologyMap_comp,
    mvSmallChainMap_incl]

/-- Naturality of the actual connecting morphism for any map of ordered covers. -/
@[reassoc]
theorem mvDelta_naturality
    (coverX : interior A ∪ interior B = Set.univ)
    (coverY : interior C ∪ interior D = Set.univ) (n : ℕ) :
    mvDelta R A B coverX n ≫ HabsMap R n (mvIntersectionMap A B C D f hA hB) =
      HabsMap R (n+1) f ≫ mvDelta R C D coverY n := by
  have hi :
      (mvSmallHomologyIso R A B coverX (n+1)).inv ≫
          HomologicalComplex.homologyMap (mvSmallChainMap R A B C D f hA hB) (n+1) =
        HabsMap R (n+1) f ≫ (mvSmallHomologyIso R C D coverY (n+1)).inv := by
    apply (cancel_mono (mvSmallHomologyIso R C D coverY (n+1)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [mvSmallHomologyIso_naturality R A B C D f hA hB coverX coverY]
    simp only [Iso.inv_hom_id_assoc]
  unfold mvDelta
  rw [Category.assoc, mvSmallDelta_naturality, ← Category.assoc, hi, Category.assoc]

end Naturality
end NRR.SingularHomology
