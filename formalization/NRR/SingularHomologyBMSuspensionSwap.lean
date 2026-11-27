import NRR.SingularHomologyMayerVietorisCover

/-! The sign in Mayer--Vietoris when a map exchanges the two cover pieces.
This supplies the orientation sign for the real suspension coordinate. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology

namespace NRR.SingularHomology
variable (R : Type) [Ring R]
variable {X Y : TopCat.{0}} (A B : Set X) (C D : Set Y)
variable (f : X ⟶ Y) (hA : Set.MapsTo f A D) (hB : Set.MapsTo f B C)

/-- The map on the overlap, reordered after exchanging cover pieces. -/
def mvSwappedIntersectionMap : TopCat.of (A ∩ B : Set X) ⟶
    TopCat.of (C ∩ D : Set Y) :=
  TopCat.ofHom ⟨fun x => ⟨f x, hB x.property.2, hA x.property.1⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[reassoc (attr := simp)]
theorem mvSwappedIntersectionMap_left :
    mvSwappedIntersectionMap A B C D f hA hB ≫ mvInclLeft C D =
      mvInclRight A B ≫ mvRestrictMap B C f hB := rfl

@[reassoc (attr := simp)]
theorem mvSwappedIntersectionMap_right :
    mvSwappedIntersectionMap A B C D f hA hB ≫ mvInclRight C D =
      mvInclLeft A B ≫ mvRestrictMap A D f hA := rfl

private theorem mono_smallIncl {Z : TopCat.{0}} (E F : Set Z) :
    Mono (mvSmallIncl (R := R) E F) := by
  unfold mvSmallIncl
  infer_instance

theorem mvSwappedSmallChainMap_condition :
    simplicialChainMap R (mvQa A B) ≫
        (CsingMap R (mvRestrictMap A D f hA) ≫ simplicialChainMap R (mvPb C D)) =
      simplicialChainMap R (mvQb A B) ≫
        (CsingMap R (mvRestrictMap B C f hB) ≫ simplicialChainMap R (mvPa C D)) := by
  letI := mono_smallIncl R C D
  apply (cancel_mono (mvSmallIncl (R := R) C D)).mp
  simp only [Category.assoc, mvPa_smallIncl, mvPb_smallIncl]
  change CsingMap R (mvInclLeft A B) ≫ CsingMap R (mvRestrictMap A D f hA) ≫
      CsingMap R (subIncl D) =
    CsingMap R (mvInclRight A B) ≫ CsingMap R (mvRestrictMap B C f hB) ≫
      CsingMap R (subIncl C)
  simp only [← CsingMap_comp]
  congr 1

/-- The actual map on small chains for a map exchanging the pieces. -/
def mvSwappedSmallChainMap :
    mvSmallComplex (R := R) A B ⟶ mvSmallComplex (R := R) C D :=
  (mvChain_isPushout (R := R) A B).desc
    (CsingMap R (mvRestrictMap A D f hA) ≫ simplicialChainMap R (mvPb C D))
    (CsingMap R (mvRestrictMap B C f hB) ≫ simplicialChainMap R (mvPa C D))
    (mvSwappedSmallChainMap_condition R A B C D f hA hB)

@[reassoc (attr := simp)]
theorem mvPa_mvSwappedSmallChainMap :
    simplicialChainMap R (mvPa A B) ≫ mvSwappedSmallChainMap R A B C D f hA hB =
      CsingMap R (mvRestrictMap A D f hA) ≫ simplicialChainMap R (mvPb C D) :=
  (mvChain_isPushout (R := R) A B).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem mvPb_mvSwappedSmallChainMap :
    simplicialChainMap R (mvPb A B) ≫ mvSwappedSmallChainMap R A B C D f hA hB =
      CsingMap R (mvRestrictMap B C f hB) ≫ simplicialChainMap R (mvPa C D) :=
  (mvChain_isPushout (R := R) A B).inr_desc _ _ _

@[reassoc]
theorem mvSwappedSmallChainMap_incl :
    mvSwappedSmallChainMap R A B C D f hA hB ≫ mvSmallIncl (R := R) C D =
      mvSmallIncl (R := R) A B ≫ CsingMap R f := by
  apply (mvChain_isPushout (R := R) A B).hom_ext
  · rw [← Category.assoc, mvPa_mvSwappedSmallChainMap, Category.assoc, mvPb_smallIncl,
      ← Category.assoc, mvPa_smallIncl, ← CsingMap_comp, ← CsingMap_comp,
      mvRestrictMap_subIncl]
  · rw [← Category.assoc, mvPb_mvSwappedSmallChainMap, Category.assoc, mvPa_smallIncl,
      ← Category.assoc, mvPb_smallIncl, ← CsingMap_comp, ← CsingMap_comp,
      mvRestrictMap_subIncl]

/-- Swapping the summands changes the sign on the union term of the
short exact sequence, since its second map is the difference of inclusions. -/
def mvSwappedShortComplexMap : mvSC (R := R) A B ⟶ mvSC (R := R) C D where
  τ₁ := CsingMap R (mvSwappedIntersectionMap A B C D f hA hB)
  τ₂ := biprod.lift (biprod.snd ≫ CsingMap R (mvRestrictMap B C f hB))
    (biprod.fst ≫ CsingMap R (mvRestrictMap A D f hA))
  τ₃ := -mvSwappedSmallChainMap R A B C D f hA hB
  comm₁₂ := by
    apply biprod.hom_ext
    · change CsingMap R (mvSwappedIntersectionMap A B C D f hA hB) ≫
          (biprod.lift (CsingMap R (mvInclLeft C D)) (CsingMap R (mvInclRight C D))) ≫
          biprod.fst = _
      simp [mvSC, mvShortComplex, Category.assoc, ← CsingMap_comp]
      exact CsingMap_comp R _ _
    · change CsingMap R (mvSwappedIntersectionMap A B C D f hA hB) ≫
          (biprod.lift (CsingMap R (mvInclLeft C D)) (CsingMap R (mvInclRight C D))) ≫
          biprod.snd = _
      simp [mvSC, mvShortComplex, Category.assoc, ← CsingMap_comp]
      exact CsingMap_comp R _ _
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp [mvSC, mvShortComplex, Category.assoc, mvPa_mvSwappedSmallChainMap]
    · simp [mvSC, mvShortComplex, Category.assoc, mvPb_mvSwappedSmallChainMap]

/-- Signed naturality on actual small-chain homology. -/
theorem mvSwappedSmallDelta_naturality (n : ℕ) :
    mvSmallDelta R A B n ≫
        HabsMap R n (mvSwappedIntersectionMap A B C D f hA hB) =
      -(HomologicalComplex.homologyMap
        (mvSwappedSmallChainMap R A B C D f hA hB) (n+1) ≫ mvSmallDelta R C D n) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (mvSwappedShortComplexMap R A B C D f hA hB) (mvSC_shortExact (R := R) A B)
      (mvSC_shortExact (R := R) C D) (n+1) n rfl
  simpa only [mvSwappedShortComplexMap, HomologicalComplex.homologyMap_neg,
    Preadditive.neg_comp] using h

/-- Exchanging the two pieces reverses the sign of the genuine singular
Mayer--Vietoris connecting map. -/
@[reassoc]
theorem mvDelta_swapped_naturality
    (coverX : interior A ∪ interior B = Set.univ)
    (coverY : interior C ∪ interior D = Set.univ) (n : ℕ) :
    mvDelta R A B coverX n ≫
        HabsMap R n (mvSwappedIntersectionMap A B C D f hA hB) =
      -(HabsMap R (n+1) f ≫ mvDelta R C D coverY n) := by
  have hi :
      (mvSmallHomologyIso R A B coverX (n+1)).inv ≫
          HomologicalComplex.homologyMap
            (mvSwappedSmallChainMap R A B C D f hA hB) (n+1) =
        HabsMap R (n+1) f ≫ (mvSmallHomologyIso R C D coverY (n+1)).inv := by
    apply (cancel_mono (mvSmallHomologyIso R C D coverY (n+1)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (mvSmallHomologyIso R A B coverX (n+1)).inv ≫
        (HomologicalComplex.homologyMap
          (mvSwappedSmallChainMap R A B C D f hA hB) (n+1) ≫
          HomologicalComplex.homologyMap (mvSmallIncl (R := R) C D) (n+1)) = _
    rw [← HomologicalComplex.homologyMap_comp, mvSwappedSmallChainMap_incl,
      HomologicalComplex.homologyMap_comp]
    change (mvSmallHomologyIso R A B coverX (n+1)).inv ≫
      ((mvSmallHomologyIso R A B coverX (n+1)).hom ≫ HabsMap R (n+1) f) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  unfold mvDelta
  rw [Category.assoc, mvSwappedSmallDelta_naturality, Preadditive.comp_neg,
    ← Category.assoc, hi, Category.assoc]

end NRR.SingularHomology
