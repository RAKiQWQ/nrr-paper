import NRR.SingularHomologyMayerVietoris
import NRR.SingularHomologyExcisionSmall

/-! Naturality of the actual two-set Mayer--Vietoris connecting map.
The map on small chains is built by the proved chain pushout. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology
namespace NRR.SingularHomology
variable (R : Type) [Ring R]
variable {X Y : TopCat.{0}} (A B : Set X) (C D : Set Y)
variable (f : X ⟶ Y) (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)

def mvRestrictMap : TopCat.of A ⟶ TopCat.of C :=
  TopCat.ofHom ⟨fun x => ⟨f x, hA x.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def mvIntersectionMap : TopCat.of (A ∩ B : Set X) ⟶ TopCat.of (C ∩ D : Set Y) :=
  TopCat.ofHom ⟨fun x => ⟨f x, hA x.property.1, hB x.property.2⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[reassoc (attr := simp)]
theorem mvRestrictMap_subIncl :
    mvRestrictMap A C f hA ≫ subIncl C = subIncl A ≫ f := rfl

@[reassoc (attr := simp)]
theorem mvIntersectionMap_left :
    mvIntersectionMap A B C D f hA hB ≫ mvInclLeft C D =
      mvInclLeft A B ≫ mvRestrictMap A C f hA := rfl

@[reassoc (attr := simp)]
theorem mvIntersectionMap_right :
    mvIntersectionMap A B C D f hA hB ≫ mvInclRight C D =
      mvInclRight A B ≫ mvRestrictMap B D f hB := rfl

private theorem mono_mvSmallIncl' {Z : TopCat.{0}} (E F : Set Z) :
    Mono (mvSmallIncl (R := R) E F) := by
  unfold mvSmallIncl
  infer_instance

theorem mvSmallChainMap_condition :
    simplicialChainMap R (mvQa A B) ≫
        (CsingMap R (mvRestrictMap A C f hA) ≫ simplicialChainMap R (mvPa C D)) =
      simplicialChainMap R (mvQb A B) ≫
        (CsingMap R (mvRestrictMap B D f hB) ≫ simplicialChainMap R (mvPb C D)) := by
  letI := mono_mvSmallIncl' R C D
  apply (cancel_mono (mvSmallIncl (R := R) C D)).mp
  simp only [Category.assoc, mvPa_smallIncl, mvPb_smallIncl]
  change CsingMap R (mvInclLeft A B) ≫
      CsingMap R (mvRestrictMap A C f hA) ≫ CsingMap R (subIncl C) =
    CsingMap R (mvInclRight A B) ≫
      CsingMap R (mvRestrictMap B D f hB) ≫ CsingMap R (subIncl D)
  simp only [← CsingMap_comp]
  congr 1

def mvSmallChainMap :
    mvSmallComplex (R := R) A B ⟶ mvSmallComplex (R := R) C D :=
  (mvChain_isPushout (R := R) A B).desc
    (CsingMap R (mvRestrictMap A C f hA) ≫ simplicialChainMap R (mvPa C D))
    (CsingMap R (mvRestrictMap B D f hB) ≫ simplicialChainMap R (mvPb C D))
    (mvSmallChainMap_condition R A B C D f hA hB)

@[reassoc (attr := simp)]
theorem mvPa_mvSmallChainMap :
    simplicialChainMap R (mvPa A B) ≫ mvSmallChainMap R A B C D f hA hB =
      CsingMap R (mvRestrictMap A C f hA) ≫ simplicialChainMap R (mvPa C D) :=
  (mvChain_isPushout (R := R) A B).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem mvPb_mvSmallChainMap :
    simplicialChainMap R (mvPb A B) ≫ mvSmallChainMap R A B C D f hA hB =
      CsingMap R (mvRestrictMap B D f hB) ≫ simplicialChainMap R (mvPb C D) :=
  (mvChain_isPushout (R := R) A B).inr_desc _ _ _

@[reassoc]
theorem mvSmallChainMap_incl :
    mvSmallChainMap R A B C D f hA hB ≫ mvSmallIncl (R := R) C D =
      mvSmallIncl (R := R) A B ≫ CsingMap R f := by
  apply (mvChain_isPushout (R := R) A B).hom_ext
  · rw [← Category.assoc, mvPa_mvSmallChainMap, Category.assoc, mvPa_smallIncl,
      ← Category.assoc, mvPa_smallIncl, ← CsingMap_comp, ← CsingMap_comp,
      mvRestrictMap_subIncl]
  · rw [← Category.assoc, mvPb_mvSmallChainMap, Category.assoc, mvPb_smallIncl,
      ← Category.assoc, mvPb_smallIncl, ← CsingMap_comp, ← CsingMap_comp,
      mvRestrictMap_subIncl]

def mvShortComplexMap : mvSC (R := R) A B ⟶ mvSC (R := R) C D where
  τ₁ := CsingMap R (mvIntersectionMap A B C D f hA hB)
  τ₂ := biprod.map (CsingMap R (mvRestrictMap A C f hA))
    (CsingMap R (mvRestrictMap B D f hB))
  τ₃ := mvSmallChainMap R A B C D f hA hB
  comm₁₂ := by
    apply biprod.hom_ext
    · change CsingMap R (mvIntersectionMap A B C D f hA hB) ≫
          (biprod.lift (CsingMap R (mvInclLeft C D)) (CsingMap R (mvInclRight C D))) ≫
          biprod.fst =
        (biprod.lift (CsingMap R (mvInclLeft A B)) (CsingMap R (mvInclRight A B))) ≫
          biprod.map (CsingMap R (mvRestrictMap A C f hA))
            (CsingMap R (mvRestrictMap B D f hB)) ≫ biprod.fst
      simp only [biprod.lift_fst, biprod.map_fst,
        ← Category.assoc, biprod.lift_fst, ← CsingMap_comp, mvIntersectionMap_left]
    · change CsingMap R (mvIntersectionMap A B C D f hA hB) ≫
          (biprod.lift (CsingMap R (mvInclLeft C D)) (CsingMap R (mvInclRight C D))) ≫
          biprod.snd =
        (biprod.lift (CsingMap R (mvInclLeft A B)) (CsingMap R (mvInclRight A B))) ≫
          biprod.map (CsingMap R (mvRestrictMap A C f hA))
            (CsingMap R (mvRestrictMap B D f hB)) ≫ biprod.snd
      simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        ← Category.assoc, biprod.lift_snd, ← CsingMap_comp, mvIntersectionMap_right]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp [mvSC, mvShortComplex, Category.assoc, mvPa_mvSmallChainMap]
    · simp [mvSC, mvShortComplex, Category.assoc, mvPb_mvSmallChainMap]

/-- The actual signed connecting morphism commutes with every map of
ordered two-set covers. -/
theorem mvSmallDelta_naturality (n : ℕ) :
    mvSmallDelta R A B n ≫ HabsMap R n (mvIntersectionMap A B C D f hA hB) =
      HomologicalComplex.homologyMap (mvSmallChainMap R A B C D f hA hB) (n+1) ≫
        mvSmallDelta R C D n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (mvShortComplexMap R A B C D f hA hB) (mvSC_shortExact (R := R) A B)
      (mvSC_shortExact (R := R) C D) (n+1) n rfl

end NRR.SingularHomology
