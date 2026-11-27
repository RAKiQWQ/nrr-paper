/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from Submission/Homology/Excision.lean in
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
Generalized to modules over an arbitrary ring.
-/
import NRR.SingularHomologySmallChains
import NRR.SingularHomologyRelMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
namespace NRR.SingularHomology

section CokernelPushout
variable {C : Type*} [Category C] [HasZeroMorphisms C]
variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
variable [HasCokernel f] [HasCokernel inr]

/-- Pushout identifies the two actual cokernel objects. -/
def cokernelPushoutIso (sq : IsPushout f g inl inr) : cokernel f ≅ cokernel inr where
  hom := cokernel.map f inr g inl sq.w
  inv := cokernel.desc inr (sq.desc (cokernel.π f) 0 (by simp)) (by simp)
  hom_inv_id := by
    apply (cancel_epi (cokernel.π f)).mp
    simp [cokernel.map, Category.assoc]
  inv_hom_id := by
    apply (cancel_epi (cokernel.π inr)).mp
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    apply sq.hom_ext
    · simp
    · simp
end CokernelPushout

variable (R : Type) [Ring R]
variable {X : TopCat.{0}} (A B : Set X)

/-- The square of singular chain complexes attached to the small-simplices cover is a pushout. -/
theorem mvChain_isPushout :
    IsPushout
      (simplicialChainMap R (mvQa A B))
      (simplicialChainMap R (mvQb A B))
      (simplicialChainMap R (mvPa A B))
      (simplicialChainMap R (mvPb A B)) := by
  let qa := simplicialChainMap R (mvQa A B)
  let qb := simplicialChainMap R (mvQb A B)
  let pa := simplicialChainMap R (mvPa A B)
  let pb := simplicialChainMap R (mvPb A B)
  let h := (mvSC_shortExact (R := R) A B).gIsCokernel
  have hcond : qa ≫ pa = qb ≫ pb := by
    dsimp [qa, qb, pa, pb, simplicialChainMap]
    rw [← (CsingSSetFunctor R) |>.map_comp,
      ← (CsingSSetFunctor R) |>.map_comp,
      mvQa_comp_mvPa]
  have hzero (s : PushoutCocone qa qb) :
      biprod.lift qa qb ≫ biprod.desc s.inl (-s.inr) = 0 := by
    simp only [biprod.lift_desc, Preadditive.comp_neg, s.condition, add_neg_cancel]
  let desc (s : PushoutCocone qa qb) : mvSmallComplex (R := R) A B ⟶ s.pt :=
    h.desc (CokernelCofork.ofπ (biprod.desc s.inl (-s.inr)) (hzero s))
  have hfac (s : PushoutCocone qa qb) :
      biprod.desc pa (-pb) ≫ desc s = biprod.desc s.inl (-s.inr) := by
    exact h.fac (CokernelCofork.ofπ (biprod.desc s.inl (-s.inr)) (hzero s))
      WalkingParallelPair.one
  have fac_left (s : PushoutCocone qa qb) : pa ≫ desc s = s.inl := by
    calc
      pa ≫ desc s = biprod.inl ≫ biprod.desc pa (-pb) ≫ desc s := by simp
      _ = biprod.inl ≫ biprod.desc s.inl (-s.inr) := by rw [hfac]
      _ = s.inl := by simp
  have fac_right (s : PushoutCocone qa qb) : pb ≫ desc s = s.inr := by
    have hneg : (-pb) ≫ desc s = -s.inr := by
      calc
        (-pb) ≫ desc s = biprod.inr ≫ biprod.desc pa (-pb) ≫ desc s := by simp
        _ = biprod.inr ≫ biprod.desc s.inl (-s.inr) := by rw [hfac]
        _ = -s.inr := by simp
    simpa only [Preadditive.neg_comp, neg_inj] using hneg
  exact IsPushout.of_isColimit
    (PushoutCocone.IsColimit.mk hcond desc fac_left fac_right (fun s m hm₁ hm₂ => by
      apply Cofork.IsColimit.hom_ext h
      have heq : biprod.desc pa (-pb) ≫ m = biprod.desc pa (-pb) ≫ desc s := by
        apply biprod.hom_ext' <;>
          simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Preadditive.neg_comp,
            hm₁, hm₂, fac_left, fac_right]
      exact heq))

/-- The relative chain complex of the small-simplices pair `(C^{A,B}_*(X), C_*(B))`. -/
abbrev mvSmallRelComplex : ChainComplex (ModuleCat R) ℕ :=
  cokernel (simplicialChainMap R (mvPb A B))

instance mono_mvInclLeft : Mono (mvInclLeft A B) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  exact Subtype.ext (congrArg (fun z : A => (z : X)) h)

instance mono_mvInclRight : Mono (mvInclRight A B) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  exact Subtype.ext (congrArg (fun z : B => (z : X)) h)

/-- The pushout square induces the chain map from `(A, A ∩ B)` to the relative small-chain
complex. -/
noncomputable def mvExcisionToSmallChainMap :
    relComplex (R := R) (mvInclLeft A B) ⟶ mvSmallRelComplex (R := R) A B :=
  let sq := mvChain_isPushout (R := R) A B
  cokernel.map
    (simplicialChainMap R (mvQa A B))
    (simplicialChainMap R (mvPb A B))
    (simplicialChainMap R (mvQb A B))
    (simplicialChainMap R (mvPa A B)) sq.w

/-- The pushout comparison of relative chain complexes is an isomorphism. -/
theorem isIso_mvExcisionToSmallChainMap :
    IsIso (mvExcisionToSmallChainMap (R := R) A B) := by
  exact (cokernelPushoutIso (mvChain_isPushout (R := R) A B)).isIso_hom

instance mono_mvPb : Mono (mvPb A B) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  change Mono ((mvPb A B).app (op ⦋n.unop.len⦌))
  rw [CategoryTheory.mono_iff_injective]
  exact injective_mvPb_app A B n.unop.len

/-- The short exact sequence defining relative chains for the small-simplices pair. -/
noncomputable def mvSmallRelShortComplex :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  let pb := simplicialChainMap R (mvPb A B)
  ShortComplex.mk pb (cokernel.π pb) (cokernel.condition pb)

theorem mvSmallRelShortComplex_shortExact :
    (mvSmallRelShortComplex (R := R) A B).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    change Mono (simplicialChainMap R (mvPb A B))
    exact mono_simplicialChainMap R (mvPb A B)
  epi_g := coequalizer.π_epi

/-- Inclusion of small chains in all singular chains induces a map of relative complexes. -/
noncomputable def mvSmallRelMap :
    mvSmallRelComplex (R := R) A B ⟶ relComplex (R := R) (subIncl B) :=
  cokernel.map
    (simplicialChainMap R (mvPb A B))
    (CsingMap R (subIncl B)) (𝟙 _) (mvSmallIncl (R := R) A B)
    ((mvPb_smallIncl (R := R) A B).trans (Category.id_comp _).symm)

/-- The morphism of relative short exact sequences induced by inclusion of small chains. -/
noncomputable def mvSmallRelShortComplexMap :
    mvSmallRelShortComplex (R := R) A B ⟶ relShortComplex (R := R) (subIncl B) where
  τ₁ := 𝟙 _
  τ₂ := mvSmallIncl (R := R) A B
  τ₃ := mvSmallRelMap (R := R) A B
  comm₁₂ := by
    change (𝟙 _ : Csing R (TopCat.of B) ⟶ Csing R (TopCat.of B)) ≫ CsingMap R (subIncl B) =
      simplicialChainMap R (mvPb A B) ≫ mvSmallIncl (R := R) A B
    rw [Category.id_comp, mvPb_smallIncl (R := R)]
  comm₂₃ := by
    change mvSmallIncl (R := R) A B ≫ relProj (R := R) (subIncl B) =
      cokernel.π (simplicialChainMap R (mvPb A B)) ≫
        mvSmallRelMap (R := R) A B
    symm
    change cokernel.π (simplicialChainMap R (mvPb A B)) ≫
        cokernel.desc (simplicialChainMap R (mvPb A B))
          (mvSmallIncl (R := R) A B ≫ cokernel.π (CsingMap R (subIncl B))) _ =
      mvSmallIncl (R := R) A B ≫ cokernel.π (CsingMap R (subIncl B))
    rw [cokernel.π_desc]

/-- The pushout and small-simplices comparisons compose to the canonical relative chain map. -/
theorem mvExcisionChainMap_comp :
    mvExcisionToSmallChainMap (R := R) A B ≫ mvSmallRelMap (R := R) A B =
      relComplexMap (R := R) (mvInclLeft A B) (subIncl B)
        (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B by rfl) := by
  apply (coequalizer.π_epi : Epi (relProj (R := R) (mvInclLeft A B))).left_cancellation
  change cokernel.π (CsingMap R (mvInclLeft A B)) ≫
      (mvExcisionToSmallChainMap (R := R) A B ≫ mvSmallRelMap (R := R) A B) =
    cokernel.π (CsingMap R (mvInclLeft A B)) ≫
      relComplexMap (R := R) (mvInclLeft A B) (subIncl B) _
  rw [← Category.assoc]
  change (cokernel.π (simplicialChainMap R (mvQa A B)) ≫
      cokernel.desc (simplicialChainMap R (mvQa A B))
        (simplicialChainMap R (mvPa A B) ≫
          cokernel.π (simplicialChainMap R (mvPb A B))) _) ≫
      mvSmallRelMap (R := R) A B =
    cokernel.π (CsingMap R (mvInclLeft A B)) ≫
      relComplexMap (R := R) (mvInclLeft A B) (subIncl B) _
  rw [cokernel.π_desc, Category.assoc]
  change simplicialChainMap R (mvPa A B) ≫
      (cokernel.π (simplicialChainMap R (mvPb A B)) ≫
        cokernel.desc (simplicialChainMap R (mvPb A B))
          (mvSmallIncl (R := R) A B ≫ cokernel.π (CsingMap R (subIncl B))) _) =
    cokernel.π (CsingMap R (mvInclLeft A B)) ≫
      relComplexMap (R := R) (mvInclLeft A B) (subIncl B) _
  rw [cokernel.π_desc, ← Category.assoc, mvPa_smallIncl (R := R)]
  change CsingMap R (subIncl A) ≫ relProj (R := R) (subIncl B) =
    relProj (R := R) (mvInclLeft A B) ≫ relComplexMap (R := R) (mvInclLeft A B) (subIncl B) _
  exact (relProj_comp_relComplexMap (R := R) (mvInclLeft A B) (subIncl B) _).symm

/-- The canonical relative-homology excision map for a two-set cover. -/
def mvExcisionHrelMap (n : ℕ) : Hrel R n (mvInclLeft A B) ⟶ Hrel R n (subIncl B) :=
  HrelMap R n (mvInclLeft A B) (subIncl B)
    (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B by rfl)


end NRR.SingularHomology
