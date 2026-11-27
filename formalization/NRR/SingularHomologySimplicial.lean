/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The splitting below adapts Submission/Homology/SimplicialSplitting.lean from
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
It is generalized from abelian groups to modules over an arbitrary ring.
-/
import NRR.SingularHomologyPair
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
noncomputable section
namespace NRR.SingularHomology
variable (R : Type) [Ring R]
abbrev CsingSSetFunctor : SSet.{0} ⥤ ChainComplex (ModuleCat R) ℕ :=
  (SSet.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
abbrev CsingSSet (Y : SSet.{0}) : ChainComplex (ModuleCat R) ℕ :=
  (CsingSSetFunctor R).obj Y
def simplicialChainMap {X Y : SSet.{0}} (f : X ⟶ Y) : CsingSSet R X ⟶ CsingSSet R Y :=
  (CsingSSetFunctor R).map f
def simplexι {Y : SSet.{0}} {n : ℕ} (y : Y _⦋n⦌) :
    ModuleCat.of R R ⟶ (CsingSSet R Y).X n :=
  Sigma.ι (fun _ : Y _⦋n⦌ => ModuleCat.of R R) y
@[ext] theorem simplicialChain_hom_ext {Y : SSet.{0}} {n : ℕ} {T : ModuleCat R}
    {f g : (CsingSSet R Y).X n ⟶ T}
    (h : ∀ y, simplexι R y ≫ f = simplexι R y ≫ g) : f = g :=
  Sigma.hom_ext f g h
@[reassoc (attr := simp)] theorem simplexι_chainMap_f {X Y : SSet.{0}}
    (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    simplexι R x ≫ (simplicialChainMap R f).f n = simplexι R (f.app _ x) := by
  simp [simplexι, simplicialChainMap, CsingSSetFunctor, SSet.singularChainComplexFunctor, sigmaConst]
instance mono_simplicialChainMap {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] :
    Mono (simplicialChainMap R f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of R R)).map (f.app (op ⦋n⦌)))
  infer_instance

/-- The actual alternating boundary formula on a singular-chain generator. -/
@[reassoc] theorem simplexι_d {Y : SSet.{0}} {n : ℕ} (y : Y _⦋n + 1⦌) :
    simplexι R y ≫ (CsingSSet R Y).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexι R (Y.δ i y) := by
  simp [CsingSSet, CsingSSetFunctor, simplexι, SSet.singularChainComplexFunctor,
    Preadditive.comp_sum, SimplicialObject.δ, sigmaConst]

def ccDesc {Y : SSet.{0}} {n : ℕ} {T : ModuleCat R}
    (v : Y _⦋n⦌ → (ModuleCat.of R R ⟶ T)) : (CsingSSet R Y).X n ⟶ T :=
  Sigma.desc v
@[reassoc (attr := simp)] theorem ι_ccDesc {Y : SSet.{0}} {n : ℕ} {T : ModuleCat R}
    (v : Y _⦋n⦌ → (ModuleCat.of R R ⟶ T)) (y : Y _⦋n⦌) :
    simplexι R y ≫ ccDesc R v = v y := by
  exact Sigma.ι_desc v y
theorem biprodX_hom_ext {K L : ChainComplex (ModuleCat R) ℕ} {n : ℕ}
    {T : ModuleCat R} {f g : (K ⊞ L).X n ⟶ T}
    (h₁ : (biprod.inl : K ⟶ K ⊞ L).f n ≫ f =
      (biprod.inl : K ⟶ K ⊞ L).f n ≫ g)
    (h₂ : (biprod.inr : L ⟶ K ⊞ L).f n ≫ f =
      (biprod.inr : L ⟶ K ⊞ L).f n ≫ g) : f = g := by
  apply (cancel_epi (HomologicalComplex.biprodXIso K L n).inv).mp
  apply biprod.hom_ext'
  · simpa using h₁
  · simpa using h₂

section

variable {G Sa Sb D : SSet.{0}} (qa : G ⟶ Sa) (qb : G ⟶ Sb) (pa : Sa ⟶ D) (pb : Sb ⟶ D)

/-- The Mayer–Vietoris short complex `ℤ[G] ⟶ ℤ[Sa] ⊞ ℤ[Sb] ⟶ ℤ[D]`. -/
def mvShortComplex (h : qa ≫ pa = qb ≫ pb) : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk
    (biprod.lift (simplicialChainMap R qa)
      (simplicialChainMap R qb))
    (biprod.desc (simplicialChainMap R pa)
      (-simplicialChainMap R pb))
    (by
      simp only [simplicialChainMap]
      rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp, h,
        add_neg_cancel])

@[simp]
lemma mvShortComplex_X₁ (h : qa ≫ pa = qb ≫ pb) :
    (mvShortComplex (R := R) qa qb pa pb h).X₁ = CsingSSet R G := rfl

@[simp]
lemma mvShortComplex_X₃ (h : qa ≫ pa = qb ≫ pb) :
    (mvShortComplex (R := R) qa qb pa pb h).X₃ = CsingSSet R D := rfl

/-- The degreewise retraction of `ℤ[G] ⟶ ℤ[Sb]`: a simplex of `Sb` in the image of `G` is sent
back to its (unique) preimage, and all other simplices are sent to `0`. -/
def mvRetr (n : ℕ) : (CsingSSet R Sb).X n ⟶ (CsingSSet R G).X n :=
  open scoped Classical in
  ccDesc (R := R) fun y =>
    if h : ∃ z, qb.app (op ⦋n⦌) z = y then simplexι R h.choose else 0

@[reassoc]
lemma ι_mvRetr {n : ℕ} (hqb : Function.Injective (qb.app (op ⦋n⦌))) (z : G _⦋n⦌) :
    simplexι R (qb.app _ z) ≫ mvRetr (R := R) qb n =
      simplexι R z := by
  classical
  rw [mvRetr, ι_ccDesc (R := R), dif_pos ⟨z, rfl⟩]
  congr 1
  exact hqb (Exists.choose_spec (⟨z, rfl⟩ : ∃ w, qb.app (op ⦋n⦌) w = qb.app _ z))

@[reassoc]
lemma ι_mvRetr_of_not_mem {n : ℕ} (y : Sb _⦋n⦌) (h : ¬ ∃ z, qb.app (op ⦋n⦌) z = y) :
    simplexι R y ≫ mvRetr (R := R) qb n = 0 := by
  classical
  rw [mvRetr, ι_ccDesc (R := R), dif_neg h]

/-- The chosen inverse on basis elements retracts any injective simplicial map
in each chain degree. This is a degreewise splitting, not a chain retraction. -/
theorem simplicialChainMap_f_comp_mvRetr {n : ℕ}
    (hqb : Function.Injective (qb.app (op ⦋n⦌))) :
    (simplicialChainMap R qb).f n ≫ mvRetr R qb n = 𝟙 _ := by
  apply simplicialChain_hom_ext R
  intro z
  rw [simplexι_chainMap_f_assoc, ι_mvRetr R qb hqb, Category.comp_id]

variable {qa qb pa pb} in
/-- The degreewise section of `ℤ[Sa] ⊞ ℤ[Sb] ⟶ ℤ[D]`: a simplex of `D` coming from `Sa` is sent
to its preimage in the first summand, and a simplex coming only from `Sb` is sent to minus its
preimage in the second summand. -/
def mvSect {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d)) :
    (CsingSSet R D).X n ⟶ (CsingSSet R Sa ⊞ CsingSSet R Sb).X n :=
  open scoped Classical in
  ccDesc (R := R) fun d =>
    if h : ∃ x, pa.app (op ⦋n⦌) x = d then
      simplexι R h.choose ≫ (biprod.inl : CsingSSet R Sa ⟶ _).f n
    else
      -(simplexι R ((hcover d).resolve_left h).choose ≫
        (biprod.inr : CsingSSet R Sb ⟶ _).f n)

variable {qa qb pa pb}

@[reassoc]
lemma ι_mvSect_of_mem {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hpa : Function.Injective (pa.app (op ⦋n⦌))) (x : Sa _⦋n⦌) :
    simplexι R (pa.app _ x) ≫ mvSect (R := R) hcover =
      simplexι R x ≫ (biprod.inl : CsingSSet R Sa ⟶ _).f n := by
  classical
  rw [mvSect, ι_ccDesc (R := R), dif_pos ⟨x, rfl⟩]
  congr 2
  exact hpa (Exists.choose_spec (⟨x, rfl⟩ : ∃ w, pa.app (op ⦋n⦌) w = pa.app _ x))

@[reassoc]
lemma ι_mvSect_of_not_mem {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hpb : Function.Injective (pb.app (op ⦋n⦌))) (y : Sb _⦋n⦌)
    (h : ¬ ∃ x, pa.app (op ⦋n⦌) x = pb.app _ y) :
    simplexι R (pb.app _ y) ≫ mvSect (R := R) hcover =
      -(simplexι R y ≫ (biprod.inr : CsingSSet R Sb ⟶ _).f n) := by
  classical
  rw [mvSect, ι_ccDesc (R := R), dif_neg h]
  congr 3
  exact hpb (Exists.choose_spec (((hcover (pb.app _ y)).resolve_left h)))

@[reassoc]
lemma ι_mvLift {n : ℕ} (z : G _⦋n⦌) :
    simplexι R z ≫
        (biprod.lift (simplicialChainMap R qa)
          (simplicialChainMap R qb)).f n =
      simplexι R (qa.app _ z) ≫ (biprod.inl : CsingSSet R Sa ⟶ _).f n +
        simplexι R (qb.app _ z) ≫ (biprod.inr : CsingSSet R Sb ⟶ _).f n := by
  rw [biprod.lift_eq]
  simp [HomologicalComplex.add_f_apply]

/-- `mvRetr (R := R)` is a retraction of the first map of the Mayer–Vietoris short complex. -/
lemma mvLift_comp_mvRetr {n : ℕ} (hqb : Function.Injective (qb.app (op ⦋n⦌))) :
    (biprod.lift (simplicialChainMap R qa)
        (simplicialChainMap R qb)).f n ≫
      ((biprod.snd : CsingSSet R Sa ⊞ CsingSSet R Sb ⟶ _).f n ≫ mvRetr (R := R) qb n) =
      𝟙 ((CsingSSet R G).X n) := by
  rw [← Category.assoc, HomologicalComplex.biprod_lift_snd_f]
  refine simplicialChain_hom_ext R fun z => ?_
  rw [simplexι_chainMap_f_assoc, ι_mvRetr (R := R) qb hqb, Category.comp_id]

/-- `mvSect (R := R)` is a section of the second map of the Mayer–Vietoris short complex. -/
lemma mvSect_comp_mvDesc {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hpa : Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : Function.Injective (pb.app (op ⦋n⦌))) :
    mvSect (R := R) hcover ≫ (biprod.desc (simplicialChainMap R pa)
        (-simplicialChainMap R pb)).f n = 𝟙 ((CsingSSet R D).X n) := by
  refine simplicialChain_hom_ext R fun d => ?_
  rw [Category.comp_id]
  by_cases hd : ∃ x, pa.app (op ⦋n⦌) x = d
  · obtain ⟨x, rfl⟩ := hd
    rw [ι_mvSect_of_mem_assoc (R := R) hcover hpa, HomologicalComplex.biprod_inl_desc_f,
      simplexι_chainMap_f]
  · obtain ⟨y, rfl⟩ := (hcover d).resolve_left hd
    rw [ι_mvSect_of_not_mem_assoc (R := R) hcover hpb y hd, Preadditive.neg_comp, Category.assoc,
      HomologicalComplex.biprod_inr_desc_f, HomologicalComplex.neg_f_apply,
      Preadditive.comp_neg, neg_neg, simplexι_chainMap_f]

/-- The retraction and the section add up to the identity. -/
lemma mvRetr_add_mvSect {n : ℕ}
    (h : qa ≫ pa = qb ≫ pb)
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hqb : Function.Injective (qb.app (op ⦋n⦌)))
    (hpa : Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : Function.Injective (pb.app (op ⦋n⦌)))
    (hinter : ∀ (x : Sa _⦋n⦌) (y : Sb _⦋n⦌),
      pa.app (op ⦋n⦌) x = pb.app (op ⦋n⦌) y → ∃ z, qb.app (op ⦋n⦌) z = y) :
    ((biprod.snd : CsingSSet R Sa ⊞ CsingSSet R Sb ⟶ _).f n ≫ mvRetr (R := R) qb n) ≫
        (biprod.lift (simplicialChainMap R qa)
          (simplicialChainMap R qb)).f n +
      (biprod.desc (simplicialChainMap R pa)
          (-simplicialChainMap R pb)).f n ≫ mvSect (R := R) hcover =
      𝟙 ((CsingSSet R Sa ⊞ CsingSSet R Sb).X n) := by
  refine biprodX_hom_ext R ?_ ?_
  · simp only [Preadditive.comp_add, Category.assoc,
      HomologicalComplex.biprod_inl_snd_f_assoc, zero_comp, zero_add,
      HomologicalComplex.biprod_inl_desc_f_assoc, Category.comp_id]
    refine simplicialChain_hom_ext R fun x => ?_
    rw [simplexι_chainMap_f_assoc, ι_mvSect_of_mem (R := R) hcover hpa]
  · simp only [Preadditive.comp_add, Category.assoc,
      HomologicalComplex.biprod_inr_snd_f_assoc,
      HomologicalComplex.biprod_inr_desc_f_assoc, Category.comp_id,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp]
    rw [← sub_eq_add_neg, sub_eq_iff_eq_add]
    refine simplicialChain_hom_ext R fun y => ?_
    rw [Preadditive.comp_add]
    by_cases hy : ∃ z, qb.app (op ⦋n⦌) z = y
    · obtain ⟨z, rfl⟩ := hy
      have hz : pb.app (op ⦋n⦌) (qb.app (op ⦋n⦌) z) = pa.app (op ⦋n⦌) (qa.app (op ⦋n⦌) z) := by
        have hh := NatTrans.congr_app h (op ⦋n⦌)
        have hz' := congrArg (fun u : G _⦋n⦌ ⟶ D _⦋n⦌ => u z) hh
        simpa using hz'.symm
      rw [ι_mvRetr_assoc (R := R) qb hqb, ι_mvLift (R := R), simplexι_chainMap_f_assoc, hz,
        ι_mvSect_of_mem (R := R) hcover hpa, add_comm]
    · rw [ι_mvRetr_of_not_mem_assoc (R := R) qb y hy, zero_comp, simplexι_chainMap_f_assoc,
        ι_mvSect_of_not_mem (R := R) hcover hpb y (fun ⟨x, hx⟩ => hy (hinter x y hx)),
        add_neg_cancel]

variable (qa qb pa pb) in
/-- The Mayer–Vietoris short complex is degreewise split. -/
def mvSplitting (h : qa ≫ pa = qb ≫ pb) (n : ℕ)
    (hqb : Function.Injective (qb.app (op ⦋n⦌)))
    (hpa : Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : Function.Injective (pb.app (op ⦋n⦌)))
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hinter : ∀ (x : Sa _⦋n⦌) (y : Sb _⦋n⦌),
      pa.app (op ⦋n⦌) x = pb.app (op ⦋n⦌) y → ∃ z, qb.app (op ⦋n⦌) z = y) :
    ShortComplex.Splitting
      ((mvShortComplex (R := R) qa qb pa pb h).map (HomologicalComplex.eval _ _ n)) where
  r := (biprod.snd : CsingSSet R Sa ⊞ CsingSSet R Sb ⟶ _).f n ≫ mvRetr (R := R) qb n
  s := mvSect (R := R) hcover
  f_r := mvLift_comp_mvRetr (R := R) hqb
  s_g := mvSect_comp_mvDesc (R := R) hcover hpa hpb
  id := mvRetr_add_mvSect (R := R) h hcover hqb hpa hpb hinter

/-- The Mayer–Vietoris sequence of chain complexes is short exact. -/
theorem mvShortComplex_shortExact (h : qa ≫ pa = qb ≫ pb)
    (hqb : ∀ n : ℕ, Function.Injective (qb.app (op ⦋n⦌)))
    (hpa : ∀ n : ℕ, Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : ∀ n : ℕ, Function.Injective (pb.app (op ⦋n⦌)))
    (hcover : ∀ (n : ℕ) (d : D _⦋n⦌),
      (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hinter : ∀ (n : ℕ) (x : Sa _⦋n⦌) (y : Sb _⦋n⦌),
      pa.app (op ⦋n⦌) x = pb.app (op ⦋n⦌) y → ∃ z, qb.app (op ⦋n⦌) z = y) :
    (mvShortComplex (R := R) qa qb pa pb h).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (mvSplitting (R := R) qa qb pa pb h n (hqb n) (hpa n) (hpb n) (hcover n) (hinter n)).shortExact)

end


end NRR.SingularHomology
