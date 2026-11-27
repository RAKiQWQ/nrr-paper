/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from Submission/Model/Suspension.lean in akopjan/toptverbert-nandakumar,
revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic

noncomputable section

/-!
# The unreduced suspension of a topological space

Mathlib has no notion of suspension, so we build one. The unreduced suspension `Susp X` of a
topological space `X` is the quotient of `I × X` obtained by collapsing `{0} × X` to a single
point (the *south pole*) and `{1} × X` to a single point (the *north pole*).

## Main definitions

* `NRR.SuspensionGeometry.Susp X` — the unreduced suspension, with its quotient topology;
* `NRR.SuspensionGeometry.Susp.mk` — the quotient map `C(I × X, Susp X)`;
* `NRR.SuspensionGeometry.Susp.south`, `NRR.SuspensionGeometry.Susp.north` — the two cone points;
* `NRR.SuspensionGeometry.Susp.lift` — the universal property: a continuous map out of `I × X` which is
  constant on `{0} × X` and on `{1} × X` descends to `Susp X`;
* `NRR.SuspensionGeometry.Susp.height` — the well-defined suspension parameter `Susp X → I`;
* `NRR.SuspensionGeometry.Susp.map` — functoriality, together with `Susp.map_id` and `Susp.map_comp`.

We also record that `Susp X` is compact when `X` is, and Hausdorff when `X` is (no compactness
needed for the latter: the identifications only happen over the two endpoints of `I`).

Note that with this definition `Susp X` is empty when `X` is; the two cone points are therefore
only defined under a `[Nonempty X]` hypothesis.
-/

namespace NRR.SuspensionGeometry

open unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]

/-- The relation on `I × X` collapsing `{0} × X` to a point and `{1} × X` to a point. -/
def SuspRel (X : Type u) : I × X → I × X → Prop := fun a b =>
  a = b ∨ (a.1 = 0 ∧ b.1 = 0) ∨ (a.1 = 1 ∧ b.1 = 1)

theorem suspRel_equivalence (X : Type u) : Equivalence (SuspRel X) where
  refl _ := Or.inl rfl
  symm := by
    rintro a b (rfl | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨h₂, h₁⟩)
    · exact Or.inr (Or.inr ⟨h₂, h₁⟩)
  trans := by
    rintro a b c (rfl | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) (rfl | ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨h₃, h₄⟩)
    · exact Or.inr (Or.inr ⟨h₃, h₄⟩)
    · exact Or.inr (Or.inl ⟨h₁, h₂⟩)
    · exact Or.inr (Or.inl ⟨h₁, h₄⟩)
    · exact absurd (h₂.symm.trans h₃) (by norm_num)
    · exact Or.inr (Or.inr ⟨h₁, h₂⟩)
    · exact absurd (h₃.symm.trans h₂) (by norm_num)
    · exact Or.inr (Or.inr ⟨h₁, h₄⟩)

/-- The setoid on `I × X` underlying the unreduced suspension. -/
def suspSetoid (X : Type u) : Setoid (I × X) := ⟨SuspRel X, suspRel_equivalence X⟩

/-- The unreduced suspension of `X`: the quotient of `I × X` collapsing `{0} × X` to one point
and `{1} × X` to another. -/
def Susp (X : Type u) [TopologicalSpace X] : Type u := Quotient (suspSetoid X)

instance instTopologicalSpaceSusp : TopologicalSpace (Susp X) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

namespace Susp

/-- The quotient map `I × X → Susp X`. -/
def mk : C(I × X, Susp X) :=
  ⟨fun p => Quotient.mk (suspSetoid X) p, continuous_quot_mk⟩

theorem mk_apply (p : I × X) : (mk p : Susp X) = Quotient.mk (suspSetoid X) p := rfl

@[elab_as_elim]
theorem ind {motive : Susp X → Prop} (h : ∀ p : I × X, motive (mk p)) (q : Susp X) : motive q :=
  Quotient.ind h q

theorem mk_surjective : Function.Surjective (mk : I × X → Susp X) :=
  Quotient.mk_surjective

theorem mk_eq_mk {a b : I × X} : (mk a : Susp X) = mk b ↔ SuspRel X a b := Quotient.eq_iff_equiv

theorem mk_eq_mk_of_rel {a b : I × X} (h : SuspRel X a b) : (mk a : Susp X) = mk b :=
  mk_eq_mk.mpr h

theorem mk_zero_eq_mk_zero (x y : X) : (mk (0, x) : Susp X) = mk (0, y) :=
  mk_eq_mk_of_rel (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem mk_one_eq_mk_one (x y : X) : (mk (1, x) : Susp X) = mk (1, y) :=
  mk_eq_mk_of_rel (Or.inr (Or.inr ⟨rfl, rfl⟩))

instance instNonemptySusp [Nonempty X] : Nonempty (Susp X) := ⟨mk (0, Classical.arbitrary X)⟩

/-- The south pole of the suspension, the image of `{0} × X`. -/
noncomputable def south (X : Type u) [TopologicalSpace X] [Nonempty X] : Susp X :=
  mk (0, Classical.arbitrary X)

/-- The north pole of the suspension, the image of `{1} × X`. -/
noncomputable def north (X : Type u) [TopologicalSpace X] [Nonempty X] : Susp X :=
  mk (1, Classical.arbitrary X)

theorem mk_zero [Nonempty X] (x : X) : (mk (0, x) : Susp X) = south X :=
  mk_zero_eq_mk_zero x _

theorem mk_one [Nonempty X] (x : X) : (mk (1, x) : Susp X) = north X :=
  mk_one_eq_mk_one x _

instance instCompactSpaceSusp [CompactSpace X] : CompactSpace (Susp X) :=
  inferInstanceAs (CompactSpace (Quotient _))

/-- The universal property of the suspension: a continuous map `f : I × X → Y` which is constant
on `{0} × X` and on `{1} × X` descends to a continuous map `Susp X → Y`. -/
def lift (f : C(I × X, Y)) (h₀ : ∀ x y : X, f (0, x) = f (0, y))
    (h₁ : ∀ x y : X, f (1, x) = f (1, y)) : C(Susp X, Y) :=
  ⟨Quotient.lift f (by
      rintro ⟨t, x⟩ ⟨s, y⟩ (h | ⟨h, h'⟩ | ⟨h, h'⟩)
      · exact congrArg f h
      · simp only at h h'
        subst h; subst h'; exact h₀ x y
      · simp only at h h'
        subst h; subst h'; exact h₁ x y),
    f.continuous.quotient_lift _⟩

@[simp]
theorem lift_mk (f : C(I × X, Y)) (h₀ : ∀ x y : X, f (0, x) = f (0, y))
    (h₁ : ∀ x y : X, f (1, x) = f (1, y)) (p : I × X) : lift f h₀ h₁ (mk p) = f p := rfl

/-- The height function `Susp X → I`; it is well defined because the identifications only
happen inside a single level `{t} × X`. -/
def height : C(Susp X, I) :=
  lift ⟨fun p => p.1, continuous_fst⟩ (fun _ _ => rfl) (fun _ _ => rfl)

@[simp]
theorem height_mk (p : I × X) : height (mk p) = p.1 := rfl

theorem isQuotientMap_mk : Topology.IsQuotientMap (mk : I × X → Susp X) :=
  isQuotientMap_quot_mk

/-- The set of interior levels of the suspension parameter. -/
def openLevels : Set I := ({0} : Set I)ᶜ ∩ ({1} : Set I)ᶜ

theorem isOpen_openLevels : IsOpen (openLevels : Set I) :=
  isClosed_singleton.isOpen_compl.inter isClosed_singleton.isOpen_compl

/-- Over the interior levels the quotient map is injective, so boxes are saturated. -/
theorem preimage_image_prod (S : Set X) :
    (mk : I × X → Susp X) ⁻¹' (mk '' (openLevels ×ˢ S)) = openLevels ×ˢ S := by
  ext ⟨s, z⟩
  refine ⟨?_, fun h => ⟨(s, z), h, rfl⟩⟩
  rintro ⟨⟨t, w⟩, ⟨ht, hw⟩, heq⟩
  rcases mk_eq_mk.mp heq with h | ⟨h₁, -⟩ | ⟨h₁, -⟩
  · rw [← h]; exact ⟨ht, hw⟩
  · exact absurd h₁ ht.1
  · exact absurd h₁ ht.2

instance instT2SpaceSusp [T2Space X] : T2Space (Susp X) := by
  refine ⟨fun q q' hne => ?_⟩
  induction q using Susp.ind with
  | h p =>
    induction q' using Susp.ind with
    | h p' =>
      obtain ⟨t, x⟩ := p
      obtain ⟨s, y⟩ := p'
      by_cases hts : t = s
      · subst hts
        have hx : x ≠ y := fun h => hne (by rw [h])
        have ht : t ∈ openLevels := by
          refine ⟨fun h => hne ?_, fun h => hne ?_⟩
          · simp only [Set.mem_singleton_iff] at h
            subst h; exact mk_zero_eq_mk_zero x y
          · simp only [Set.mem_singleton_iff] at h
            subst h; exact mk_one_eq_mk_one x y
        obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hx
        refine ⟨mk '' (openLevels ×ˢ U), mk '' (openLevels ×ˢ V), ?_, ?_,
          ⟨(t, x), ⟨ht, hxU⟩, rfl⟩, ⟨(t, y), ⟨ht, hyV⟩, rfl⟩, ?_⟩
        · rw [← isQuotientMap_mk.isOpen_preimage, preimage_image_prod]
          exact isOpen_openLevels.prod hU
        · rw [← isQuotientMap_mk.isOpen_preimage, preimage_image_prod]
          exact isOpen_openLevels.prod hV
        · rw [Set.disjoint_left]
          rintro q hq hq'
          induction q using Susp.ind with
          | h r =>
            have h₁ : r ∈ openLevels ×ˢ U := by rw [← preimage_image_prod U]; exact hq
            have h₂ : r ∈ openLevels ×ˢ V := by rw [← preimage_image_prod V]; exact hq'
            exact (Set.disjoint_left.mp hUV h₁.2) h₂.2
      · obtain ⟨A, B, hA, hB, htA, hsB, hAB⟩ := t2_separation hts
        refine ⟨height ⁻¹' A, height ⁻¹' B, hA.preimage height.continuous,
          hB.preimage height.continuous, htA, hsB, ?_⟩
        exact hAB.preimage _

/-- The suspension of a continuous map. -/
def map (f : C(X, Y)) : C(Susp X, Susp Y) :=
  lift ⟨fun p => mk (p.1, f p.2), mk.continuous.comp (by fun_prop)⟩
    (fun x y => mk_zero_eq_mk_zero (f x) (f y)) (fun x y => mk_one_eq_mk_one (f x) (f y))

@[simp]
theorem map_mk (f : C(X, Y)) (p : I × X) : map f (mk p) = mk (p.1, f p.2) := rfl

@[simp]
theorem map_south [Nonempty X] [Nonempty Y] (f : C(X, Y)) :
    map f (south X) = south Y := by
  rw [south, map_mk, mk_zero]

@[simp]
theorem map_north [Nonempty X] [Nonempty Y] (f : C(X, Y)) :
    map f (north X) = north Y := by
  rw [north, map_mk, mk_one]

@[simp]
theorem map_id : map (ContinuousMap.id X) = ContinuousMap.id (Susp X) := by
  ext q
  induction q using Susp.ind with
  | h p => rfl

@[simp]
theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) : map (g.comp f) = (map g).comp (map f) := by
  ext q
  induction q using Susp.ind with
  | h p => rfl

/-- A homeomorphism induces a homeomorphism of unreduced suspensions. -/
noncomputable def mapHomeomorph (e : X ≃ₜ Y) : Susp X ≃ₜ Susp Y where
  toFun := map (e : C(X, Y))
  invFun := map (e.symm : C(Y, X))
  left_inv q := by
    induction q using Susp.ind with
    | h p =>
        rcases p with ⟨t, x⟩
        simp only [map_mk]
        exact congrArg (fun z ↦ (mk (t, z) : Susp X)) (e.symm_apply_apply x)
  right_inv q := by
    induction q using Susp.ind with
    | h p =>
        rcases p with ⟨t, y⟩
        simp only [map_mk]
        exact congrArg (fun z ↦ (mk (t, z) : Susp Y)) (e.apply_symm_apply y)
  continuous_toFun := (map (e : C(X, Y))).continuous
  continuous_invFun := (map (e.symm : C(Y, X))).continuous

end Susp

end NRR.SuspensionGeometry

namespace NRR.SuspensionGeometry
open Set Topology unitInterval
open scoped ContinuousMap
set_option maxHeartbeats 1000000

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Descent through a quotient, with a computation rule independent of the chosen section. -/
def quotientLift (q : C(X,Y)) (hq : IsQuotientMap q) (f : C(X,Z))
    (hf : ∀ x y, q x = q y → f x = f y) : C(Y,Z) := by
  let s := Function.surjInv hq.surjective
  have hs : ∀ y, q (s y) = y := Function.surjInv_eq hq.surjective
  refine ⟨fun y => f (s y), hq.continuous_iff.mpr ?_⟩
  have he : (fun x => f (s (q x))) = f := funext fun x => hf _ _ (hs (q x))
  change Continuous (fun x => f (s (q x)))
  rw [he]
  exact f.continuous

@[simp] theorem quotientLift_apply (q : C(X,Y)) (hq : IsQuotientMap q) (f : C(X,Z))
    (hf : ∀ x y, q x = q y → f x = f y) (x : X) :
    quotientLift q hq f hf (q x) = f x :=
  hf _ _ (Function.surjInv_eq hq.surjective (q x))

/-- Parametrized descent; compactness of the interval supplies the product quotient theorem. -/
def quotientLiftParam (q : C(X,Y)) (hq : IsQuotientMap q) (f : C(I × X,Z))
    (hf : ∀ t x y, q x = q y → f (t,x) = f (t,y)) : C(I × Y,Z) := by
  let s := Function.surjInv hq.surjective
  have hs : ∀ y, q (s y) = y := Function.surjInv_eq hq.surjective
  refine ⟨fun p => f (p.1,s p.2), hq.continuous_lift_prod_right ?_⟩
  have he : (fun p : I × X => f (p.1,s (q p.2))) = f :=
    funext fun p => hf _ _ _ (hs (q p.2))
  change Continuous (fun p : I × X => f (p.1,s (q p.2)))
  rw [he]
  exact f.continuous

@[simp] theorem quotientLiftParam_apply (q : C(X,Y)) (hq : IsQuotientMap q)
    (f : C(I × X,Z)) (hf : ∀ t x y, q x = q y → f (t,x) = f (t,y)) (t : I) (x : X) :
    quotientLiftParam q hq f hf (t,q x) = f (t,x) :=
  hf _ _ _ (Function.surjInv_eq hq.surjective (q x))

def homeomorphOfBijectiveQuotient (q : C(X,Y)) (hq : IsQuotientMap q)
    (hb : Function.Bijective q) : X ≃ₜ Y where
  toEquiv := Equiv.ofBijective q hb
  continuous_toFun := q.continuous
  continuous_invFun := hq.continuous_iff.mpr (by
    change Continuous (fun x => (Equiv.ofBijective q hb).symm ((Equiv.ofBijective q hb) x))
    simpa using (continuous_id : Continuous (id : X → X)))

namespace Susp

/-- Reflection exchanges the two poles. -/
def reflect : C(Susp X,Susp X) :=
  lift ⟨fun p => mk (σ p.1,p.2), mk.continuous.comp (by fun_prop)⟩
    (by intro x y; simpa using mk_one_eq_mk_one x y)
    (by intro x y; simpa using mk_zero_eq_mk_zero x y)

@[simp] theorem reflect_mk (t : I) (x : X) : reflect (mk (t,x)) = mk (σ t,x) := rfl

@[simp] theorem reflect_reflect (z : Susp X) : reflect (reflect z) = z := by
  induction z using ind with | h p => exact congrArg (fun t => mk (t,p.2)) (symm_symm p.1)

@[simp] theorem height_reflect (z : Susp X) : height (reflect z) = σ (height z) := by
  induction z using ind with | h p => rfl

@[simp] theorem height_map (f : C(X,Y)) (z : Susp X) : height (map f z) = height z := by
  induction z using ind with | h p => rfl

/-- The quotient restricted to a saturated open subspace. -/
def restrictMk (N : Set (Susp X)) : C(mk ⁻¹' N,N) :=
  ⟨fun p => ⟨mk p.val,p.property⟩,
    (mk.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem quotient_restrictMk (N : Set (Susp X)) (hN : IsOpen N) :
    IsQuotientMap (restrictMk N) := isQuotientMap_mk.restrictPreimage_isOpen hN

/-- Away from the two poles the suspension has its usual product coordinates. -/
def band (T : Set I) : Set (Susp X) := height ⁻¹' T

theorem injective_restrictMk_band (T : Set I) (h0 : (0 : I) ∉ T)
    (h1 : (1 : I) ∉ T) : Function.Injective (restrictMk (band (X := X) T)) := by
  intro a b hab
  apply Subtype.ext
  rcases mk_eq_mk.mp (congrArg Subtype.val hab) with he | ⟨ha,_⟩ | ⟨ha,_⟩
  · exact he
  · exact (h0 (ha ▸ a.property)).elim
  · exact (h1 (ha ▸ a.property)).elim

def bandCoordinates (T : Set I) (hT : IsOpen T) (h0 : (0 : I) ∉ T)
    (h1 : (1 : I) ∉ T) : band (X := X) T ≃ₜ T × X := by
  let e : mk ⁻¹' band (X := X) T ≃ₜ T × X := {
    toFun := fun p => (⟨p.val.1,p.property⟩,p.val.2)
    invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hinj : Function.Injective (restrictMk (band (X := X) T)) := by
    intro a b hab
    apply Subtype.ext
    rcases mk_eq_mk.mp (congrArg Subtype.val hab) with he | ⟨ha,_⟩ | ⟨ha,_⟩
    · exact he
    · exact (h0 (ha ▸ a.property)).elim
    · exact (h1 (ha ▸ a.property)).elim
  exact (homeomorphOfBijectiveQuotient _
    (quotient_restrictMk _ (hT.preimage height.continuous))
    ⟨hinj,(quotient_restrictMk _ (hT.preimage height.continuous)).surjective⟩).symm.trans e

@[simp] theorem bandCoordinates_mk (T : Set I) (hT : IsOpen T) (h0 : (0 : I) ∉ T)
    (h1 : (1 : I) ∉ T) (t : I) (x : X) (ht : t ∈ T) :
    bandCoordinates (X := X) T hT h0 h1 ⟨mk (t,x),ht⟩ = (⟨t,ht⟩,x) := by
  apply (bandCoordinates (X := X) T hT h0 h1).symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The closed arc lying above a marked point. -/
def arc (p : X) : Set (Susp X) := range (fun t : I => mk (t,p))

def arcHomeomorph (p : X) : I ≃ₜ arc p := by
  let f : C(I,arc p) := ⟨fun t => ⟨mk (t,p),⟨t,rfl⟩⟩,by fun_prop⟩
  refine {
    toFun := f
    invFun := fun z => height z.val
    left_inv := fun t => rfl
    right_inv := ?_
    continuous_toFun := f.continuous
    continuous_invFun := height.continuous.comp continuous_subtype_val }
  rintro ⟨z,t,rfl⟩
  rfl

theorem arc_contractible (p : X) : ContractibleSpace (arc p) := by
  letI : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  exact (arcHomeomorph p).symm.contractibleSpace

theorem mem_arc_mk (p x : X) (t : I) :
    mk (t,x) ∈ arc p ↔ t = 0 ∨ t = 1 ∨ x = p := by
  constructor
  · rintro ⟨s,hs⟩
    rcases mk_eq_mk.mp hs with he | ⟨_,ht⟩ | ⟨_,ht⟩
    · exact Or.inr (Or.inr (congrArg Prod.snd he).symm)
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,mk_zero_eq_mk_zero _ _⟩
    · exact ⟨1,mk_one_eq_mk_one _ _⟩
    · exact ⟨t,rfl⟩

end Susp
end NRR.SuspensionGeometry
