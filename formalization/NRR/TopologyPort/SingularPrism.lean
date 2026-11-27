import NRR.TopologyPort.SimplexCut
import NRR.TopologyPort.SimplicialChainHomotopy
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Homotopy.Basic

/-! Direct prism coordinates for the singular simplicial set in mathlib 4.24.
This avoids importing the newer simplicial geometric-realization API. -/

noncomputable section
open CategoryTheory Opposite SimplexCategory Simplicial
open scoped unitInterval

namespace NRR.TopologyPort

universe u

@[simp] theorem singularEquiv_precomp (X : TopCat.{u}) {a b : SimplexCategory} (f : a ⟶ b)
    (s : (TopCat.toSSet.obj X).obj (op b)) :
    X.toSSetObjEquiv (op a) ((TopCat.toSSet.obj X).map f.op s) =
      (X.toSSetObjEquiv (op b) s).comp ⟨toTopMap f,continuous_toTopMap f⟩ := rfl

@[simp] theorem singularEquiv_postcomp {X Y : TopCat.{u}} (f : X ⟶ Y) (a : SimplexCategory)
    (s : (TopCat.toSSet.obj X).obj (op a)) :
    Y.toSSetObjEquiv (op a) ((TopCat.toSSet.map f).app (op a) s) =
      f.hom.comp (X.toSSetObjEquiv (op a) s) := rfl

theorem toTopMap_comp_apply {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (s : a.toTopObj) : toTopMap g (toTopMap f s) = toTopMap (f ≫ g) s :=
  congrArg (fun m => m.hom s) (toTop₀.map_comp f g).symm

theorem toTopMap_id_apply (a : SimplexCategory) (p : a.toTopObj) :
    toTopMap (𝟙 a) p = p :=
  congrArg (fun m => m.hom p) (toTop₀.map_id a)

def intervalReadout : C(⦋1⦌.toTopObj,unitInterval) :=
  (⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩ : C(unitInterval,unitInterval)).comp
    ⟨toTopObjOneHomeo,toTopObjOneHomeo.continuous⟩

def prismTime {n : ℕ} (i : Fin (n+1)) : C(⦋n+1⦌.toTopObj,unitInterval) :=
  intervalReadout.comp ⟨toTopMap (toMk₁ i.castSucc.succ),continuous_toTopMap _⟩

def prismSimplex {X Y : TopCat.{u}} {f g : C(X,Y)} (H : f.Homotopy g)
    {n : ℕ} (i : Fin (n+1)) (s : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj Y).obj (op ⦋n+1⦌) :=
  (Y.toSSetObjEquiv _).symm
    (H.toContinuousMap.comp ((prismTime i).prodMk
      ((X.toSSetObjEquiv _ s).comp ⟨toTopMap (SimplexCategory.σ i),continuous_toTopMap _⟩)))

@[simp] theorem singularEquiv_prismSimplex {X Y : TopCat.{u}} {f g : C(X,Y)}
    (H : f.Homotopy g) {n : ℕ} (i : Fin (n+1))
    (s : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (p : ⦋n+1⦌.toTopObj) :
    Y.toSSetObjEquiv _ (prismSimplex H i s) p =
      H (prismTime i p,(X.toSSetObjEquiv _ s) (toTopMap (SimplexCategory.σ i) p)) := by
  simp only [prismSimplex,Equiv.apply_symm_apply]
  rfl

/-- A prism identity follows from its two actual affine coordinate maps:
the time cut and the projection to the original simplex. -/
theorem prismSimplex_naturality {X Y : TopCat.{u}} {f g : C(X,Y)}
    (H : f.Homotopy g) {m n : ℕ} (i : Fin (n+1)) (j : Fin (m+1))
    (a : ⦋m+1⦌ ⟶ ⦋n+1⦌) (b : ⦋m⦌ ⟶ ⦋n⦌)
    (time : a ≫ toMk₁ i.castSucc.succ = toMk₁ j.castSucc.succ)
    (base : a ≫ SimplexCategory.σ i = SimplexCategory.σ j ≫ b)
    (s : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj Y).map a.op (prismSimplex H i s) =
      prismSimplex H j ((TopCat.toSSet.obj X).map b.op s) := by
  apply (Y.toSSetObjEquiv _).injective
  ext p
  apply congrArg (fun z : unitInterval × X => H z)
  apply Prod.ext
  · change intervalReadout (toTopMap (toMk₁ i.castSucc.succ) (toTopMap a p)) =
      intervalReadout (toTopMap (toMk₁ j.castSucc.succ) p)
    rw [toTopMap_comp_apply,time]
  · change (X.toSSetObjEquiv _ s) (toTopMap (SimplexCategory.σ i) (toTopMap a p)) =
      (X.toSSetObjEquiv _ s) (toTopMap b (toTopMap (SimplexCategory.σ j) p))
    rw [toTopMap_comp_apply,base,← toTopMap_comp_apply]

theorem prismSimplex_compare {X Y : TopCat.{u}} {f g : C(X,Y)}
    (H : f.Homotopy g) {m n : ℕ} (i j : Fin (n+1))
    (a b : ⦋m⦌ ⟶ ⦋n+1⦌)
    (time : a ≫ toMk₁ i.castSucc.succ = b ≫ toMk₁ j.castSucc.succ)
    (base : a ≫ SimplexCategory.σ i = b ≫ SimplexCategory.σ j)
    (s : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj Y).map a.op (prismSimplex H i s) =
      (TopCat.toSSet.obj Y).map b.op (prismSimplex H j s) := by
  apply (Y.toSSetObjEquiv _).injective
  ext p
  apply congrArg (fun z : unitInterval × X => H z)
  apply Prod.ext
  · change intervalReadout (toTopMap (toMk₁ i.castSucc.succ) (toTopMap a p)) =
      intervalReadout (toTopMap (toMk₁ j.castSucc.succ) (toTopMap b p))
    rw [toTopMap_comp_apply,toTopMap_comp_apply,time]
  · change (X.toSSetObjEquiv _ s) (toTopMap (SimplexCategory.σ i) (toTopMap a p)) =
      (X.toSSetObjEquiv _ s) (toTopMap (SimplexCategory.σ j) (toTopMap b p))
    rw [toTopMap_comp_apply,toTopMap_comp_apply,base]

theorem intervalReadout_toTopMap_const_one {a : SimplexCategory}
    (c : a ⟶ ⦋1⦌) (hc : ∀ i,c i = 1) (p : a.toTopObj) :
    intervalReadout (toTopMap c p) = 1 := by
  apply Subtype.ext
  change 1-((toTopMap c p) 0 : ℝ) = 1
  have zero : (toTopMap c p) 0 = 0 := by
    rw [coe_toTopMap]
    apply Finset.sum_eq_zero
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    have bad : (1 : Fin 2) = 0 := (hc i).symm.trans he
    norm_num at bad
  rw [zero]
  norm_num

theorem intervalReadout_toTopMap_const_zero {a : SimplexCategory}
    (c : a ⟶ ⦋1⦌) (hc : ∀ i,c i = 0) (p : a.toTopObj) :
    intervalReadout (toTopMap c p) = 0 := by
  apply Subtype.ext
  change 1-((toTopMap c p) 0 : ℝ) = 0
  have one : (toTopMap c p) 0 = 1 := by
    simpa only [coe_toTopMap,hc,Finset.filter_True] using p.property
  rw [one]
  norm_num

theorem prismTime_face_zero (n : ℕ) (p : ⦋n⦌.toTopObj) :
    prismTime (0 : Fin (n+1)) (toTopMap (δ 0) p) = 1 := by
  change intervalReadout (toTopMap (toMk₁ (0 : Fin (n+1)).castSucc.succ)
    (toTopMap (δ 0) p)) = 1
  rw [toTopMap_comp_apply]
  apply intervalReadout_toTopMap_const_one
  intro k
  change toMk₁ (0 : Fin (n+1)).castSucc.succ ((δ 0) k) = 1
  apply (toMk₁_apply_eq_one_iff _ _).mpr
  change (1 : ℕ) ≤ ((0 : Fin (n+2)).succAbove k).val
  simp

theorem prismTime_face_last (n : ℕ) (p : ⦋n⦌.toTopObj) :
    prismTime (Fin.last n) (toTopMap (δ (Fin.last (n+1))) p) = 0 := by
  change intervalReadout (toTopMap (toMk₁ (Fin.last n).castSucc.succ)
    (toTopMap (δ (Fin.last (n+1))) p)) = 0
  rw [toTopMap_comp_apply]
  apply intervalReadout_toTopMap_const_zero
  intro k
  apply (toMk₁_apply_eq_zero_iff _ _).mpr
  change ((Fin.last (n+1)).succAbove k).val < n+1
  simpa using k.isLt

/-- A continuous homotopy supplies every simplex of an actual simplicial
homotopy of the singular simplicial sets. -/
def singularSSetHomotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : f.hom.Homotopy g.hom) :
    SimplicialObject.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h i := prismSimplex H i
  h_zero_comp_δ_zero n := by
    funext s
    apply (Y.toSSetObjEquiv _).injective
    ext p
    change H (prismTime 0 (toTopMap (δ 0) p),
      (X.toSSetObjEquiv _ s) (toTopMap (SimplexCategory.σ 0) (toTopMap (δ 0) p))) =
        g.hom ((X.toSSetObjEquiv _ s) p)
    rw [prismTime_face_zero,toTopMap_comp_apply,
      show δ (0 : Fin (n+2)) ≫ SimplexCategory.σ (0 : Fin (n+1)) = 𝟙 ⦋n⦌ from
        δ_comp_σ_self (i := 0),toTopMap_id_apply]
    exact H.apply_one _
  h_last_comp_δ_last n := by
    funext s
    apply (Y.toSSetObjEquiv _).injective
    ext p
    change H (prismTime (Fin.last n) (toTopMap (δ (Fin.last (n+1))) p),
      (X.toSSetObjEquiv _ s) (toTopMap (SimplexCategory.σ (Fin.last n))
        (toTopMap (δ (Fin.last (n+1))) p))) = f.hom ((X.toSSetObjEquiv _ s) p)
    rw [prismTime_face_last,toTopMap_comp_apply,show δ (Fin.last (n+1)) ≫
      SimplexCategory.σ (Fin.last n) = 𝟙 _ from δ_comp_σ_succ]
    rw [toTopMap_id_apply]
    exact H.apply_zero _
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    funext s
    apply prismSimplex_naturality H j.succ j (δ i.castSucc) (δ i) _
      (δ_comp_σ_of_le hij) s
    simpa using δ_comp_toMk₁_of_lt j.succ.castSucc.succ i.castSucc (by
      change i.val < j.val+2
      change i.val ≤ j.val at hij
      omega)
  h_succ_comp_δ_castSucc_succ j := by
    funext s
    apply prismSimplex_compare H j.succ j.castSucc
      (δ j.castSucc.succ) (δ j.castSucc.succ) _ _ s
    · rw [δ_comp_toMk₁_of_lt _ _ (by change j.val+1 < j.val+2; omega),
        δ_comp_toMk₁_of_le _ _ (by change j.val+1 ≤ j.val+1; omega)]
      rfl
    · rw [show δ j.castSucc.succ ≫ SimplexCategory.σ j.succ = 𝟙 _ from δ_comp_σ_self,
        show δ j.castSucc.succ ≫ SimplexCategory.σ j.castSucc = 𝟙 _ from δ_comp_σ_succ]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    funext s
    apply prismSimplex_naturality H j.castSucc j (δ i.succ) (δ i) _
      (δ_comp_σ_of_gt hji) s
    simpa using δ_comp_toMk₁_of_le j.castSucc.castSucc.succ i.succ (by
      change j.val+1 ≤ i.val+1
      change j.val < i.val at hji
      omega)
  h_comp_σ_castSucc_of_le i j hij := by
    funext s
    apply prismSimplex_naturality H j j.succ (SimplexCategory.σ i.castSucc)
      (SimplexCategory.σ i) _ (σ_comp_σ hij) s
    simpa using σ_comp_toMk₁_of_lt j.castSucc.succ i.castSucc (by
      change i.val < j.val+1
      exact Nat.lt_succ_of_le hij)
  h_comp_σ_succ_of_lt i j hji := by
    funext s
    apply prismSimplex_naturality H j j.castSucc (SimplexCategory.σ i.succ)
      (SimplexCategory.σ i) _ (σ_comp_σ hji).symm s
    simpa using σ_comp_toMk₁_of_le j.castSucc.succ i.succ (by
      change j.val+1 ≤ i.val+1
      exact Nat.succ_le_succ hji)

open AlgebraicTopology Limits in
/-- The actual singular chain maps of continuously homotopic maps are
chain homotopic, with any coefficient object in a preadditive category. -/
def singularChainHomotopy {C : Type*} [Category C] [Preadditive C]
    [HasCoproducts.{u} C] [CategoryWithHomology C] (R : C)
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : f.hom.Homotopy g.hom) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  ((singularSSetHomotopy H).whiskerRight (sigmaConst.obj R)).toChainHomotopy

open AlgebraicTopology Limits in
theorem singularHomologyMap_eq_of_homotopy {C : Type*} [Category C] [Preadditive C]
    [HasCoproducts.{u} C] [CategoryWithHomology C] (R : C)
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : f.hom.Homotopy g.hom) (k : ℕ) :
    HomologicalComplex.homologyMap (((singularChainComplexFunctor C).obj R).map f) k =
      HomologicalComplex.homologyMap (((singularChainComplexFunctor C).obj R).map g) k :=
  (singularChainHomotopy R H).homologyMap_eq k

theorem prismSimplex_pair_naturality {A X B Y : TopCat.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (HA : fA.hom.Homotopy gA.hom) (HX : f.hom.Homotopy g.hom)
    (compat : ∀ t a,HX (t,i.hom a) = j.hom (HA (t,a)))
    {n : ℕ} (k : Fin (n+1)) (s : (TopCat.toSSet.obj A).obj (op ⦋n⦌)) :
    prismSimplex HX k ((TopCat.toSSet.map i).app _ s) =
      (TopCat.toSSet.map j).app _ (prismSimplex HA k s) := by
  apply (Y.toSSetObjEquiv _).injective
  ext p
  change HX (prismTime k p,i.hom ((A.toSSetObjEquiv _ s)
    (toTopMap (SimplexCategory.σ k) p))) =
      j.hom (HA (prismTime k p,(A.toSSetObjEquiv _ s)
        (toTopMap (SimplexCategory.σ k) p)))
  exact compat _ _

open AlgebraicTopology Limits in
/-- The prism operators respect an actual homotopy of subspaces. This
degreewise equality is the compatibility needed to descend to relative chains. -/
theorem singularChainHomotopy_pair_naturality {C : Type*} [Category C] [Preadditive C]
    [HasCoproducts.{u} C] [CategoryWithHomology C] (R : C)
    {A X B Y : TopCat.{u}} (i : A ⟶ X) (j : B ⟶ Y)
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (HA : fA.hom.Homotopy gA.hom) (HX : f.hom.Homotopy g.hom)
    (compat : ∀ t a,HX (t,i.hom a) = j.hom (HA (t,a))) (p q : ℕ) :
    (((singularChainComplexFunctor C).obj R).map i).f p ≫
        (singularChainHomotopy R HX).hom p q =
      (singularChainHomotopy R HA).hom p q ≫
        (((singularChainComplexFunctor C).obj R).map j).f q := by
  by_cases hpq : p+1 = q
  · subst q
    have key (k : Fin (p+1)) :
        (sigmaConst.obj R).map ((TopCat.toSSet.map i).app (op ⦋p⦌)) ≫
            (sigmaConst.obj R).map ((singularSSetHomotopy HX).h k) =
          (sigmaConst.obj R).map ((singularSSetHomotopy HA).h k) ≫
            (sigmaConst.obj R).map ((TopCat.toSSet.map j).app (op ⦋p+1⦌)) := by
      rw [← Functor.map_comp,← Functor.map_comp]
      congr 1
      funext s
      exact prismSimplex_pair_naturality i j HA HX compat k s
    change (sigmaConst.obj R).map ((TopCat.toSSet.map i).app (op ⦋p⦌)) ≫
        SimplicialObject.Homotopy.ToChainHomotopy.hom
          ((singularSSetHomotopy HX).whiskerRight (sigmaConst.obj R)) p (p+1) =
      SimplicialObject.Homotopy.ToChainHomotopy.hom
          ((singularSSetHomotopy HA).whiskerRight (sigmaConst.obj R)) p (p+1) ≫
        (sigmaConst.obj R).map ((TopCat.toSSet.map j).app (op ⦋p+1⦌))
    simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      SimplicialObject.Homotopy.whiskerRight_h,Preadditive.comp_neg,Preadditive.neg_comp,
      Preadditive.comp_sum,Preadditive.sum_comp,Preadditive.comp_zsmul,
      Preadditive.zsmul_comp,key]
  · rw [(singularChainHomotopy R HX).zero p q (by simpa using hpq),
      (singularChainHomotopy R HA).zero p q (by simpa using hpq)]
    simp

end NRR.TopologyPort
