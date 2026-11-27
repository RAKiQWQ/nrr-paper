import NRR.PrimePowerTopologyConvexHomology

/-! The actual degree-zero singular homology of totally disconnected
spaces, with its functorial basis. This supplies the two-point sphere
calculation without invoking any unproved excision theorem. -/

noncomputable section
open Set Topology CategoryTheory Limits AlgebraicTopology Opposite Simplicial
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (R : Type) [Ring R]

theorem Csing_d_one_zero_of_totallyDisconnected (X : TopCat.{0})
    [TotallyDisconnectedSpace X] : (Csing R X).d 1 0 = 0 := by
  let e := singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    (ModuleCat R) (ModuleCat.of R R) X
  apply (cancel_mono (e.hom.f 0)).mp
  rw [zero_comp,← e.hom.comm]
  simp [e,ChainComplex.alternatingConst,HomologicalComplex.alternatingConst]

theorem Csing_sc_zero_f (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    ((Csing R X).sc 0).f = 0 := by
  change (Csing R X).d ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
  exact Csing_d_one_zero_of_totallyDisconnected R X

def HabsZeroChainsIso (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    Habs R 0 X ≅ (Csing R X).X 0 :=
  (ShortComplex.HomologyData.ofZeros ((Csing R X).sc 0)
    (Csing_sc_zero_f R X) (by simp)).left.homologyIso

theorem HabsZeroChainsIso_naturality {X Y : TopCat.{0}}
    [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y] (f : X ⟶ Y) :
    HabsMap R 0 f ≫ (HabsZeroChainsIso R Y).hom =
      (HabsZeroChainsIso R X).hom ≫ (CsingMap R f).f 0 := by
  exact (ShortComplex.HomologyMapData.ofZeros
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
      (CsingMap R f))
    (Csing_sc_zero_f R X) (by simp)
    (Csing_sc_zero_f R Y) (by simp)).left.homologyMap_comm

def zeroSimplexEquiv (X : TopCat.{0}) :
    (TopCat.toSSet.obj X).obj (op ⦋0⦌) ≃ X :=
  (X.toSSetObjEquiv (op ⦋0⦌)).trans
    { toFun := fun f => f default
      invFun := fun x => ContinuousMap.const _ x
      left_inv := fun f => by
        apply ContinuousMap.ext
        intro p
        exact congrArg f (Subsingleton.elim default p)
      right_inv := fun _ => rfl }

def HabsZeroDiscreteIso (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    Habs R 0 X ≅ ∐ (fun _ : X => ModuleCat.of R R) :=
  HabsZeroChainsIso R X ≪≫ Sigma.reindex (zeroSimplexEquiv X) (fun _ : X => ModuleCat.of R R)

theorem zeroSimplexEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (s : (TopCat.toSSet.obj X).obj (op ⦋0⦌)) :
    zeroSimplexEquiv Y ((TopCat.toSSet.map f).app _ s) = f (zeroSimplexEquiv X s) := rfl

@[reassoc (attr := simp)]
theorem constant_ι_reindex {α β : Type} (e : α ≃ β) (a : α) :
    Sigma.ι (fun _ : α => ModuleCat.of R R) a ≫
        (Sigma.reindex e (fun _ : β => ModuleCat.of R R)).hom =
      Sigma.ι (fun _ : β => ModuleCat.of R R) (e a) :=
  Sigma.ι_reindex_hom e (fun _ : β => ModuleCat.of R R) a

theorem zeroChains_reindex_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (CsingMap R f).f 0 ≫
        (Sigma.reindex (zeroSimplexEquiv Y) (fun _ : Y => ModuleCat.of R R)).hom =
      (Sigma.reindex (zeroSimplexEquiv X) (fun _ : X => ModuleCat.of R R)).hom ≫
        (sigmaConst.obj (ModuleCat.of R R)).map (show X → Y from f) := by
  apply Sigma.hom_ext
  intro s
  simp only [← Category.assoc]
  change Sigma.ι _ s ≫
      (sigmaConst.obj (ModuleCat.of R R)).map ((TopCat.toSSet.map f).app (op ⦋0⦌)) ≫ _ = _
  simp only [sigmaConst]
  simp [zeroSimplexEquiv_naturality]

theorem HabsZeroDiscreteIso_naturality {X Y : TopCat.{0}}
    [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y] (f : X ⟶ Y) :
    HabsMap R 0 f ≫ (HabsZeroDiscreteIso R Y).hom =
      (HabsZeroDiscreteIso R X).hom ≫
        (sigmaConst.obj (ModuleCat.of R R)).map (show X → Y from f) := by
  unfold HabsZeroDiscreteIso
  simp only [Iso.trans_hom,← Category.assoc]
  rw [HabsZeroChainsIso_naturality]
  rw [Category.assoc,zeroChains_reindex_naturality,← Category.assoc]

def discretePointClass (X : TopCat.{0}) [TotallyDisconnectedSpace X] (x : X) :
    ModuleCat.of R R ⟶ Habs R 0 X :=
  Sigma.ι (fun _ : X => ModuleCat.of R R) x ≫ (HabsZeroDiscreteIso R X).inv

theorem discretePointClass_naturality {X Y : TopCat.{0}}
    [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y] (f : X ⟶ Y) (x : X) :
    discretePointClass R X x ≫ HabsMap R 0 f = discretePointClass R Y (f x) := by
  apply (cancel_mono (HabsZeroDiscreteIso R Y).hom).mp
  unfold discretePointClass
  rw [Category.assoc,Category.assoc,HabsZeroDiscreteIso_naturality]
  simp [sigmaConst]

/-- The actual point class in an arbitrary topological space, induced by
the inclusion of a point. Its normalization uses the canonical basis of
the degree-zero homology of the one-point space. -/
def homologyPointClass (X : TopCat.{0}) (x : X) : ModuleCat.of R R ⟶ Habs R 0 X :=
  discretePointClass R (TopCat.of Unit) () ≫ HabsMap R 0 (homologyPointIncl x)

theorem homologyPointClass_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    homologyPointClass R X x ≫ HabsMap R 0 f = homologyPointClass R Y (f x) := by
  unfold homologyPointClass
  rw [Category.assoc,← HabsMap_comp]
  rfl

theorem homologyPointClass_eq_discrete (X : TopCat.{0}) [TotallyDisconnectedSpace X] (x : X) :
    homologyPointClass R X x = discretePointClass R X x :=
  discretePointClass_naturality R (homologyPointIncl x) ()

def freePointEvaluation (X : Type) (x : X) :
    (∐ (fun _ : X => ModuleCat.of R R)) ⟶ ModuleCat.of R R := by
  classical
  exact Sigma.desc (fun y => if y = x then 𝟙 _ else 0)

@[reassoc (attr := simp)]
theorem pointClass_evaluation (X : TopCat.{0}) [TotallyDisconnectedSpace X] (x y : X) :
    homologyPointClass R X y ≫ (HabsZeroDiscreteIso R X).hom ≫ freePointEvaluation R X x =
      if y = x then 𝟙 (ModuleCat.of R R) else 0 := by
  classical
  rw [homologyPointClass_eq_discrete]
  dsimp [discretePointClass]
  simp [Category.assoc, freePointEvaluation]

theorem pointClass_sub_ne_zero [Nontrivial R] (X : TopCat.{0})
    [TotallyDisconnectedSpace X] (x y : X) (hne : x ≠ y) :
    homologyPointClass R X x-homologyPointClass R X y ≠ 0 := by
  classical
  intro he
  have hz := congrArg (fun f : ModuleCat.of R R ⟶ Habs R 0 X =>
    f ≫ (HabsZeroDiscreteIso R X).hom ≫ freePointEvaluation R X x) he
  dsimp at hz
  have hzx := pointClass_evaluation R X x x
  have hzy := pointClass_evaluation R X x y
  have hleft : (homologyPointClass R X x-homologyPointClass R X y) ≫
      (HabsZeroDiscreteIso R X).hom ≫ freePointEvaluation R X x = 𝟙 _ := by
    rw [Preadditive.sub_comp,hzx,hzy]
    simp [Ne.symm hne]
  rw [hleft,zero_comp] at hz
  have hv := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1) hz
  change (1 : R) = 0 at hv
  exact one_ne_zero hv

end NRR.PrimePowerTopology
