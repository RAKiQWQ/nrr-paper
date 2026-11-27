import NRR.PrimePowerTopologyLocalDegree
import NRR.TopologyPort.SingularPrism
import Mathlib.Analysis.Convex.Contractible

/-! Positive-degree singular homology of contractible local models.

All homology groups here are the actual singular homology objects with
arbitrary ring coefficients from `SingularHomologyPair`.
-/

noncomputable section
open Set Topology Metric CategoryTheory Limits AlgebraicTopology
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [Ring R]

theorem isZero_Habs_of_totallyDisconnected (k : ℕ) (hk : k ≠ 0)
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] : IsZero (Habs R k X) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat R) k (ModuleCat.of R R) X hk

def homologyPointCollapse (X : TopCat.{0}) : X ⟶ TopCat.of Unit :=
  TopCat.ofHom (ContinuousMap.const X ())

def homologyPointIncl {X : TopCat.{0}} (x : X) : TopCat.of Unit ⟶ X :=
  TopCat.ofHom (ContinuousMap.const Unit x)

theorem HabsMap_const_eq_zero (k : ℕ) (hk : k ≠ 0)
    {X Y : TopCat.{0}} (y : Y) :
    HabsMap R k (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
  change HabsMap R k (homologyPointCollapse X ≫ homologyPointIncl y) = 0
  rw [HabsMap_comp]
  have hz : HabsMap R k (homologyPointIncl y) = 0 :=
    (isZero_Habs_of_totallyDisconnected R k hk (TopCat.of Unit)).eq_zero_of_src _
  rw [hz,comp_zero]

theorem HabsMap_eq_of_homotopy (k : ℕ) {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : f.hom.Homotopy g.hom) : HabsMap R k f = HabsMap R k g :=
  NRR.TopologyPort.singularHomologyMap_eq_of_homotopy (ModuleCat.of R R) H k

def HabsIsoOfHomotopyEquiv (k : ℕ) {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    Habs R k (TopCat.of X) ≅ Habs R k (TopCat.of Y) where
  hom := HabsMap R k (TopCat.ofHom e.toFun)
  inv := HabsMap R k (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← HabsMap_comp]
    exact (HabsMap_eq_of_homotopy R k e.left_inv.some).trans (HabsMap_id R k _)
  inv_hom_id := by
    rw [← HabsMap_comp]
    exact (HabsMap_eq_of_homotopy R k e.right_inv.some).trans (HabsMap_id R k _)

def HabsZeroPointIso : Habs R 0 (TopCat.of Unit) ≅ ModuleCat.of R R :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat R) (ModuleCat.of R R) (TopCat.of Unit) ≪≫
      coproductUniqueIso (fun _ : Unit => ModuleCat.of R R)

/-- The zeroth homology of a contractible space is the coefficient module;
the isomorphism is induced by a genuine contraction to a point. -/
def HabsZeroContractibleIso (X : TopCat.{0}) [ContractibleSpace X] :
    Habs R 0 X ≅ ModuleCat.of R R :=
  HabsIsoOfHomotopyEquiv R 0 (ContractibleSpace.hequiv_unit X).some ≪≫ HabsZeroPointIso R

/-- Every positive-dimensional actual singular homology group of a
contractible space is zero, with arbitrary ring coefficients. -/
theorem isZero_Habs_of_contractible (k : ℕ) (hk : k ≠ 0)
    (X : TopCat.{0}) [ContractibleSpace X] : IsZero (Habs R k X) := by
  obtain ⟨x,⟨H⟩⟩ := id_nullhomotopic X
  apply (IsZero.iff_id_eq_zero _).mpr
  have he : HabsMap R k (𝟙 X) =
      HabsMap R k (TopCat.ofHom (ContinuousMap.const X x)) :=
    HabsMap_eq_of_homotopy R k H
  rw [HabsMap_id,HabsMap_const_eq_zero R k hk] at he
  exact he

theorem isZero_Habs_of_convex {E : Type} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (k : ℕ) (hk : k ≠ 0) {S : Set E} (convex : Convex ℝ S) (nonempty : S.Nonempty) :
    IsZero (Habs R k (TopCat.of S)) := by
  letI : ContractibleSpace S := convex.contractibleSpace nonempty
  exact isZero_Habs_of_contractible R k hk (TopCat.of S)

theorem isZero_Habs_closedBall {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (hk : k ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    IsZero (Habs R k (TopCat.of (closedBall (0 : E) r))) :=
  isZero_Habs_of_convex R k hk (convex_closedBall (0 : E) r)
    ⟨0,mem_closedBall_self hr⟩

theorem isZero_Habs_ball {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) :
    IsZero (Habs R k (TopCat.of (ball (0 : E) r))) :=
  isZero_Habs_of_convex R k hk (convex_ball (0 : E) r) ⟨0,mem_ball_self hr⟩

/-- The relative connecting map is an isomorphism whenever the two
adjacent absolute groups of the ambient space vanish. -/
theorem isIso_relδ_of_ambient_zero (k : ℕ) {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i]
    (zeroNext : IsZero (Habs R (k+1) X)) (zeroCurrent : IsZero (Habs R k X)) :
    IsIso (relδ R k i) := by
  have hj : relJ R (k+1) i = 0 := zeroNext.eq_zero_of_src _
  have hi : relIota R k i = 0 := zeroCurrent.eq_zero_of_tgt _
  letI : Mono (relδ R k i) := (pair_exact_j_δ R k i).mono_g hj
  letI : Epi (relδ R k i) := (pair_exact_δ_iota R k i).epi_f hi
  exact isIso_of_mono_of_epi _

def relδIso_of_ambient_zero (k : ℕ) {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i]
    (zeroNext : IsZero (Habs R (k+1) X)) (zeroCurrent : IsZero (Habs R k X)) :
    Hrel R (k+1) i ≅ Habs R k A := by
  letI := isIso_relδ_of_ambient_zero R k i zeroNext zeroCurrent
  exact asIso (relδ R k i)

theorem isIso_relδ_of_contractible (k : ℕ) (hk : k ≠ 0) {A X : TopCat.{0}}
    [ContractibleSpace X] (i : A ⟶ X) [Mono i] : IsIso (relδ R k i) :=
  isIso_relδ_of_ambient_zero R k i
    (isZero_Habs_of_contractible R (k+1) (by omega) X)
    (isZero_Habs_of_contractible R k hk X)

/-- In positive degrees the connecting morphism for the actual normal
disk and its boundary sphere is an isomorphism. The radius is any
nonnegative real number; a zero-radius sphere may of course be degenerate. -/
theorem isIso_normalDisk_relδ (d n k : ℕ) [NeZero n] (r : ℝ) (hr : 0 ≤ r) :
    IsIso (relδ R (k+1) (normalBoundaryIncl d n r)) :=
  isIso_relδ_of_ambient_zero R (k+1) (normalBoundaryIncl d n r)
    (isZero_Habs_closedBall R (k+1+1) (by omega) r hr)
    (isZero_Habs_closedBall R (k+1) (by omega) r hr)

def normalDiskBoundaryIso (d n k : ℕ) [NeZero n] (r : ℝ) (hr : 0 ≤ r) :
    Hrel R (k+2) (normalBoundaryIncl d n r) ≅
      Habs R (k+1) (TopCat.of (sphere (0 : ReducedValues (d+1) n) r)) := by
  letI := isIso_normalDisk_relδ R d n k r hr
  exact asIso (relδ R (k+1) (normalBoundaryIncl d n r))

end NRR.PrimePowerTopology
