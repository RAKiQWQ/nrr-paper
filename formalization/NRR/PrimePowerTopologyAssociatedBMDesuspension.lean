import NRR.PrimePowerTopologyBMSuspensionGeometricIteration
import NRR.PrimePowerTopologyAssociatedBMFiberAction

/-! Geometric dimension descent for the actual associated total space.
Base relabelling is natural and the reduced fiber contributes its genuine
determinant character in the bottom degree. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ}

def associatedFiberEuclidean (d n : ℕ) :
    ReducedValues (d+1) n ≃L[ℝ] Space (d*(n-1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [fiberReducedValues_finrank,finrank_euclideanSpace_fin])

def associatedCoverEuclidean (d n : ℕ) :
    AssociatedCover (d+1) n ≃ₜ Configuration (d+1) n × Space (d*(n-1)) :=
  (Homeomorph.refl _).prodCongr (associatedFiberEuclidean d n).toHomeomorph

def associatedBMBaseHomeomorph (g : ConfigurationGroup n) :
    AssociatedCover (d+1) n ≃ₜ AssociatedCover (d+1) n :=
  (relabelConfiguration g).prodCongr (Homeomorph.refl _)

def associatedBMBaseMap (g : ConfigurationGroup n) :
    TopCat.of (OnePoint (AssociatedCover (d+1) n)) ⟶
      TopCat.of (OnePoint (AssociatedCover (d+1) n)) :=
  TopCat.ofHom ⟨(associatedBMBaseHomeomorph g).onePointCongr,
    (associatedBMBaseHomeomorph g).onePointCongr.continuous⟩

variable (R : Type) [CommRing R]

/-- Ordinary absolute dimension descent for the genuine associated total
space, in every positive target degree. -/
def associatedBMAbsoluteDesuspensionIso (d n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) :
    Habs R (q+d*(n-1)) (TopCat.of (OnePoint (AssociatedCover (d+1) n))) ≅
      Habs R q (TopCat.of (OnePoint (Configuration (d+1) n))) :=
  HabsIsoOfHomotopyEquiv R (q+d*(n-1))
      (associatedCoverEuclidean d n).onePointCongr.toHomotopyEquiv ≪≫
    geometricAbsoluteSpaceSuspensionIso R
      (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k
        (Nat.succ_pos d) hn) q hq (d*(n-1))

/-- The product-coordinate chart keeps the base action and all fiber
coordinates; the comparison is natural for the actual base permutation. -/
@[reassoc]
theorem associatedBMAbsoluteDesuspensionIso_base_naturality (hn : 2 ≤ n)
    (q : ℕ) (hq : 0 < q) (g : ConfigurationGroup n) :
    (associatedBMAbsoluteDesuspensionIso R d n hn q hq).hom ≫
        HabsMap R q (associatedBMSourceRelabelMap g) =
      HabsMap R (q+d*(n-1)) (associatedBMBaseMap g) ≫
        (associatedBMAbsoluteDesuspensionIso R d n hn q hq).hom := by
  let e := (associatedCoverEuclidean d n).onePointCongr
  let f := relabelConfiguration (d := d+1) g
  have h := geometricAbsoluteSpaceSuspensionIso_proper_naturality R
    (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k (Nat.succ_pos d) hn)
    (fun k => configurationSpaceProductInfinityGoodNeighborhood (d+1) n k (Nat.succ_pos d) hn)
    f f.isProperMap q hq (d*(n-1))
  have hf : properOnePointMap f f.isProperMap = associatedBMSourceRelabelMap g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    induction z using OnePoint.rec <;> rfl
  rw [hf] at h
  change (HabsMap R _ (TopCat.ofHom e.toHomotopyEquiv.toFun) ≫ _) ≫ _ = _ ≫
    (HabsMap R _ (TopCat.ofHom e.toHomotopyEquiv.toFun) ≫ _)
  simp only [Category.assoc]
  rw [h]
  simp only [← Category.assoc]
  rw [← HabsMap_comp,← HabsMap_comp]
  congr 2
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  induction z using OnePoint.rec <;> rfl

theorem associatedBMCoverRelabelMap_eq_base_fiber (g : ConfigurationGroup n) :
    associatedBMCoverRelabelMap (d := d+1) g = associatedBMBaseMap g ≫
      TopCat.ofHom ⟨(associatedBMFiberHomeomorph (d := d) g).onePointCongr,
        (associatedBMFiberHomeomorph (d := d) g).onePointCongr.continuous⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  induction z using OnePoint.rec <;> rfl

/-- The actual diagonal action differs from the base-only action by the
computed fiber determinant on bottom ordinary homology. -/
theorem associatedBMCoverRelabelMap_bottom [NeZero n] (hn : 2 ≤ n)
    (g : ConfigurationGroup n) :
    HabsMap R ((d+1)*n) (associatedBMCoverRelabelMap (d := d+1) g) =
      (Equiv.Perm.sign g : ℤ)^d •
        HabsMap R ((d+1)*n) (associatedBMBaseMap (d := d) g) := by
  rw [associatedBMCoverRelabelMap_eq_base_fiber,HabsMap_comp,
    associatedBMFiberMap_bottom R hn g]
  simp

theorem associatedBMBottom_degree (d n : ℕ) (hn : 0 < n) :
    d+n+d*(n-1) = (d+1)*n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
  ring

private theorem HabsMap_degree_naturality {X Y : TopCat.{0}}
    (a b : ℕ) (h : a = b) (f : X ⟶ Y) :
    eqToHom (congrArg (fun k => Habs R k X) h) ≫ HabsMap R b f =
      HabsMap R a f ≫ eqToHom (congrArg (fun k => Habs R k Y) h) := by
  subst b
  simp

/-- In the first possible degree, desuspension lands in the genuine
lowest configuration degree. -/
def associatedBMBottomAbsoluteIso (d n : ℕ) (hn : 2 ≤ n) :
    Habs R ((d+1)*n) (TopCat.of (OnePoint (AssociatedCover (d+1) n))) ≅
      Habs R (d+n) (TopCat.of (OnePoint (Configuration (d+1) n))) :=
  eqToIso (congrArg
      (fun k => Habs R k (TopCat.of (OnePoint (AssociatedCover (d+1) n))))
      (associatedBMBottom_degree d n (by omega)).symm) ≪≫
    associatedBMAbsoluteDesuspensionIso R d n hn (d+n) (by omega)

@[reassoc]
theorem associatedBMBottomAbsoluteIso_base_naturality (hn : 2 ≤ n)
    (g : ConfigurationGroup n) :
    (associatedBMBottomAbsoluteIso R d n hn).hom ≫
        HabsMap R (d+n) (associatedBMSourceRelabelMap g) =
      HabsMap R ((d+1)*n) (associatedBMBaseMap g) ≫
        (associatedBMBottomAbsoluteIso R d n hn).hom := by
  simp only [associatedBMBottomAbsoluteIso,Iso.trans_hom,eqToIso.hom,Category.assoc]
  rw [associatedBMAbsoluteDesuspensionIso_base_naturality,
    ← Category.assoc,HabsMap_degree_naturality]
  simp only [Category.assoc]
  exact (associatedBMBottom_degree d n (by omega)).symm

/-- Positive absolute/singleton-relative comparison for the actual
singleton inclusion, in the model used by the associated BM complexes. -/
def positiveSingletonRelativeIso (q : ℕ) (hq : 0 < q) {X : TopCat.{0}} (p : X) :
    Habs R q X ≅ Hrel R q (subIncl (Y := X) {p}) := by
  cases q with
  | zero => omega
  | succ q => exact relativeOfContractiblePositiveIso R q _

@[simp] theorem positiveSingletonRelativeIso_hom (q : ℕ) (hq : 0 < q)
    {X : TopCat.{0}} (p : X) :
    (positiveSingletonRelativeIso R q hq p).hom = relJ R q (subIncl (Y := X) {p}) := by
  cases q with
  | zero => omega
  | succ q => rfl

/-- Its naturality is the naturality of the actual relative quotient. -/
@[reassoc]
theorem positiveSingletonRelativeIso_naturality (q : ℕ) (hq : 0 < q)
    {X Y : TopCat.{0}} (p : X) (p' : Y) (f : X ⟶ Y)
    (fA : TopCat.of ({p} : Set X) ⟶ TopCat.of ({p'} : Set Y))
    (w : subIncl {p} ≫ f = fA ≫ subIncl {p'}) :
    (positiveSingletonRelativeIso R q hq p).hom ≫ HrelMap R q _ _ w =
      HabsMap R q f ≫ (positiveSingletonRelativeIso R q hq p').hom := by
  simp only [positiveSingletonRelativeIso_hom]
  exact relJ_naturality R q _ _ w

end NRR.PrimePowerTopology
