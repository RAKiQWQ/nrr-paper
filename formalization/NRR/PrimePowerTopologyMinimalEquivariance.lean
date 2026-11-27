import NRR.PrimePowerTopologyMinimalRelative
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! Coherently oriented actual minimal cells. A single identity-cell class
is transported by genuine label permutations; arbitrary sphere charts do
not enter the transformation law. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

theorem compactifiedConfigurationRelabel_mul_apply {d n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (x : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel (σ*τ) x =
      compactifiedConfigurationRelabel σ (compactifiedConfigurationRelabel τ x) := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rfl

@[simp] theorem compactifiedConfigurationRelabel_one_apply {d n : ℕ}
    (x : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel (1 : Equiv.Perm (Fin n)) x = x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rfl

/-- Restrict the actual compactified Fuks relabeling to its lowest level. -/
def minimalSkeletonRelabel {d n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    minimalSkeleton d n ≃ₜ minimalSkeleton d n :=
  (minimalLevelHomeomorph d n).trans
    ((compactifiedFuksRelabel (k := d) σ).trans (minimalLevelHomeomorph d n).symm)

@[simp] theorem minimalSkeletonRelabel_val {d n : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) (x : minimalSkeleton d n) :
    (minimalSkeletonRelabel σ x).val = compactifiedConfigurationRelabel σ x.val := rfl

def minimalSkeletonRelabelMap {d n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    TopCat.of (minimalSkeleton d n) ⟶ TopCat.of (minimalSkeleton d n) :=
  TopCat.ofHom ⟨minimalSkeletonRelabel σ,(minimalSkeletonRelabel σ).continuous⟩

@[simp] theorem minimalSkeletonRelabelMap_one (d n : ℕ) [NeZero n] :
    minimalSkeletonRelabelMap (d := d) (1 : Equiv.Perm (Fin n)) = 𝟙 _ := by
  ext x
  exact compactifiedConfigurationRelabel_one_apply x.val

theorem minimalSkeletonRelabelMap_mul {d n : ℕ} [NeZero n]
    (σ τ : Equiv.Perm (Fin n)) :
    minimalSkeletonRelabelMap (d := d) (σ*τ) =
      minimalSkeletonRelabelMap τ ≫ minimalSkeletonRelabelMap σ := by
  ext x
  exact compactifiedConfigurationRelabel_mul_apply σ τ x.val

/-- In a cell ordered by τ, actual relabeling by σ changes its chamber
index to σ*τ and leaves its common horizontal position fixed. -/
def heightChamberRelabel {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    heightChamber n τ ≃ₜ heightChamber n (σ*τ) where
  toFun t := ⟨fun i => t.val (σ.symm i),by
    intro i j hij
    simpa only [Equiv.Perm.mul_apply,Equiv.symm_apply_apply] using t.property hij⟩
  invFun t := ⟨fun i => t.val (σ i),by
    intro i j hij
    exact t.property hij⟩
  left_inv t := by apply Subtype.ext; funext i; simp
  right_inv t := by apply Subtype.ext; funext i; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply (σ.symm i)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply (σ i)).comp continuous_subtype_val

def compactifiedCellRelabel {d n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    OnePoint (Space d × heightChamber n τ) ≃ₜ
      OnePoint (Space d × heightChamber n (σ*τ)) :=
  ((Homeomorph.refl (Space d)).prodCongr (heightChamberRelabel σ τ)).onePointCongr

def compactifiedCellRelabelMap {d n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (Space d × heightChamber n τ)) ⟶
      TopCat.of (OnePoint (Space d × heightChamber n (σ*τ))) :=
  TopCat.ofHom ⟨compactifiedCellRelabel σ τ,(compactifiedCellRelabel σ τ).continuous⟩

theorem minimalCellInclusionMap_relabel {d n : ℕ} [NeZero n]
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    minimalCellInclusionMap (d := d) i₀ τ ≫ minimalSkeletonRelabelMap σ =
      compactifiedCellRelabelMap σ τ ≫ minimalCellInclusionMap i₀ (σ*τ) := by
  ext p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe p => rfl

/-- The identity cell is used as the sole orientation choice. -/
def identityCellRelabel {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OnePoint (Space d × heightChamber n 1) ≃ₜ
      OnePoint (Space d × heightChamber n σ) := by
  simpa only [mul_one] using (compactifiedCellRelabel (d := d) σ 1)

def identityCellRelabelMap {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TopCat.of (OnePoint (Space d × heightChamber n 1)) ⟶
      TopCat.of (OnePoint (Space d × heightChamber n σ)) :=
  TopCat.ofHom ⟨identityCellRelabel σ,(identityCellRelabel σ).continuous⟩

theorem minimalCellInclusionMap_identity_relabel {d n : ℕ} [NeZero n]
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    minimalCellInclusionMap (d := d) i₀ 1 ≫ minimalSkeletonRelabelMap σ =
      identityCellRelabelMap σ ≫ minimalCellInclusionMap i₀ σ := by
  simpa only [mul_one] using minimalCellInclusionMap_relabel (d := d) i₀ σ 1

section Homology

variable (R : Type) [CommRing R]

/-- The orientation of every cell is transported from the identity cell
by an actual homeomorphism. -/
def coherentCellTopHomologyIso {d n : ℕ} (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    Habs R (d+n) (TopCat.of (OnePoint (Space d × heightChamber n σ))) ≅
      ModuleCat.of R R :=
  (HabsIsoOfHomotopyEquiv R (d+n) (identityCellRelabel (d := d) σ).toHomotopyEquiv).symm ≪≫
    minimalCellTopHomologyIso R d n 1 hdim

/-- The coherent generator is defined by the true group action on the
identity-cell generator, not by independent orientation choices. -/
def coherentMinimalGenerator {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    ModuleCat.of R R ⟶ Habs R (d+n) (TopCat.of (minimalSkeleton d n)) :=
  minimalCellGenerator R i₀ 1 hdim ≫ HabsMap R (d+n) (minimalSkeletonRelabelMap σ)

theorem coherentMinimalGenerator_factor {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalGenerator R i₀ σ hdim =
      (coherentCellTopHomologyIso R σ hdim).inv ≫
        HabsMap R (d+n) (minimalCellInclusionMap i₀ σ) := by
  change ((minimalCellTopHomologyIso R d n 1 hdim).inv ≫
      HabsMap R (d+n) (minimalCellInclusionMap i₀ 1)) ≫
      HabsMap R (d+n) (minimalSkeletonRelabelMap σ) =
    ((minimalCellTopHomologyIso R d n 1 hdim).inv ≫
      HabsMap R (d+n) (identityCellRelabelMap σ)) ≫
      HabsMap R (d+n) (minimalCellInclusionMap i₀ σ)
  rw [Category.assoc,← HabsMap_comp,minimalCellInclusionMap_identity_relabel,
    HabsMap_comp,← Category.assoc]

theorem coherentMinimalGenerator_relabel {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ τ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalGenerator R i₀ τ hdim ≫ HabsMap R (d+n) (minimalSkeletonRelabelMap σ) =
      coherentMinimalGenerator R i₀ (σ*τ) hdim := by
  unfold coherentMinimalGenerator
  rw [Category.assoc,← HabsMap_comp,← minimalSkeletonRelabelMap_mul]

def coherentMinimalCoefficient {d n : ℕ} (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ⟶ ModuleCat.of R R :=
  HabsMap R (d+n) (minimalCellRetractionMap i₀ σ) ≫
    (coherentCellTopHomologyIso R σ hdim).hom

/-- The change from the old coefficient chart is an actual scalar-module
automorphism, so no normalization of an unproved sign is required. -/
def coherentCellGaugeIso {d n : ℕ} (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    ModuleCat.of R R ≅ ModuleCat.of R R :=
  (minimalCellTopHomologyIso R d n σ hdim).symm ≪≫ coherentCellTopHomologyIso R σ hdim

theorem coherentMinimalCoefficient_eq_old {d n : ℕ} (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalCoefficient R i₀ σ hdim =
      minimalCellCoefficient R i₀ σ hdim ≫ (coherentCellGaugeIso R σ hdim).hom := by
  simp [coherentMinimalCoefficient,minimalCellCoefficient,coherentCellGaugeIso,Category.assoc]

theorem coherentMinimalGenerator_eq_old {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalGenerator R i₀ σ hdim =
      (coherentCellGaugeIso R σ hdim).inv ≫ minimalCellGenerator R i₀ σ hdim := by
  rw [coherentMinimalGenerator_factor]
  simp [coherentCellGaugeIso,minimalCellGenerator,Category.assoc]

theorem coherentMinimalGenerator_coefficient_same {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalGenerator R i₀ σ hdim ≫ coherentMinimalCoefficient R i₀ σ hdim = 𝟙 _ := by
  rw [coherentMinimalGenerator_factor]
  unfold coherentMinimalCoefficient
  rw [Category.assoc,← Category.assoc _ _ (coherentCellTopHomologyIso R σ hdim).hom,
    ← HabsMap_comp,minimalCellInclusionMap_retraction,HabsMap_id,Category.id_comp,
    Iso.inv_hom_id]

theorem coherentMinimalGenerator_coefficient_other {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ τ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) (hne : σ ≠ τ) :
    coherentMinimalGenerator R i₀ σ hdim ≫ coherentMinimalCoefficient R i₀ τ hdim = 0 := by
  have h : HabsMap R (d+n) (minimalCellInclusionMap (d := d) i₀ σ) ≫
      HabsMap R (d+n) (minimalCellRetractionMap i₀ τ) = 0 := by
    rw [← HabsMap_comp,minimalCellInclusionMap_retraction_other i₀ σ τ hne]
    exact HabsMap_const_eq_zero R (d+n) hdim.ne'
      (X := TopCat.of (OnePoint (Space d × heightChamber n σ)))
      (Y := TopCat.of (OnePoint (Space d × heightChamber n τ))) ∞
  rw [coherentMinimalGenerator_factor]
  unfold coherentMinimalCoefficient
  rw [Category.assoc,← Category.assoc _ _ (coherentCellTopHomologyIso R τ hdim).hom,
    h,zero_comp,comp_zero]

def coherentMinimalClass {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) :=
  coherentMinimalGenerator R i₀ σ hdim 1

/-- Exact left regular action on genuine singular homology classes. -/
theorem coherentMinimalClass_relabel {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ τ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    HabsMap R (d+n) (minimalSkeletonRelabelMap σ) (coherentMinimalClass R i₀ τ hdim) =
      coherentMinimalClass R i₀ (σ*τ) hdim :=
  congrArg (fun f : ModuleCat.of R R ⟶ Habs R (d+n) (TopCat.of (minimalSkeleton d n)) => f 1)
    (coherentMinimalGenerator_relabel R i₀ σ τ hdim)

theorem coherentMinimalClass_coefficient {d n : ℕ} [NeZero n] (i₀ : Fin n)
    (σ τ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalCoefficient R i₀ τ hdim (coherentMinimalClass R i₀ σ hdim) =
      if σ = τ then 1 else 0 := by
  classical
  by_cases h : σ = τ
  · subst τ
    simpa only [if_pos rfl] using
      congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
        (coherentMinimalGenerator_coefficient_same R i₀ σ hdim)
  · simpa only [if_neg h] using
      congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f 1)
        (coherentMinimalGenerator_coefficient_other R i₀ σ τ hdim h)

theorem coherentMinimalClass_ne_zero [Nontrivial R] {d n : ℕ} [NeZero n]
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) (hdim : 0 < d+n) :
    coherentMinimalClass R i₀ σ hdim ≠ 0 := by
  intro hz
  have h := coherentMinimalClass_coefficient R i₀ σ σ hdim
  rw [hz,map_zero,if_pos rfl] at h
  exact zero_ne_one h

theorem linearIndependent_coherentMinimalClass {d n : ℕ} [NeZero n]
    (i₀ : Fin n) (hdim : 0 < d+n) :
    LinearIndependent R (fun σ : Equiv.Perm (Fin n) => coherentMinimalClass R i₀ σ hdim) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg τ
  let c : Habs R (d+n) (TopCat.of (minimalSkeleton d n)) →ₗ[R] R :=
    (coherentMinimalCoefficient R i₀ τ hdim).hom
  have cv (σ : Equiv.Perm (Fin n)) :
      c (coherentMinimalClass R i₀ σ hdim) = if σ = τ then 1 else 0 :=
    coherentMinimalClass_coefficient R i₀ σ τ hdim
  have h := congrArg c hg
  simp only [map_sum,map_smul,cv,map_zero,smul_eq_mul,mul_ite,mul_one,mul_zero] at h
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

def minimalLevelMap (d n : ℕ) [NeZero n] :
    TopCat.of (minimalSkeleton d n) ⟶ TopCat.of (compactifiedFuksLevel d n d) :=
  TopCat.ofHom ⟨minimalLevelHomeomorph d n,(minimalLevelHomeomorph d n).continuous⟩

theorem minimalLevelMap_relabel {d n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    minimalSkeletonRelabelMap σ ≫ minimalLevelMap d n =
      minimalLevelMap d n ≫ compactifiedFuksRelabelMap σ := by
  ext x
  rfl

/-- The canonical map into the homology of the actual lowest Fuks pair. -/
def minimalActualRelativeComparison (d n : ℕ) [NeZero n] :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ⟶
      (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) :=
  HabsMap R (d+n) (minimalLevelMap d n) ≫
    relJ R (d+n) (compactifiedFuksInclusion (show d-1 ≤ d by omega))

theorem isIso_minimalActualRelativeComparison (d n : ℕ) [NeZero n] (hd : 0 < d) :
    IsIso (minimalActualRelativeComparison R d n) := by
  letI : IsIso (HabsMap R (d+n) (minimalLevelMap d n)) := by
    change IsIso (HabsIsoOfHomotopyEquiv R (d+n)
      (minimalLevelHomeomorph d n).toHomotopyEquiv).hom
    infer_instance
  letI := contractible_lowerFuksLevel d n hd
  have hdim : 2 ≤ d+n := by have hn := NeZero.pos n; omega
  obtain ⟨q,hq⟩ : ∃ q : ℕ,d+n = q+2 := ⟨d+n-2,by omega⟩
  letI : IsIso (relJ R (d+n)
      (compactifiedFuksInclusion (d := d) (n := n) (show d-1 ≤ d by omega))) := by
    rw [hq]
    change IsIso (relativeOfContractibleSubspaceIso R q
      (compactifiedFuksInclusion (d := d) (n := n) (show d-1 ≤ d by omega))).hom
    infer_instance
  unfold minimalActualRelativeComparison
  infer_instance

def minimalActualRelativeComparisonIso (d n : ℕ) [NeZero n] (hd : 0 < d) :
    Habs R (d+n) (TopCat.of (minimalSkeleton d n)) ≅
      (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) := by
  letI := isIso_minimalActualRelativeComparison R d n hd
  exact asIso (minimalActualRelativeComparison R d n)

@[simp] theorem minimalActualRelativeComparisonIso_hom
    (d n : ℕ) [NeZero n] (hd : 0 < d) :
    (minimalActualRelativeComparisonIso R d n hd).hom =
      minimalActualRelativeComparison R d n := rfl

theorem minimalActualRelativeComparison_naturality {d n : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) :
    HabsMap R (d+n) (minimalSkeletonRelabelMap σ) ≫ minimalActualRelativeComparison R d n =
      minimalActualRelativeComparison R d n ≫
        HomologicalComplex.homologyMap
          (fuksRelativeRelabel R (d := d) (n := n) (show d-1 ≤ d by omega) σ) (d+n) := by
  unfold minimalActualRelativeComparison
  rw [← Category.assoc,← HabsMap_comp,minimalLevelMap_relabel,HabsMap_comp,
    Category.assoc,Category.assoc]
  apply congrArg (fun f => HabsMap R (d+n) (minimalLevelMap d n) ≫ f)
  exact (relJ_naturality R (d+n)
    (compactifiedFuksInclusion (d := d) (n := n) (show d-1 ≤ d by omega))
    (compactifiedFuksInclusion (show d-1 ≤ d by omega))
    (compactifiedFuksInclusion_equivariant (show d-1 ≤ d by omega) σ)).symm

def coherentMinimalRelativeGenerator {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    ModuleCat.of R R ⟶
      (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) :=
  coherentMinimalGenerator R i₀ σ (by omega) ≫ minimalActualRelativeComparison R d n

theorem coherentMinimalRelativeGenerator_relabel {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    coherentMinimalRelativeGenerator R hd i₀ τ ≫
        HomologicalComplex.homologyMap
          (fuksRelativeRelabel R (d := d) (n := n) (show d-1 ≤ d by omega) σ) (d+n) =
      coherentMinimalRelativeGenerator R hd i₀ (σ*τ) := by
  unfold coherentMinimalRelativeGenerator
  rw [Category.assoc,← minimalActualRelativeComparison_naturality,
    ← Category.assoc,coherentMinimalGenerator_relabel]

def coherentMinimalRelativeClass {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) :=
  coherentMinimalRelativeGenerator R hd i₀ σ 1

theorem coherentMinimalRelativeClass_relabel {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    HomologicalComplex.homologyMap
        (fuksRelativeRelabel R (d := d) (n := n) (show d-1 ≤ d by omega) σ) (d+n)
        (coherentMinimalRelativeClass R hd i₀ τ) =
      coherentMinimalRelativeClass R hd i₀ (σ*τ) :=
  congrArg (fun f : ModuleCat.of R R ⟶
    (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) => f 1)
    (coherentMinimalRelativeGenerator_relabel R hd i₀ σ τ)

def coherentMinimalRelativeCoefficient {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) ⟶
      ModuleCat.of R R :=
  (minimalActualRelativeComparisonIso R d n hd).inv ≫
    coherentMinimalCoefficient R i₀ σ (by omega)

theorem coherentMinimalRelativeClass_coefficient {d n : ℕ} [NeZero n] (hd : 0 < d)
    (i₀ : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    coherentMinimalRelativeCoefficient R hd i₀ τ (coherentMinimalRelativeClass R hd i₀ σ) =
      if σ = τ then 1 else 0 := by
  have hi := (minimalActualRelativeComparisonIso R d n hd).hom_inv_id
  rw [minimalActualRelativeComparisonIso_hom] at hi
  have h : coherentMinimalRelativeGenerator R hd i₀ σ ≫
      coherentMinimalRelativeCoefficient R hd i₀ τ =
      coherentMinimalGenerator R (d := d) i₀ σ (by omega) ≫
        coherentMinimalCoefficient R (d := d) i₀ τ (by omega) := by
    unfold coherentMinimalRelativeGenerator coherentMinimalRelativeCoefficient
    rw [Category.assoc,← Category.assoc _ _ (coherentMinimalCoefficient R (d := d) i₀ τ (by omega)),
      hi,Category.id_comp]
  change coherentMinimalRelativeCoefficient R hd i₀ τ
    (coherentMinimalRelativeGenerator R hd i₀ σ 1) = _
  rw [← ModuleCat.comp_apply,h,ModuleCat.comp_apply]
  exact coherentMinimalClass_coefficient R (d := d) i₀ σ τ (by omega)

theorem coherentMinimalRelativeClass_ne_zero [Nontrivial R] {d n : ℕ} [NeZero n]
    (hd : 0 < d) (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    coherentMinimalRelativeClass R hd i₀ σ ≠ 0 := by
  intro hz
  have h := coherentMinimalRelativeClass_coefficient R hd i₀ σ σ
  rw [hz,map_zero,if_pos rfl] at h
  exact zero_ne_one h

theorem linearIndependent_coherentMinimalRelativeClass {d n : ℕ} [NeZero n]
    (hd : 0 < d) (i₀ : Fin n) :
    LinearIndependent R (fun σ : Equiv.Perm (Fin n) => coherentMinimalRelativeClass R hd i₀ σ) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg τ
  let c :
      (fuksRelativeComplex R (d := d) (n := n) (show d-1 ≤ d by omega)).homology (d+n) →ₗ[R] R :=
    (coherentMinimalRelativeCoefficient R hd i₀ τ).hom
  have cv (σ : Equiv.Perm (Fin n)) :
      c (coherentMinimalRelativeClass R hd i₀ σ) = if σ = τ then 1 else 0 :=
    coherentMinimalRelativeClass_coefficient R hd i₀ σ τ
  have h := congrArg c hg
  simp only [map_sum,map_smul,cv,map_zero,smul_eq_mul,mul_ite,mul_one,mul_zero] at h
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

private theorem homologyMap_smul_modules
    {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (r : R) (q : ℕ) :
    HomologicalComplex.homologyMap (r • f) q = r • HomologicalComplex.homologyMap f q := by
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map
      (r • f) = r • (HomologicalComplex.shortComplexFunctor (ModuleCat R)
        (ComplexShape.down ℕ) q).map f by rfl,
    ShortComplex.homologyMap_smul]

/-- The character relation holds on the homology of the actual twisted
relative chain complex, because it already holds between its chain maps. -/
theorem minimalTwistedProjection_homology_action {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (σ : Equiv.Perm (Fin n)) (q : ℕ) :
    HomologicalComplex.homologyMap
        (fuksRelativeRelabel R (d := d) (n := n) (show d-1 ≤ d by omega) σ) q ≫
      HomologicalComplex.homologyMap
        (twistedFuksRelativeProj R (d := d) χ (show d-1 ≤ d by omega)) q =
      (χ σ : R) • HomologicalComplex.homologyMap
        (twistedFuksRelativeProj R (d := d) χ (show d-1 ≤ d by omega)) q := by
  rw [← HomologicalComplex.homologyMap_comp,fuksRelativeRelabel_proj,homologyMap_smul_modules]

/-- The image of the coherent identity-cell map in genuine twisted-chain
homology. Nonvanishing is deliberately a separate chain-comparison problem. -/
def coherentTwistedMinimalMap {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    ModuleCat.of R R ⟶
      (twistedFuksRelativeComplex R (d := d) χ (show d-1 ≤ d by omega)).homology (d+n) :=
  coherentMinimalRelativeGenerator R hd i₀ 1 ≫ HomologicalComplex.homologyMap
    (twistedFuksRelativeProj R (d := d) χ (show d-1 ≤ d by omega)) (d+n)

theorem coherentMinimalRelativeGenerator_twistedImage {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) :
    coherentMinimalRelativeGenerator R hd i₀ σ ≫ HomologicalComplex.homologyMap
        (twistedFuksRelativeProj R (d := d) χ (show d-1 ≤ d by omega)) (d+n) =
      (χ σ : R) • coherentTwistedMinimalMap R χ hd i₀ := by
  have h := coherentMinimalRelativeGenerator_relabel R hd i₀ σ 1
  simp only [mul_one] at h
  rw [← h,Category.assoc,minimalTwistedProjection_homology_action,Linear.comp_smul]
  rfl

def coherentTwistedMinimalClass {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n) :
    (twistedFuksRelativeComplex R (d := d) χ (show d-1 ≤ d by omega)).homology (d+n) :=
  coherentTwistedMinimalMap R χ hd i₀ 1

theorem coherentMinimalRelativeClass_twistedImage {d n : ℕ} [NeZero n]
    (χ : Equiv.Perm (Fin n) →* Rˣ) (hd : 0 < d) (i₀ : Fin n)
    (σ : Equiv.Perm (Fin n)) :
    HomologicalComplex.homologyMap
        (twistedFuksRelativeProj R (d := d) χ (show d-1 ≤ d by omega)) (d+n)
        (coherentMinimalRelativeClass R hd i₀ σ) =
      (χ σ : R) • coherentTwistedMinimalClass R χ hd i₀ := by
  have h := congrArg (fun f : ModuleCat.of R R ⟶
      (twistedFuksRelativeComplex R (d := d) χ (show d-1 ≤ d by omega)).homology (d+n) => f 1)
    (coherentMinimalRelativeGenerator_twistedImage R χ hd i₀ σ)
  simpa only [ModuleCat.comp_apply,coherentMinimalRelativeClass,
    coherentTwistedMinimalClass,ModuleCat.hom_smul,LinearMap.smul_apply] using h

end Homology
end NRR.PrimePowerTopology
