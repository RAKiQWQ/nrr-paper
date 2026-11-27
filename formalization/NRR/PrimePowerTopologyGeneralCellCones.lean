import NRR.ClosedPolyhedralCone
import NRR.PrimePowerTopologyFiltration
import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Genuine Fox--Neuwirth closed-cone parameters for arbitrary adjacent
prefix-depth words. There are m+1 labels in D coordinates. The word a_i
specifies the first distinct coordinate of labels i and i+1. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology Metric
open scoped OnePoint
open NRR.PrimePower

namespace NRR.PrimePowerTopology

abbrev GeneralCellAmbient (D m : ℕ) := Fin (m+1) → Space D

/-- Equalities in the coordinates preceding each specified first difference. -/
def generalCellLinearSpace {D m : ℕ} (a : Fin m → Fin D) :
    Submodule ℝ (GeneralCellAmbient D m) where
  carrier := {x | ∀ i : Fin m, ∀ k : Fin D, k < a i → x i.castSucc k = x i.succ k}
  zero_mem' := by intro i k _; simp
  add_mem' := by
    intro x y hx hy i k hk
    change x i.castSucc k + y i.castSucc k = x i.succ k + y i.succ k
    rw [hx i k hk, hy i k hk]
  smul_mem' := by
    intro c x hx i k hk
    change c * x i.castSucc k = c * x i.succ k
    rw [hx i k hk]

/-- The adjacent gap at the first coordinate allowed to separate two labels. -/
def generalCellGap {D m : ℕ} (a : Fin m → Fin D) (i : Fin m) :
    generalCellLinearSpace a →L[ℝ] ℝ :=
  ((EuclideanSpace.proj (a i)).comp
    ((ContinuousLinearMap.proj i.succ).comp (generalCellLinearSpace a).subtypeL)) -
  ((EuclideanSpace.proj (a i)).comp
    ((ContinuousLinearMap.proj i.castSucc).comp (generalCellLinearSpace a).subtypeL))

@[simp] theorem generalCellGap_apply {D m : ℕ} (a : Fin m → Fin D) (i : Fin m)
    (x : generalCellLinearSpace a) :
    generalCellGap a i x = x.val i.succ (a i) - x.val i.castSucc (a i) := rfl

def generalCellDirectionVector {D m : ℕ} (a : Fin m → Fin D) : GeneralCellAmbient D m :=
  fun i => WithLp.toLp 2 fun k =>
    ∑ j : Fin m, if j.val < i.val then (if a j ≤ k then (1 : ℝ) else 0) else 0

theorem generalCellDirectionVector_step {D m : ℕ} (a : Fin m → Fin D)
    (i : Fin m) (k : Fin D) :
    generalCellDirectionVector a i.succ k = generalCellDirectionVector a i.castSucc k +
      (if a i ≤ k then 1 else 0) := by
  classical
  change (∑ j : Fin m, if j.val < i.val+1 then (if a j ≤ k then (1 : ℝ) else 0) else 0) =
    (∑ j : Fin m, if j.val < i.val then (if a j ≤ k then (1 : ℝ) else 0) else 0) + _
  calc
    _ = ∑ j : Fin m,
        ((if j.val < i.val then (if a j ≤ k then (1 : ℝ) else 0) else 0) +
          if j = i then (if a j ≤ k then (1 : ℝ) else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j; simp
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        by_cases hlt : j.val < i.val
        · have hlt' : j.val < i.val+1 := by omega
          simp only [hlt, hlt', hji, if_true, if_false, add_zero]
        · have hlt' : ¬ j.val < i.val+1 := by omega
          simp only [hlt, hlt', hji, if_false, zero_add]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem generalCellDirectionVector_mem {D m : ℕ} (a : Fin m → Fin D) :
    generalCellDirectionVector a ∈ generalCellLinearSpace a := by
  intro i k hk
  have h := generalCellDirectionVector_step a i k
  simp only [not_le_of_gt hk, if_false, add_zero] at h
  exact h.symm

def generalCellDirection {D m : ℕ} (a : Fin m → Fin D) : generalCellLinearSpace a :=
  ⟨generalCellDirectionVector a, generalCellDirectionVector_mem a⟩

@[simp] theorem generalCellGap_direction {D m : ℕ} (a : Fin m → Fin D) (i : Fin m) :
    generalCellGap a i (generalCellDirection a) = 1 := by
  rw [generalCellGap_apply]
  change generalCellDirectionVector a i.succ (a i) -
    generalCellDirectionVector a i.castSucc (a i) = 1
  rw [generalCellDirectionVector_step]
  simp

def generalCellClosedDomain {D m : ℕ} (a : Fin m → Fin D) :
    Set (generalCellLinearSpace a) := ClosedPolyhedralCone.carrier (generalCellGap a)

def generalCellOpenDomain {D m : ℕ} (a : Fin m → Fin D) :
    Set (generalCellLinearSpace a) := ClosedPolyhedralCone.strict (generalCellGap a)

theorem generalCellOpenDomain_nonempty {D m : ℕ} (a : Fin m → Fin D) :
    (generalCellOpenDomain a).Nonempty :=
  ⟨generalCellDirection a, fun i => by rw [generalCellGap_direction]; exact zero_lt_one⟩

/-- The prescribed first differences put the actual label vectors in
strict lexicographic order, so every point of an open cell is a configuration. -/
theorem generalCellAmbient_injective {D m : ℕ} (a : Fin m → Fin D)
    (x : generalCellLinearSpace a) (hx : x ∈ generalCellOpenDomain a) :
    Function.Injective x.val := by
  have hm : StrictMono (fun i : Fin (m+1) => toLex (fun k : Fin D => x.val i k)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine ⟨a i, fun k hk => x.property i k hk, ?_⟩
    exact sub_pos.mp (hx i)
  intro i j hij
  apply hm.injective
  exact congrArg (fun z : Space D => toLex (fun k : Fin D => z k)) hij

def generalCellConfigurationMap {D m : ℕ} (a : Fin m → Fin D) :
    C(generalCellOpenDomain a, Configuration D (m+1)) where
  toFun x := ⟨x.val.val, generalCellAmbient_injective a x.val x.property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem isEmbedding_generalCellConfigurationMap {D m : ℕ} (a : Fin m → Fin D) :
    IsEmbedding (generalCellConfigurationMap a) := by
  have h : IsEmbedding (fun x : generalCellOpenDomain a =>
      (x.val.val : GeneralCellAmbient D m)) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  exact IsEmbedding.of_comp (generalCellConfigurationMap a).continuous continuous_subtype_val h

theorem interior_generalCellClosedDomain {D m : ℕ} (a : Fin m → Fin D) :
    interior (generalCellClosedDomain a) = generalCellOpenDomain a :=
  ClosedPolyhedralCone.interior_carrier (generalCellGap a)
    (fun i => by rw [generalCellGap_direction]; exact zero_lt_one)

/-- Every genuine prefix-depth closed cone, with at least two labels,
has a disk compactification in its actual linear parameter space. -/
def generalCellClosedDisk {D m : ℕ} [NeZero m] (a : Fin m → Fin D) :
    OnePoint (generalCellClosedDomain a) ≃ₜ
      closedBall (0 : generalCellLinearSpace a) 1 :=
  ClosedPolyhedralCone.onePointHomeomorphClosedBall (generalCellGap a)
    (fun i => by rw [generalCellGap_direction]; exact zero_lt_one)

@[simp] theorem generalCellClosedDisk_infty_mem_sphere {D m : ℕ} [NeZero m]
    (a : Fin m → Fin D) :
    (generalCellClosedDisk a (∞ : OnePoint (generalCellClosedDomain a)) :
        generalCellLinearSpace a) ∈ sphere 0 1 :=
  ClosedPolyhedralCone.onePointHomeomorphClosedBall_infty_mem_sphere _ _

@[simp] theorem generalCellClosedDisk_coe_mem_sphere_iff {D m : ℕ} [NeZero m]
    (a : Fin m → Fin D) (x : generalCellClosedDomain a) :
    (generalCellClosedDisk a (x : OnePoint (generalCellClosedDomain a)) :
        generalCellLinearSpace a) ∈ sphere 0 1 ↔ x.val ∉ generalCellOpenDomain a :=
  ClosedPolyhedralCone.onePointHomeomorphClosedBall_coe_mem_sphere_iff _ _ _

abbrev GeneralCellFreeIndex {D m : ℕ} (a : Fin m → Fin D) :=
  Σ i : Fin m, Set.Ici (a i)

abbrev GeneralCellFreeCoordinates {D m : ℕ} (a : Fin m → Fin D) :=
  Space D × (GeneralCellFreeIndex a → ℝ)

def generalCellPrefixSum {m : ℕ} (b : Fin m → ℝ) (i : Fin (m+1)) : ℝ :=
  ∑ j : Fin m, if j.val < i.val then b j else 0

@[simp] theorem generalCellPrefixSum_zero {m : ℕ} (b : Fin m → ℝ) :
    generalCellPrefixSum b 0 = 0 := by simp [generalCellPrefixSum]

theorem generalCellPrefixSum_step {m : ℕ} (b : Fin m → ℝ) (i : Fin m) :
    generalCellPrefixSum b i.succ = generalCellPrefixSum b i.castSucc + b i := by
  classical
  unfold generalCellPrefixSum
  change (∑ j : Fin m, if j.val < i.val+1 then b j else 0) =
    (∑ j : Fin m, if j.val < i.val then b j else 0) + _
  calc
    _ = ∑ j : Fin m, ((if j.val < i.val then b j else 0) + if j = i then b j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j; simp
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        by_cases hlt : j.val < i.val
        · have hlt' : j.val < i.val+1 := by omega
          simp only [hlt, hlt', hji, if_true, if_false, add_zero]
        · have hlt' : ¬ j.val < i.val+1 := by omega
          simp only [hlt, hlt', hji, if_false, zero_add]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

def generalCellFreeCoordinatesMap {D m : ℕ} (a : Fin m → Fin D) :
    generalCellLinearSpace a →ₗ[ℝ] GeneralCellFreeCoordinates a where
  toFun x := (x.val 0, fun ik => x.val ik.1.succ ik.2.val - x.val ik.1.castSucc ik.2.val)
  map_add' := by
    intro x y
    apply Prod.ext
    · rfl
    · funext ik
      change (x.val ik.1.succ ik.2.val + y.val ik.1.succ ik.2.val) -
        (x.val ik.1.castSucc ik.2.val + y.val ik.1.castSucc ik.2.val) = _
      simp only [Prod.snd_add, Pi.add_apply]
      ring
  map_smul' := by
    intro c x
    apply Prod.ext
    · rfl
    · funext ik
      change c * x.val ik.1.succ ik.2.val - c * x.val ik.1.castSucc ik.2.val =
        c * (x.val ik.1.succ ik.2.val - x.val ik.1.castSucc ik.2.val)
      ring

def generalCellFreeIncrement {D m : ℕ} (a : Fin m → Fin D)
    (p : GeneralCellFreeCoordinates a) (k : Fin D) (j : Fin m) : ℝ :=
  if h : a j ≤ k then p.2 ⟨j,⟨k,h⟩⟩ else 0

def generalCellFromCoordinatesVector {D m : ℕ} (a : Fin m → Fin D)
    (p : GeneralCellFreeCoordinates a) : GeneralCellAmbient D m :=
  fun i => WithLp.toLp 2 fun k => p.1 k + generalCellPrefixSum (generalCellFreeIncrement a p k) i

theorem generalCellFromCoordinatesVector_step {D m : ℕ} (a : Fin m → Fin D)
    (p : GeneralCellFreeCoordinates a) (i : Fin m) (k : Fin D) :
    generalCellFromCoordinatesVector a p i.succ k =
      generalCellFromCoordinatesVector a p i.castSucc k + generalCellFreeIncrement a p k i := by
  change p.1 k + generalCellPrefixSum _ i.succ =
    (p.1 k + generalCellPrefixSum _ i.castSucc) + _
  rw [generalCellPrefixSum_step]
  ring

theorem generalCellFromCoordinatesVector_mem {D m : ℕ} (a : Fin m → Fin D)
    (p : GeneralCellFreeCoordinates a) :
    generalCellFromCoordinatesVector a p ∈ generalCellLinearSpace a := by
  intro i k hk
  rw [generalCellFromCoordinatesVector_step, generalCellFreeIncrement,
    dif_neg (not_le_of_gt hk), add_zero]

def generalCellFromCoordinates {D m : ℕ} (a : Fin m → Fin D)
    (p : GeneralCellFreeCoordinates a) : generalCellLinearSpace a :=
  ⟨generalCellFromCoordinatesVector a p, generalCellFromCoordinatesVector_mem a p⟩

theorem generalCellFreeCoordinatesMap_rightInverse {D m : ℕ} (a : Fin m → Fin D)
    (p : GeneralCellFreeCoordinates a) :
    generalCellFreeCoordinatesMap a (generalCellFromCoordinates a p) = p := by
  apply Prod.ext
  · apply PiLp.ext
    intro k
    change p.1 k + generalCellPrefixSum _ 0 = p.1 k
    simp
  · funext ik
    change generalCellFromCoordinatesVector a p ik.1.succ ik.2.val -
      generalCellFromCoordinatesVector a p ik.1.castSucc ik.2.val = p.2 ik
    rw [generalCellFromCoordinatesVector_step, add_sub_cancel_left,
      generalCellFreeIncrement, dif_pos (show a ik.1 ≤ ik.2.val from ik.2.property)]

theorem generalCellFreeCoordinatesMap_injective {D m : ℕ} (a : Fin m → Fin D) :
    Function.Injective (generalCellFreeCoordinatesMap a) := by
  intro x y hxy
  have hzero : x.val 0 = y.val 0 := congrArg Prod.fst hxy
  have hinc (i : Fin m) (k : Fin D) (hk : a i ≤ k) :
      x.val i.succ k - x.val i.castSucc k = y.val i.succ k - y.val i.castSucc k :=
    congrArg (fun p : GeneralCellFreeCoordinates a => p.2 ⟨i,⟨k,hk⟩⟩) hxy
  apply Subtype.ext
  funext i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ i hi =>
      apply PiLp.ext
      intro k
      by_cases hk : a i ≤ k
      · have hh := hinc i k hk
        rw [congrArg (fun z : Space D => z k) hi] at hh
        linarith
      · have hlt := lt_of_not_ge hk
        rw [← x.property i k hlt, ← y.property i k hlt]
        exact congrArg (fun z : Space D => z k) hi

/-- Initial position and every unconstrained adjacent coordinate increment
are independent linear coordinates on the actual prefix-equality space. -/
def generalCellCoordinateEquiv {D m : ℕ} (a : Fin m → Fin D) :
    generalCellLinearSpace a ≃ₗ[ℝ] GeneralCellFreeCoordinates a :=
  LinearEquiv.ofBijective (generalCellFreeCoordinatesMap a)
    ⟨generalCellFreeCoordinatesMap_injective a,
      fun p => ⟨generalCellFromCoordinates a p, generalCellFreeCoordinatesMap_rightInverse a p⟩⟩

theorem card_generalCellFreeIndex {D m : ℕ} (a : Fin m → Fin D) :
    Fintype.card (GeneralCellFreeIndex a) = ∑ i : Fin m, (D - (a i).val) := by
  simp only [GeneralCellFreeIndex, Fintype.card_sigma, Fintype.card_Ici, Fin.card_Ici]

theorem finrank_generalCellLinearSpace_sum {D m : ℕ} (a : Fin m → Fin D) :
    Module.finrank ℝ (generalCellLinearSpace a) = D + ∑ i : Fin m, (D - (a i).val) := by
  rw [(generalCellCoordinateEquiv a).finrank_eq]
  simp only [GeneralCellFreeCoordinates, Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_pi_fintype, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, card_generalCellFreeIndex]

/-- The dimension agrees with the usual Fox--Neuwirth word formula. -/
theorem finrank_generalCellLinearSpace {D m : ℕ} (a : Fin m → Fin D) :
    Module.finrank ℝ (generalCellLinearSpace a) = D * (m+1) - ∑ i : Fin m, (a i).val := by
  rw [finrank_generalCellLinearSpace_sum]
  have hs : (∑ i : Fin m, (D - (a i).val)) + (∑ i : Fin m, (a i).val) = m * D := by
    rw [← Finset.sum_add_distrib]
    have he (i : Fin m) : D - (a i).val + (a i).val = D := by omega
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hp : D * (m+1) = D + m * D := by ring
  omega

private theorem card_image_monotone_fin {α : Type*} [PartialOrder α]
    [DecidableEq α] [DecidableLT α] {m : ℕ}
    (f : Fin (m+1) → α) (hf : Monotone f) :
    (Finset.univ.image f).card =
      1 + ∑ i : Fin m, if f i.castSucc < f i.succ then 1 else 0 := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      let g : Fin (m+1) → α := fun i => f i.castSucc
      have hg : Monotone g := hf.comp Fin.strictMono_castSucc.monotone
      have repr : Finset.univ.image f =
          insert (f (Fin.last (m+1))) (Finset.univ.image g) := by
        ext y
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨i, rfl⟩
          induction i using Fin.lastCases with
          | last => exact Or.inl rfl
          | cast i => exact Or.inr ⟨i, rfl⟩
        · rintro (rfl | ⟨i, rfl⟩)
          · exact ⟨Fin.last (m+1), rfl⟩
          · exact ⟨i.castSucc, rfl⟩
      rw [repr, Fin.sum_univ_castSucc]
      by_cases hlt : f (Fin.last m).castSucc < f (Fin.last m).succ
      · have hnew : f (Fin.last (m+1)) ∉ Finset.univ.image g := by
          rintro hmem
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
          have hle : f i.castSucc ≤ f (Fin.last m).castSucc :=
            hf (Fin.strictMono_castSucc.monotone (Fin.le_last i))
          exact (ne_of_lt (hle.trans_lt hlt)) hi
        rw [Finset.card_insert_of_notMem hnew, ih g hg]
        simp only [hlt, if_true]
        rfl
      · have he : g (Fin.last m) = f (Fin.last (m+1)) := by
          by_contra hne
          exact hlt (lt_of_le_of_ne (hf (Fin.castSucc_le_succ _)) hne)
        have hmem : f (Fin.last (m+1)) ∈ Finset.univ.image g :=
          he ▸ Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, rfl⟩
        rw [Finset.card_insert_of_mem hmem, ih g hg]
        simp only [hlt, if_false, add_zero]
        rfl

/-- Before a word's first difference, adjacent labels have the same actual
horizontal prefix used by the closed Fuks filtration. -/
theorem generalCell_fuksProjection_step_eq {d m : ℕ} (a : Fin m → Fin (d+1))
    (x : generalCellOpenDomain a) (k : Fin d) (i : Fin m)
    (hk : k.castSucc < a i) :
    fuksProjection (generalCellConfigurationMap a x) k i.castSucc =
      fuksProjection (generalCellConfigurationMap a x) k i.succ := by
  funext l
  change (if l ≤ k then x.val.val i.castSucc l.castSucc else 0) =
    (if l ≤ k then x.val.val i.succ l.castSucc else 0)
  by_cases hl : l ≤ k
  · simp only [hl, if_true]
    exact x.val.property i l.castSucc
      ((Fin.strictMono_castSucc.monotone hl).trans_lt hk)
  · simp only [hl, if_false]

/-- At and beyond a word's first difference the adjacent horizontal prefixes
are strictly ordered, so they can never merge again later in the label order. -/
theorem generalCell_fuksProjection_step_lt {d m : ℕ} (a : Fin m → Fin (d+1))
    (x : generalCellOpenDomain a) (k : Fin d) (i : Fin m)
    (hk : a i ≤ k.castSucc) :
    toLex (fuksProjection (generalCellConfigurationMap a x) k i.castSucc) <
      toLex (fuksProjection (generalCellConfigurationMap a x) k i.succ) := by
  let l : Fin d := ⟨(a i).val, lt_of_le_of_lt hk k.isLt⟩
  have hl : l ≤ k := hk
  have hcast : l.castSucc = a i := Fin.ext rfl
  refine ⟨l, ?_, ?_⟩
  · intro j hj
    change (if j ≤ k then x.val.val i.castSucc j.castSucc else 0) =
      (if j ≤ k then x.val.val i.succ j.castSucc else 0)
    simp only [if_pos (hj.le.trans hl)]
    exact x.val.property i j.castSucc (by simpa only [← hcast] using hj)
  · change (if l ≤ k then x.val.val i.castSucc l.castSucc else 0) <
      (if l ≤ k then x.val.val i.succ l.castSucc else 0)
    simp only [hl, if_true]
    exact sub_pos.mp (x.property i)

/-- Exact number of distinct prefixes of length k+1 in an open word chart. -/
theorem card_fuksProjection_generalCell {d m : ℕ} (a : Fin m → Fin (d+1))
    (x : generalCellOpenDomain a) (k : Fin d) :
    (Finset.univ.image (fuksProjection (generalCellConfigurationMap a x) k)).card =
      1 + ∑ i : Fin m, if a i ≤ k.castSucc then 1 else 0 := by
  classical
  let f : Fin (m+1) → Lex (Fin d → ℝ) :=
    fun i => toLex (fuksProjection (generalCellConfigurationMap a x) k i)
  have hmono : Monotone f := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    by_cases hk : a i ≤ k.castSucc
    · exact (generalCell_fuksProjection_step_lt a x k i hk).le
    · exact (congrArg toLex
        (generalCell_fuksProjection_step_eq a x k i (lt_of_not_ge hk))).le
  have hcard : (Finset.univ.image f).card =
      (Finset.univ.image (fuksProjection (generalCellConfigurationMap a x) k)).card := by
    change (Finset.univ.image (toLex ∘
      fuksProjection (generalCellConfigurationMap a x) k)).card = _
    rw [← Finset.image_image]
    exact Finset.card_image_of_injective _ (fun _ _ h => h)
  rw [← hcard, card_image_monotone_fin f hmono]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hk : a i ≤ k.castSucc
  · simp only [hk, if_true,
      generalCell_fuksProjection_step_lt a x k i hk, f]
  · have he := generalCell_fuksProjection_step_eq a x k i (lt_of_not_ge hk)
    simp only [f, he, lt_self_iff_false, if_false, hk]

private theorem sum_generalCell_prefix_indicators {d : ℕ} (a : Fin (d+1)) :
    (∑ k : Fin d, if a ≤ k.castSucc then 1 else 0) = d - a.val := by
  have hfull : (∑ k : Fin (d+1), if a ≤ k then 1 else 0) = d + 1 - a.val := by
    have he : (Finset.univ.filter (fun k : Fin (d+1) => a ≤ k)) = Finset.Ici a := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    simp only [Finset.sum_boole, Nat.cast_id, he, Fin.card_Ici]
  rw [Fin.sum_univ_castSucc] at hfull
  simp only [Fin.le_last, if_true] at hfull
  have ha := a.isLt
  omega

/-- The actual prefix-count filtration degree is constant on each open word
chart, and is computed directly from the depths in its adjacent-difference word. -/
theorem fuksComplexity_generalCell {d m : ℕ} (a : Fin m → Fin (d+1))
    (x : generalCellOpenDomain a) :
    fuksComplexity (generalCellConfigurationMap a x) =
      d + ∑ i : Fin m, (d - (a i).val) := by
  classical
  unfold fuksComplexity
  simp_rw [card_fuksProjection_generalCell]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => sum_generalCell_prefix_indicators (a i))

/-- The geometric dimension is precisely the genuine Fuks filtration degree
plus the number of labels, for every configuration in this open word chart. -/
theorem finrank_generalCellLinearSpace_eq_fuksComplexity_add {d m : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellOpenDomain a) :
    Module.finrank ℝ (generalCellLinearSpace a) =
      fuksComplexity (generalCellConfigurationMap a x) + (m+1) := by
  rw [finrank_generalCellLinearSpace_sum, fuksComplexity_generalCell]
  have hs : (∑ i : Fin m, (d+1 - (a i).val)) =
      (∑ i : Fin m, (d - (a i).val)) + m := by
    have he (i : Fin m) : d+1 - (a i).val = (d - (a i).val) + 1 := by
      have hi := (a i).isLt
      omega
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  rw [hs]
  omega

/-- Membership of a word-chart configuration in any level of the existing
closed filtration is exactly the corresponding dimension inequality. -/
theorem generalCellConfigurationMap_mem_fuksLevel_iff {d m k : ℕ}
    (a : Fin m → Fin (d+1)) (x : generalCellOpenDomain a) :
    generalCellConfigurationMap a x ∈ fuksLevel d (m+1) k ↔
      Module.finrank ℝ (generalCellLinearSpace a) ≤ k + (m+1) := by
  rw [mem_fuksLevel_iff_complexity, finrank_generalCellLinearSpace_eq_fuksComplexity_add a x]
  omega

end NRR.PrimePowerTopology
