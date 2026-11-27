import NRR.SingularHomologyBMSuspensionProper
import NRR.PrimePowerTopologyInfinityNeighborhood
import NRR.PrimePowerTopologyEuclideanInfinityNeighborhood
import NRR.Coordinates

/-! Iteration of real BM suspension along the genuine Euclidean
coordinates. All maps are induced by proper maps on the actual point-relative
singular homology model. The generic construction isolates the single-step
geometric input and proves its proper-map naturality at every stabilization. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePowerTopology

namespace NRR.SingularHomology

variable (R : Type) [Ring R]
variable {X Y Z W : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

@[simp] theorem HbmMap_id (q : ℕ) :
    HbmMap R q (id : X → X) isProperMap_id = 𝟙 _ := by
  unfold HbmMap
  simp only [properOnePointMap_id, HrelMap_id]

theorem HbmMap_comp (q : ℕ) (f : X → Y) (hf : IsProperMap f)
    (g : Y → Z) (hg : IsProperMap g) :
    HbmMap R q f hf ≫ HbmMap R q g hg = HbmMap R q (g ∘ f) (hg.comp hf) := by
  unfold HbmMap
  rw [HrelMap_comp]
  congr 1
  exact properOnePointMap_comp f hf g hg

/-- Transport by the actual proper extension of a homeomorphism. -/
def HbmIsoOfHomeomorph (q : ℕ) (e : X ≃ₜ Y) : Hbm R q X ≅ Hbm R q Y where
  hom := HbmMap R q e e.isProperMap
  inv := HbmMap R q e.symm e.symm.isProperMap
  hom_inv_id := by
    rw [HbmMap_comp]
    have he : (e.symm ∘ e : X → X) = id := funext e.symm_apply_apply
    simp only [he, HbmMap_id]
  inv_hom_id := by
    rw [HbmMap_comp]
    have he : (e ∘ e.symm : Y → Y) = id := funext e.apply_symm_apply
    simp only [he, HbmMap_id]

@[simp] theorem HbmIsoOfHomeomorph_hom (q : ℕ) (e : X ≃ₜ Y) :
    (HbmIsoOfHomeomorph R q e).hom = HbmMap R q e e.isProperMap := rfl

/-- Commuting proper maps induce a commuting square under Euclidean
coordinate changes, also in degree zero. -/
@[reassoc]
theorem HbmIsoOfHomeomorph_naturality (q : ℕ) (e : X ≃ₜ W) (e' : Y ≃ₜ Z)
    (f : X → Y) (hf : IsProperMap f) (g : W → Z) (hg : IsProperMap g)
    (h : e' ∘ f = g ∘ e) :
    (HbmIsoOfHomeomorph R q e).hom ≫ HbmMap R q g hg =
      HbmMap R q f hf ≫ (HbmIsoOfHomeomorph R q e').hom := by
  simp only [HbmIsoOfHomeomorph_hom, HbmMap_comp]
  congr 1
  exact h.symm

/-- The canonical absolute/point-relative comparison with the positive
degree written directly, avoiding a predecessor in downstream statements. -/
def positiveHbmComparisonIso (q : ℕ) (hq : 0 < q) (X : Type) [TopologicalSpace X] :
    Habs R q (TopCat.of (OnePoint X)) ≅ Hbm R q X := by
  cases q with
  | zero => omega
  | succ q => exact pointRelativePositiveIso R q (X := TopCat.of (OnePoint X)) (∞ : OnePoint X)

@[reassoc]
theorem positiveHbmComparisonIso_naturality (q : ℕ) (hq : 0 < q)
    (f : X → Y) (hf : IsProperMap f) :
    (positiveHbmComparisonIso R q hq X).hom ≫ HbmMap R q f hf =
      HabsMap R q (properOnePointMap f hf) ≫ (positiveHbmComparisonIso R q hq Y).hom := by
  cases q with
  | zero => omega
  | succ q => exact pointRelativePositiveIso_proper_naturality R q f hf

end NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The zero-dimensional Euclidean factor is removed by its actual
projection homeomorphism. -/
def spaceProductZeroHomeomorph (X : Type) [TopologicalSpace X] :
    X × Space 0 ≃ₜ X where
  toFun := Prod.fst
  invFun x := (x,0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

/-- Split off the last real coordinate, using the specified
horizontal-height coordinates and the actual product associator. -/
def spaceProductSuccHomeomorph (X : Type) [TopologicalSpace X] (r : ℕ) :
    X × Space (r+1) ≃ₜ (X × Space r) × ℝ :=
  ((Homeomorph.refl X).prodCongr (Coordinates.horizontalHeight r).toHomeomorph).trans
    (Homeomorph.prodAssoc X (Space r) ℝ).symm

@[simp] theorem spaceProductSuccHomeomorph_apply (r : ℕ) (x : X) (v : Space (r+1)) :
    spaceProductSuccHomeomorph X r (x,v) =
      ((x,(Coordinates.horizontalHeight r v).1),(Coordinates.horizontalHeight r v).2) := rfl

/-- The real single-step isomorphisms needed to iterate over `Space r`.
This parameter is replaced by the geometric single-step construction below. -/
abbrev BMRealSuspensionSteps (R : Type) [Ring R] (X : Type) [TopologicalSpace X] :=
  ∀ (r q : ℕ) (_hq : 0 < q),
    (NRR.SingularHomology.Hbm R (q+1) ((X × Space r) × ℝ) ≅
      NRR.SingularHomology.Hbm R q (X × Space r))

open NRR.SingularHomology
variable (R : Type) [Ring R]

/-- The naturality hypothesis for a sequence of real suspension steps.
The maps on both sides are precisely the product extensions of `f`. -/
def BMRealSuspensionSteps.Naturality (S : BMRealSuspensionSteps R X)
    (T : BMRealSuspensionSteps R Y) (f : X → Y) (hf : IsProperMap f) : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k),
    (S r k hk).hom ≫ HbmMap R k (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) =
      HbmMap R (k+1) (Prod.map (Prod.map f (id : Space r → Space r)) (id : ℝ → ℝ))
        ((hf.prodMap isProperMap_id).prodMap isProperMap_id) ≫ (T r k hk).hom

/-- Iterate the actual real suspension in the chosen Euclidean coordinate
order. The target degree is positive, so every intermediate degree is positive. -/
def bmSpaceSuspensionIsoOfSteps (S : BMRealSuspensionSteps R X)
    (q : ℕ) (hq : 0 < q) :
    (r : ℕ) → Hbm R (q+r) (X × Space r) ≅ Hbm R q X
  | 0 => HbmIsoOfHomeomorph R q (spaceProductZeroHomeomorph X)
  | r+1 => HbmIsoOfHomeomorph R (q+(r+1)) (spaceProductSuccHomeomorph X r) ≪≫
      S r (q+r) (by omega) ≪≫ bmSpaceSuspensionIsoOfSteps S q hq r

/-- The full naturality square for `f × id_Space r`, given the corresponding
single-step squares. No condition such as injectivity is placed on `f`. -/
@[reassoc]
theorem bmSpaceSuspensionIsoOfSteps_naturality
    (S : BMRealSuspensionSteps R X) (T : BMRealSuspensionSteps R Y)
    (f : X → Y) (hf : IsProperMap f)
    (hstep : S.Naturality R T f hf)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (bmSpaceSuspensionIsoOfSteps R S q hq r).hom ≫ HbmMap R q f hf =
      HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) ≫ (bmSpaceSuspensionIsoOfSteps R T q hq r).hom := by
  induction r with
  | zero =>
    exact HbmIsoOfHomeomorph_naturality R q (spaceProductZeroHomeomorph X)
      (spaceProductZeroHomeomorph Y) _ (hf.prodMap isProperMap_id) f hf rfl
  | succ r ih =>
    simp only [bmSpaceSuspensionIsoOfSteps, Iso.trans_hom, Category.assoc]
    rw [ih, ← Category.assoc (S r (q+r) (by omega)).hom, hstep r (q+r) (by omega)]
    have he := HbmIsoOfHomeomorph_naturality R (q+(r+1)) (spaceProductSuccHomeomorph X r)
      (spaceProductSuccHomeomorph Y r)
      (Prod.map f (id : Space (r+1) → Space (r+1))) (hf.prodMap isProperMap_id)
      (Prod.map (Prod.map f (id : Space r → Space r)) (id : ℝ → ℝ))
      ((hf.prodMap isProperMap_id).prodMap isProperMap_id) rfl
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ (T r (q+r) (by omega)).hom ≫
        (bmSpaceSuspensionIsoOfSteps R T q hq r).hom) he

/-- The same dimension descent on absolute positive singular homology of
the genuine compactifications, via the canonical point-relative comparison. -/
def bmAbsoluteSpaceSuspensionIsoOfSteps (S : BMRealSuspensionSteps R X)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Habs R (q+r) (TopCat.of (OnePoint (X × Space r))) ≅
      Habs R q (TopCat.of (OnePoint X)) :=
  positiveHbmComparisonIso R (q+r) (by omega) (X × Space r) ≪≫
    bmSpaceSuspensionIsoOfSteps R S q hq r ≪≫ (positiveHbmComparisonIso R q hq X).symm

@[reassoc]
theorem bmAbsoluteSpaceSuspensionIsoOfSteps_naturality
    (S : BMRealSuspensionSteps R X) (T : BMRealSuspensionSteps R Y)
    (f : X → Y) (hf : IsProperMap f) (hstep : S.Naturality R T f hf)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    (bmAbsoluteSpaceSuspensionIsoOfSteps R S q hq r).hom ≫
        HabsMap R q (properOnePointMap f hf) =
      HabsMap R (q+r)
        (properOnePointMap (Prod.map f (id : Space r → Space r))
          (hf.prodMap isProperMap_id)) ≫
        (bmAbsoluteSpaceSuspensionIsoOfSteps R T q hq r).hom := by
  apply (cancel_mono (positiveHbmComparisonIso R q hq Y).hom).mp
  simp only [bmAbsoluteSpaceSuspensionIsoOfSteps, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← positiveHbmComparisonIso_naturality R q hq f hf,
    Iso.inv_hom_id_assoc, bmSpaceSuspensionIsoOfSteps_naturality R S T f hf hstep]
  rw [← Category.assoc, positiveHbmComparisonIso_naturality]
  simp only [Category.assoc]

/-- Suspension preserves and reflects vanishing of the actual proper-map
action. This applies in particular to closed-stratum inclusions. -/
theorem bmSpaceSuspensionMap_zero_iffOfSteps
    (S : BMRealSuspensionSteps R X) (T : BMRealSuspensionSteps R Y)
    (f : X → Y) (hf : IsProperMap f) (hstep : S.Naturality R T f hf)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) = 0 ↔ HbmMap R q f hf = 0 := by
  have h := bmSpaceSuspensionIsoOfSteps_naturality R S T f hf hstep q hq r
  constructor
  · intro hz
    apply (cancel_epi (bmSpaceSuspensionIsoOfSteps R S q hq r).hom).mp
    rw [h,hz,zero_comp,comp_zero]
  · intro hz
    apply (cancel_mono (bmSpaceSuspensionIsoOfSteps R T q hq r).hom).mp
    rw [← h,hz,comp_zero,zero_comp]

/-- Euclidean stabilization preserves and reflects injectivity of any
proper-map action in positive target degree. -/
theorem bmSpaceSuspensionMap_mono_iffOfSteps
    (S : BMRealSuspensionSteps R X) (T : BMRealSuspensionSteps R Y)
    (f : X → Y) (hf : IsProperMap f) (hstep : S.Naturality R T f hf)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Mono (HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id)) ↔ Mono (HbmMap R q f hf) := by
  have h := bmSpaceSuspensionIsoOfSteps_naturality R S T f hf hstep q hq r
  rw [← mono_comp_iff_of_mono _ (bmSpaceSuspensionIsoOfSteps R T q hq r).hom,
    ← h, mono_comp_iff_of_isIso]

/-- Euclidean stabilization preserves and reflects surjectivity as well. -/
theorem bmSpaceSuspensionMap_epi_iffOfSteps
    (S : BMRealSuspensionSteps R X) (T : BMRealSuspensionSteps R Y)
    (f : X → Y) (hf : IsProperMap f) (hstep : S.Naturality R T f hf)
    (q : ℕ) (hq : 0 < q) (r : ℕ) :
    Epi (HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id)) ↔ Epi (HbmMap R q f hf) := by
  have h := bmSpaceSuspensionIsoOfSteps_naturality R S T f hf hstep q hq r
  rw [← epi_comp_iff_of_isIso _ (bmSpaceSuspensionIsoOfSteps R T q hq r).hom,
    ← h, epi_comp_iff_of_epi]

/-- A specified class has nonzero image under a stabilized proper map
exactly when its dimension-descended class does. -/
theorem bmSpaceSuspensionMap_class_ne_zero_iffOfSteps
    (S : BMRealSuspensionSteps R X) (T : BMRealSuspensionSteps R Y)
    (f : X → Y) (hf : IsProperMap f) (hstep : S.Naturality R T f hf)
    (q : ℕ) (hq : 0 < q) (r : ℕ) (z : Hbm R (q+r) (X × Space r)) :
    HbmMap R (q+r) (Prod.map f (id : Space r → Space r))
        (hf.prodMap isProperMap_id) z ≠ 0 ↔
      HbmMap R q f hf ((bmSpaceSuspensionIsoOfSteps R S q hq r).hom z) ≠ 0 := by
  have h := congrArg (fun k => k z)
    (bmSpaceSuspensionIsoOfSteps_naturality R S T f hf hstep q hq r)
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  have hi := (ModuleCat.mono_iff_injective
    (bmSpaceSuspensionIsoOfSteps R T q hq r).hom).mp inferInstance
  exact (map_ne_zero_iff _ hi).symm

end NRR.PrimePowerTopology
