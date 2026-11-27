import NRR.PrimePowerExistenceConfiguration
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homotopy.Basic
import NRR.SingularHomologyRelMap
import NRR.TopologyPort.SingularPrism

/-!
The actual orbit space and associated representation space for the configuration
space action.  All maps below descend from the diagonal permutation action;
no Euler-class or configuration-space obstruction is assumed here.
-/

noncomputable section
open Set Topology
open NRR.PrimePower

namespace NRR.PrimePowerTopology

abbrev ConfigurationGroup (n : ℕ) := Equiv.Perm (Fin n)

instance configurationContinuousConstSMul {d n : ℕ} :
    ContinuousConstSMul (ConfigurationGroup n) (Configuration d n) where
  continuous_const_smul σ := (relabelConfiguration σ).continuous

instance valuesContinuousConstSMul {d n : ℕ} :
    ContinuousConstSMul (ConfigurationGroup n) (ReducedValues d n) where
  continuous_const_smul σ := (relabelValues σ).continuous

@[simp] theorem values_smul_zero {d n : ℕ} (σ : ConfigurationGroup n) :
    σ • (0 : ReducedValues d n) = 0 := (relabelValues σ).map_zero

@[simp] theorem values_smul_real_smul {d n : ℕ} (σ : ConfigurationGroup n)
    (a : ℝ) (v : ReducedValues d n) :
    σ • (a • v) = a • (σ • v) := (relabelValues σ).map_smul a v

/-- Unordered configurations with the genuine quotient topology. -/
abbrev ConfigurationBase (d n : ℕ) :=
  Quotient (MulAction.orbitRel (ConfigurationGroup n) (Configuration d n))

/-- The associated space for the diagonal action, with the quotient topology. -/
abbrev ConfigurationAssociated (d n : ℕ) :=
  Quotient (MulAction.orbitRel (ConfigurationGroup n)
    (Configuration d n × ReducedValues d n))

def configurationQuotient {d n : ℕ} : C(Configuration d n, ConfigurationBase d n) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

def associatedQuotient {d n : ℕ} :
    C(Configuration d n × ReducedValues d n, ConfigurationAssociated d n) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

@[simp] theorem configurationQuotient_smul {d n : ℕ} (σ : ConfigurationGroup n)
    (x : Configuration d n) :
    configurationQuotient (σ • x) = configurationQuotient x :=
  Quotient.sound ⟨σ, rfl⟩

@[simp] theorem associatedQuotient_smul {d n : ℕ} (σ : ConfigurationGroup n)
    (p : Configuration d n × ReducedValues d n) :
    associatedQuotient (σ • p) = associatedQuotient p :=
  Quotient.sound ⟨σ, rfl⟩

/-- Projection of the associated quotient to the orbit space. -/
def associatedProjection {d n : ℕ} :
    C(ConfigurationAssociated d n, ConfigurationBase d n) where
  toFun := Quotient.lift (fun p => configurationQuotient p.1) (by
    rintro a b ⟨σ, rfl⟩
    exact configurationQuotient_smul σ b.1)
  continuous_toFun :=
    (configurationQuotient.continuous.comp continuous_fst).quotient_lift _

@[simp] theorem associatedProjection_mk {d n : ℕ}
    (x : Configuration d n) (v : ReducedValues d n) :
    associatedProjection (associatedQuotient (x,v)) = configurationQuotient x := rfl

/-- The zero section is a continuous map on the actual quotient. -/
def associatedZeroSection {d n : ℕ} :
    C(ConfigurationBase d n, ConfigurationAssociated d n) where
  toFun := Quotient.lift (fun x => associatedQuotient (x,0)) (by
    rintro a b ⟨σ, rfl⟩
    simpa only [Prod.smul_mk, values_smul_zero] using
      associatedQuotient_smul σ (b,(0 : ReducedValues d n)))
  continuous_toFun :=
    (associatedQuotient.continuous.comp (continuous_id.prodMk continuous_const)).quotient_lift _

@[simp] theorem associatedZeroSection_mk {d n : ℕ} (x : Configuration d n) :
    associatedZeroSection (configurationQuotient x) = associatedQuotient (x,0) := rfl

@[simp] theorem associatedProjection_zeroSection {d n : ℕ} (q : ConfigurationBase d n) :
    associatedProjection (associatedZeroSection q) = q := by
  induction q using Quotient.inductionOn with | h x => rfl

/-- A continuous equivariant map determines a genuine section of the associated quotient. -/
def associatedSection {d n : ℕ} (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    C(ConfigurationBase d n, ConfigurationAssociated d n) where
  toFun := Quotient.lift (fun x => associatedQuotient (x,f x)) (by
    rintro a b ⟨σ, rfl⟩
    simpa only [Prod.smul_mk, he] using associatedQuotient_smul σ (b,f b))
  continuous_toFun :=
    (associatedQuotient.continuous.comp (continuous_id.prodMk f.continuous)).quotient_lift _

@[simp] theorem associatedSection_mk {d n : ℕ}
    (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (x : Configuration d n) :
    associatedSection f he (configurationQuotient x) = associatedQuotient (x,f x) := rfl

@[simp] theorem associatedProjection_section {d n : ℕ}
    (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (q : ConfigurationBase d n) :
    associatedProjection (associatedSection f he q) = q := by
  induction q using Quotient.inductionOn with | h x => rfl

/-- Fiberwise scalar multiplication, descended from the linear representation. -/
def associatedScale {d n : ℕ} (a : ℝ) :
    ConfigurationAssociated d n → ConfigurationAssociated d n :=
  Quotient.lift (fun p => associatedQuotient (p.1,a • p.2)) (by
    rintro p q ⟨σ, rfl⟩
    simpa only [Prod.smul_mk, values_smul_real_smul] using
      associatedQuotient_smul σ (q.1,a • q.2))

@[simp] theorem associatedScale_mk {d n : ℕ} (a : ℝ)
    (x : Configuration d n) (v : ReducedValues d n) :
    associatedScale a (associatedQuotient (x,v)) = associatedQuotient (x,a • v) := rfl

/-- Joint continuity uses the open quotient map, so includes the scalar parameter. -/
theorem continuous_associatedScale {d n : ℕ} :
    Continuous (fun p : ℝ × ConfigurationAssociated d n => associatedScale p.1 p.2) := by
  apply (IsOpenQuotientMap.id.prodMap
    (MulAction.isOpenQuotientMap_quotientMk (Γ := ConfigurationGroup n)
      (T := Configuration d n × ReducedValues d n))).continuous_comp_iff.mp
  change Continuous (fun p : ℝ × (Configuration d n × ReducedValues d n) =>
    associatedQuotient (p.2.1,p.1 • p.2.2))
  exact associatedQuotient.continuous.comp
    (continuous_snd.fst.prodMk (continuous_fst.smul continuous_snd.snd))

@[simp] theorem associatedScale_one {d n : ℕ} (z : ConfigurationAssociated d n) :
    associatedScale 1 z = z := by
  induction z using Quotient.inductionOn with
  | h p => rcases p with ⟨x,v⟩; change associatedQuotient (x,(1 : ℝ) • v) = associatedQuotient (x,v); rw [one_smul]

@[simp] theorem associatedScale_zero {d n : ℕ} (z : ConfigurationAssociated d n) :
    associatedScale 0 z = associatedZeroSection (associatedProjection z) := by
  induction z using Quotient.inductionOn with
  | h p => rcases p with ⟨x,v⟩; change associatedQuotient (x,(0 : ℝ) • v) = associatedQuotient (x,0); rw [zero_smul]

@[simp] theorem associatedProjection_scale {d n : ℕ} (a : ℝ)
    (z : ConfigurationAssociated d n) :
    associatedProjection (associatedScale a z) = associatedProjection z := by
  induction z using Quotient.inductionOn with | h p => rfl

@[simp] theorem associatedScale_zeroSection {d n : ℕ} (a : ℝ)
    (q : ConfigurationBase d n) :
    associatedScale a (associatedZeroSection q) = associatedZeroSection q := by
  induction q using Quotient.inductionOn with
  | h x => change associatedQuotient (x,a • (0 : ReducedValues d n)) = associatedQuotient (x,0); rw [smul_zero]

/-- The associated space deforms continuously to its zero section, fiber by fiber. -/
def associatedContraction {d n : ℕ} :
    ContinuousMap.Homotopy (ContinuousMap.id (ConfigurationAssociated d n))
      (associatedZeroSection.comp associatedProjection) where
  toFun p := associatedScale (1-(p.1 : ℝ)) p.2
  continuous_toFun := continuous_associatedScale.comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  map_zero_left z := by simp
  map_one_left z := by simp

@[simp] theorem associatedContraction_projection {d n : ℕ}
    (t : unitInterval) (z : ConfigurationAssociated d n) :
    associatedProjection (associatedContraction (t,z)) = associatedProjection z :=
  associatedProjection_scale _ _

@[simp] theorem associatedContraction_zeroSection {d n : ℕ}
    (t : unitInterval) (q : ConfigurationBase d n) :
    associatedContraction (t,associatedZeroSection q) = associatedZeroSection q :=
  associatedScale_zeroSection _ _

/-- Every induced section has a continuous homotopy through sections to zero. -/
def associatedSectionHomotopy {d n : ℕ}
    (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    ContinuousMap.Homotopy (associatedSection f he) associatedZeroSection where
  toFun p := associatedScale (1-(p.1 : ℝ)) (associatedSection f he p.2)
  continuous_toFun := continuous_associatedScale.comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
      ((associatedSection f he).continuous.comp continuous_snd))
  map_zero_left q := by simp
  map_one_left q := by simp

@[simp] theorem associatedSectionHomotopy_projection {d n : ℕ}
    (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (t : unitInterval) (q : ConfigurationBase d n) :
    associatedProjection (associatedSectionHomotopy f he (t,q)) = q := by
  exact (associatedProjection_scale _ _).trans (associatedProjection_section f he q)

/-- The geometric zero set in the associated quotient. -/
def associatedZeroLocus (d n : ℕ) : Set (ConfigurationAssociated d n) :=
  Set.range associatedZeroSection

/-- Vanishing in the quotient is exactly vanishing of the original vector. -/
theorem associatedQuotient_eq_zero_iff {d n : ℕ}
    (x : Configuration d n) (v : ReducedValues d n) :
    associatedQuotient (x,v) = associatedZeroSection (configurationQuotient x) ↔ v = 0 := by
  constructor
  · intro h
    obtain ⟨σ,hσ⟩ := Quotient.exact h
    have hv := congrArg Prod.snd hσ
    change σ • (0 : ReducedValues d n) = v at hv
    simpa only [values_smul_zero] using hv.symm
  · rintro rfl
    rfl

theorem associatedQuotient_mem_zeroLocus_iff {d n : ℕ}
    (x : Configuration d n) (v : ReducedValues d n) :
    associatedQuotient (x,v) ∈ associatedZeroLocus d n ↔ v = 0 := by
  constructor
  · rintro ⟨q,hq⟩
    have hb := congrArg associatedProjection hq
    simp only [associatedProjection_zeroSection,associatedProjection_mk] at hb
    exact (associatedQuotient_eq_zero_iff x v).mp (by rw [← hb]; exact hq.symm)
  · intro hv
    exact ⟨configurationQuotient x,(associatedQuotient_eq_zero_iff x v).mpr hv |>.symm⟩

/-- A zero-free equivariant map gives a section missing the actual zero locus. -/
theorem associatedSection_avoids_zeroLocus {d n : ℕ}
    (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) (q : ConfigurationBase d n) :
    associatedSection f he q ∉ associatedZeroLocus d n := by
  induction q using Quotient.inductionOn with
  | h x => exact fun h => hnz x ((associatedQuotient_mem_zeroLocus_iff x (f x)).mp h)

/-- The induced map to the complement is continuous, giving the pair-map input. -/
def associatedNonzeroSection {d n : ℕ}
    (f : C(Configuration d n, ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) :
    C(ConfigurationBase d n,{z : ConfigurationAssociated d n // z ∉ associatedZeroLocus d n}) :=
  ⟨fun q => ⟨associatedSection f he q,associatedSection_avoids_zeroLocus f he hnz q⟩,
    (associatedSection f he).continuous.subtype_mk _⟩


/-- The permutation action is isometric for the actual configuration metric. -/
theorem configuration_smul_dist {d n : ℕ} (σ : ConfigurationGroup n)
    (x y : Configuration d n) : dist (σ • x) (σ • y) = dist x y := by
  have bound (τ : ConfigurationGroup n) (a b : Configuration d n) :
      dist (τ • a) (τ • b) ≤ dist a b := by
    change dist (fun i => a.val (τ.symm i)) (fun i => b.val (τ.symm i)) ≤ dist a.val b.val
    exact (dist_pi_le_iff dist_nonneg).mpr fun i => dist_le_pi_dist a.val b.val (τ.symm i)
  apply le_antisymm (bound σ x y)
  simpa only [inv_smul_smul] using bound σ⁻¹ (σ • x) (σ • y)

/-- An open slice can meet any one orbit in at most one point. -/
def IsConfigurationSlice {d n : ℕ} (U : Set (Configuration d n)) : Prop :=
  ∀ (σ : ConfigurationGroup n) (y : Configuration d n), y ∈ U → σ • y ∈ U → σ = 1

/-- An explicit finite intersection of strict metric inequalities around x. -/
def configurationSlice {d n : ℕ} (x : Configuration d n) : Set (Configuration d n) :=
  {y | ∀ (σ : ConfigurationGroup n), σ ≠ 1 → dist x y < dist x (σ • y)}

theorem isOpen_configurationSlice {d n : ℕ} (x : Configuration d n) :
    IsOpen (configurationSlice x) := by
  change IsOpen {y | ∀ (σ : ConfigurationGroup n), σ ≠ 1 → dist x y < dist x (σ • y)}
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro σ
  by_cases hσ : σ = 1
  · simp [hσ]
  · simpa [hσ] using isOpen_lt (continuous_const.dist continuous_id)
      (continuous_const.dist (continuous_const_smul σ))

theorem self_mem_configurationSlice {d n : ℕ} (x : Configuration d n) :
    x ∈ configurationSlice x := by
  intro σ hσ
  rw [dist_self]
  apply dist_pos.mpr
  intro h
  exact hσ (configuration_action_free σ x h.symm)

theorem configurationSlice_isSlice {d n : ℕ} (x : Configuration d n) :
    IsConfigurationSlice (configurationSlice x) := by
  intro σ y hy hσy
  by_contra hσ
  have h₁ := hy σ hσ
  have h₂ := hσy σ⁻¹ (inv_ne_one.mpr hσ)
  simp only [inv_smul_smul] at h₂
  exact (lt_asymm h₁ h₂)

theorem IsConfigurationSlice.mono {d n : ℕ} {U V : Set (Configuration d n)}
    (hU : IsConfigurationSlice U) (hVU : V ⊆ U) : IsConfigurationSlice V :=
  fun σ y hy hσy => hU σ y (hVU hy) (hVU hσy)

/-- Each configuration has a positive-radius ball whose nontrivial translates
are disjoint.  The radius is obtained inside the explicit open metric slice. -/
theorem exists_configuration_ball_slice {d n : ℕ} (x : Configuration d n) :
    ∃ ε : ℝ, 0 < ε ∧ IsConfigurationSlice (Metric.ball x ε) := by
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp (isOpen_configurationSlice x) x
    (self_mem_configurationSlice x)
  exact ⟨ε,hε,(configurationSlice_isSlice x).mono hsub⟩

theorem IsConfigurationSlice.disjoint_translate {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsConfigurationSlice U)
    (σ : ConfigurationGroup n) (hσ : σ ≠ 1) :
    Disjoint U ((fun y => σ • y) '' U) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨y,hy,rfl⟩
  exact hσ (hU σ y hy hz)

def configurationSliceImage {d n : ℕ} (U : Set (Configuration d n)) :
    Set (ConfigurationBase d n) := configurationQuotient '' U

theorem isOpen_configurationSliceImage {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) :
    IsOpen (configurationSliceImage U) :=
  (MulAction.isOpenQuotientMap_quotientMk (Γ := ConfigurationGroup n)
    (T := Configuration d n)).isOpenMap U hU

def configurationSliceBaseMap {d n : ℕ} (U : Set (Configuration d n)) :
    U → configurationSliceImage U :=
  fun x => ⟨configurationQuotient x.val,⟨x.val,x.property,rfl⟩⟩

theorem configurationSliceBaseMap_bijective {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsConfigurationSlice U) :
    Function.Bijective (configurationSliceBaseMap U) := by
  constructor
  · intro a b hab
    obtain ⟨σ,hσ⟩ := Quotient.exact (congrArg Subtype.val hab)
    change σ • b.val = a.val at hσ
    have hσU : σ • b.val ∈ U := by rw [hσ]; exact a.property
    have hs := hU σ b.val b.property hσU
    apply Subtype.ext
    simpa only [hs,one_smul] using hσ.symm
  · rintro ⟨q,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩

/-- The quotient map restricted to an open slice is a homeomorphism onto an
open neighborhood in the unordered configuration space. -/
def configurationSliceBaseHomeomorph {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U) :
    U ≃ₜ configurationSliceImage U :=
  (Equiv.ofBijective (configurationSliceBaseMap U)
    (configurationSliceBaseMap_bijective hS)).toHomeomorphOfContinuousOpen
      ((configurationQuotient.continuous.comp continuous_subtype_val).subtype_mk _)
      (((MulAction.isOpenQuotientMap_quotientMk (Γ := ConfigurationGroup n)
        (T := Configuration d n)).isOpenMap.comp hU.isOpenMap_subtype_val).subtype_mk _)

/-- The portion of the associated space over the image of a slice. -/
abbrev ConfigurationAssociatedOver {d n : ℕ} (U : Set (Configuration d n)) :=
  {z : ConfigurationAssociated d n // associatedProjection z ∈ configurationSliceImage U}

def associatedSliceMap {d n : ℕ} (U : Set (Configuration d n)) :
    U × ReducedValues d n → ConfigurationAssociatedOver U :=
  fun p => ⟨associatedQuotient (p.1.val,p.2),⟨p.1.val,p.1.property,rfl⟩⟩

theorem associatedSliceMap_bijective {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsConfigurationSlice U) :
    Function.Bijective (associatedSliceMap U) := by
  constructor
  · rintro ⟨a,v⟩ ⟨b,w⟩ hab
    obtain ⟨σ,hσ⟩ := Quotient.exact (congrArg Subtype.val hab)
    have hx := congrArg Prod.fst hσ
    have hv := congrArg Prod.snd hσ
    change σ • b.val = a.val at hx
    change σ • w = v at hv
    have hs : σ = 1 := hU σ b.val b.property (by rw [hx]; exact a.property)
    apply Prod.ext
    · apply Subtype.ext
      simpa only [hs,one_smul] using hx.symm
    · simpa only [hs,one_smul] using hv.symm
  · intro z
    rcases z with ⟨z,hz⟩
    induction z using Quotient.inductionOn with
    | h p =>
      rcases p with ⟨x,v⟩
      obtain ⟨y,hy,heq⟩ := hz
      obtain ⟨σ,hσ⟩ := Quotient.exact heq
      change σ • x = y at hσ
      have hy' : σ • x ∈ U := by rw [hσ]; exact hy
      refine ⟨(⟨σ • x,hy'⟩,σ • v),?_⟩
      apply Subtype.ext
      exact associatedQuotient_smul σ (x,v)

/-- A genuine local product homeomorphism, obtained from the diagonal quotient.
Its domain is a slice times the representation and its target is the entire
preimage of the corresponding open base neighborhood. -/
def associatedSliceHomeomorph {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U) :
    U × ReducedValues d n ≃ₜ ConfigurationAssociatedOver U :=
  (Equiv.ofBijective (associatedSliceMap U) (associatedSliceMap_bijective hS)).toHomeomorphOfContinuousOpen
      ((associatedQuotient.continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _)
      (((MulAction.isOpenQuotientMap_quotientMk (Γ := ConfigurationGroup n)
        (T := Configuration d n × ReducedValues d n)).isOpenMap.comp
        (hU.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk _)

/-- Trivialization with the usual base-neighborhood-times-fiber codomain. -/
def associatedLocalTrivialization {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U) :
    ConfigurationAssociatedOver U ≃ₜ configurationSliceImage U × ReducedValues d n :=
  (associatedSliceHomeomorph hU hS).symm.trans
    ((configurationSliceBaseHomeomorph hU hS).prodCongr (Homeomorph.refl _))

@[simp] theorem associatedSliceHomeomorph_apply {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U)
    (p : U × ReducedValues d n) :
    associatedSliceHomeomorph hU hS p = associatedSliceMap U p := rfl

@[simp] theorem configurationSliceBaseHomeomorph_apply {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U)
    (x : U) : configurationSliceBaseHomeomorph hU hS x = configurationSliceBaseMap U x := rfl

@[simp] theorem associatedLocalTrivialization_mk {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U)
    (p : U × ReducedValues d n) :
    associatedLocalTrivialization hU hS (associatedSliceMap U p) =
      (configurationSliceBaseMap U p.1,p.2) := by
  change ((configurationSliceBaseHomeomorph hU hS).prodCongr (Homeomorph.refl _))
    ((associatedSliceHomeomorph hU hS).symm (associatedSliceHomeomorph hU hS p)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The local product homeomorphism is over the base, rather than just an
unrelated homeomorphism of spaces. -/
theorem associatedLocalTrivialization_projection {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U)
    (z : ConfigurationAssociatedOver U) :
    (associatedLocalTrivialization hU hS z).1.val = associatedProjection z.val := by
  have h := congrArg (fun w : ConfigurationAssociatedOver U => associatedProjection w.val)
    ((associatedSliceHomeomorph hU hS).apply_symm_apply z)
  exact h

/-- In every local product chart the geometric zero locus is exactly the
zero vector in each fiber. -/
theorem associatedLocalTrivialization_zero_iff {d n : ℕ}
    {U : Set (Configuration d n)} (hU : IsOpen U) (hS : IsConfigurationSlice U)
    (z : ConfigurationAssociatedOver U) :
    z.val ∈ associatedZeroLocus d n ↔ (associatedLocalTrivialization hU hS z).2 = 0 := by
  let p := (associatedSliceHomeomorph hU hS).symm z
  have hp : associatedSliceMap U p = z :=
    (associatedSliceHomeomorph hU hS).apply_symm_apply z
  rw [← hp,associatedLocalTrivialization_mk]
  exact associatedQuotient_mem_zeroLocus_iff p.1.val p.2

/-- The actual associated projection is locally a product with the reduced
representation, over an open neighborhood of every unordered configuration. -/
theorem associatedProjection_locally_trivial {d n : ℕ} (q : ConfigurationBase d n) :
    ∃ U : Set (ConfigurationBase d n), q ∈ U ∧ IsOpen U ∧
      ∃ H : (associatedProjection ⁻¹' U) ≃ₜ U × ReducedValues d n,
        ∀ z, (H z).1.val = associatedProjection z.val := by
  induction q using Quotient.inductionOn with
  | h x =>
    refine ⟨configurationSliceImage (configurationSlice x),
      ⟨x,self_mem_configurationSlice x,rfl⟩,
      isOpen_configurationSliceImage (isOpen_configurationSlice x),
      associatedLocalTrivialization (isOpen_configurationSlice x)
        (configurationSlice_isSlice x),?_⟩
    exact associatedLocalTrivialization_projection (isOpen_configurationSlice x)
      (configurationSlice_isSlice x)

/-- A vector space fiber maps continuously into the associated quotient. -/
def associatedFiberMap {d n : ℕ} (x : Configuration d n) :
    C(ReducedValues d n,ConfigurationAssociated d n) :=
  associatedQuotient.comp ⟨fun v => (x,v),continuous_const.prodMk continuous_id⟩

@[simp] theorem associatedFiberMap_apply {d n : ℕ}
    (x : Configuration d n) (v : ReducedValues d n) :
    associatedFiberMap x v = associatedQuotient (x,v) := rfl

/-- Freeness of the configuration action makes each displayed fiber map injective. -/
theorem associatedFiberMap_injective {d n : ℕ} (x : Configuration d n) :
    Function.Injective (associatedFiberMap x) := by
  intro v w h
  obtain ⟨σ,hσ⟩ := Quotient.exact h
  have hx := congrArg Prod.fst hσ
  have hv := congrArg Prod.snd hσ
  change σ • x = x at hx
  change σ • w = v at hv
  simpa only [configuration_action_free σ x hx,one_smul] using hv.symm

/-- Continuous map of the nonzero subspaces used by relative singular homology. -/
def associatedFiberNonzeroMap {d n : ℕ} (x : Configuration d n) :
    C({v : ReducedValues d n // v ≠ 0},
      {z : ConfigurationAssociated d n // z ∉ associatedZeroLocus d n}) :=
  ⟨fun v => ⟨associatedFiberMap x v.val,fun h =>
      v.property ((associatedQuotient_mem_zeroLocus_iff x v.val).mp h)⟩,
    ((associatedFiberMap x).continuous.comp continuous_subtype_val).subtype_mk _⟩

open CategoryTheory NRR.SingularHomology

/-- The explicit commutative square defining the map of relative pairs
(V,V minus zero) to (E,E minus the zero section). -/
theorem associatedFiber_pair_comm {d n : ℕ} (x : Configuration d n) :
    subIncl (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0} ≫
        TopCat.ofHom (associatedFiberMap x) =
      TopCat.ofHom (associatedFiberNonzeroMap x) ≫
        subIncl (Y := TopCat.of (ConfigurationAssociated d n)) (associatedZeroLocus d n)ᶜ := rfl

def associatedFiberRelative {d n : ℕ} (R : Type) [Ring R] (k : ℕ)
    (x : Configuration d n) :
    HrelSet R k (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0} ⟶
      HrelSet R k (Y := TopCat.of (ConfigurationAssociated d n))
        (associatedZeroLocus d n)ᶜ :=
  HrelMap R k _ _ (associatedFiber_pair_comm x)

/-- The zero-free induced section factors through the zero-section complement
as an equality of continuous maps, ready to be used by relative functoriality. -/
theorem associatedNonzeroSection_comp_inclusion {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) :
    TopCat.ofHom (associatedNonzeroSection f he hnz) ≫
        subIncl (Y := TopCat.of (ConfigurationAssociated d n)) (associatedZeroLocus d n)ᶜ =
      TopCat.ofHom (associatedSection f he) := rfl

/-- The zero-section map followed by the canonical absolute-to-relative map.
This is an actual singular-homology morphism.  Nonvanishing of it is a
separate topological computation, not asserted by its definition. -/
def associatedZeroSectionRelativeMap {d n : ℕ} (R : Type) [Ring R] (k : ℕ) :
    Habs R k (TopCat.of (ConfigurationBase d n)) ⟶
      HrelSet R k (Y := TopCat.of (ConfigurationAssociated d n))
        (associatedZeroLocus d n)ᶜ :=
  HabsMap R k (TopCat.ofHom associatedZeroSection) ≫
    relJ R k (subIncl (Y := TopCat.of (ConfigurationAssociated d n))
      (associatedZeroLocus d n)ᶜ)

/-- A zero-free equivariant map forces the actual zero-section relative
homology morphism to vanish, by its section homotopy and factorization
through the zero-section complement. -/
theorem associatedZeroSectionRelativeMap_eq_zero_of_nonzero {d n : ℕ}
    (R : Type) [Ring R] (k : ℕ)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) :
    associatedZeroSectionRelativeMap (d := d) (n := n) R k = 0 := by
  have hhom := NRR.TopologyPort.singularHomologyMap_eq_of_homotopy
    (ModuleCat.of R R)
    (X := TopCat.of (ConfigurationBase d n))
    (Y := TopCat.of (ConfigurationAssociated d n))
    (f := TopCat.ofHom (associatedSection f he))
    (g := TopCat.ofHom associatedZeroSection)
    (associatedSectionHomotopy f he) k
  change HabsMap R k (TopCat.ofHom (associatedSection f he)) =
    HabsMap R k (TopCat.ofHom associatedZeroSection) at hhom
  unfold associatedZeroSectionRelativeMap
  rw [← hhom,← associatedNonzeroSection_comp_inclusion f he hnz,HabsMap_comp,
    Category.assoc]
  have hz : HabsMap R k
      (subIncl (Y := TopCat.of (ConfigurationAssociated d n)) (associatedZeroLocus d n)ᶜ) ≫
      relJ R k (subIncl (Y := TopCat.of (ConfigurationAssociated d n))
        (associatedZeroLocus d n)ᶜ) = 0 := by
    unfold HabsMap relJ
    rw [← HomologicalComplex.homologyMap_comp]
    simp only [relProj,Limits.cokernel.condition,HomologicalComplex.homologyMap_zero]
  rw [hz,Limits.comp_zero]

/-- The exact remaining nonvanishing interface: a nonzero genuine
zero-section relative morphism obstructs every zero-free equivariant map. -/
theorem equivariant_has_zero_of_associatedZeroSectionRelativeMap_ne_zero {d n : ℕ}
    (R : Type) [Ring R] (k : ℕ)
    (h : associatedZeroSectionRelativeMap (d := d) (n := n) R k ≠ 0)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) :
    ∃ x, f x = 0 := by
  by_contra hnz
  exact h (associatedZeroSectionRelativeMap_eq_zero_of_nonzero R k f he
    (fun x hx => hnz ⟨x,hx⟩))
end NRR.PrimePowerTopology
