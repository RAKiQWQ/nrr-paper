import NRR.PrimePowerTopologyAssociatedBMFundamental
import NRR.SingularHomologySimplicial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.GroupTheory.Perm.Sign

/-! An explicit compact-cube chart for the one-point compactification of
ordered configuration space and actual singular simplices on its staircase
triangulation. -/

noncomputable section
open Set Topology CategoryTheory
open scoped OnePoint Simplicial
open Opposite
open NRR.PrimePower NRR.SingularHomology
open NRR.SingularHomology.SimplexGeometry

namespace NRR.PrimePowerTopology

abbrev ConfigurationAxis (d n : ℕ) := Fin n × Fin d

def configurationAxisEquiv (d n : ℕ) :
    ConfigurationAxis d n ≃ Fin (n*d) :=
  Fintype.equivFinOfCardEq (by simp [ConfigurationAxis])

/-- The compact cube has one scalar coordinate per point-coordinate pair. -/
abbrev ConfigurationCube (d n : ℕ) := Fin (n*d) → Set.Icc (0 : ℝ) 1

def configurationCubeInterior (d n : ℕ) : Set (ConfigurationCube d n) :=
  {x | ∀ a, (x a).val ∈ Set.Ioo (0 : ℝ) 1}

theorem isOpen_configurationCubeInterior (d n : ℕ) :
    IsOpen (configurationCubeInterior d n) := by
  classical
  rw [configurationCubeInterior]
  have repr : {x : ConfigurationCube d n | ∀ a,
      (x a).val ∈ Set.Ioo (0 : ℝ) 1} =
      ⋂ a : Fin (n*d),
        (fun x : ConfigurationCube d n => (x a).val) ⁻¹' Set.Ioo (0 : ℝ) 1 := by
    ext x
    simp only [mem_setOf_eq, mem_iInter, mem_preimage]
  rw [repr]
  exact isOpen_iInter_of_finite fun a =>
    isOpen_Ioo.preimage (by fun_prop)

/-- Affinely identify the unit interval with the tangent chart interval. -/
def unitIntervalAngleOrderIso : Set.Ioo (0 : ℝ) 1 ≃o
    Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) where
  toFun x := ⟨Real.pi * x.val - Real.pi / 2, by
    constructor
    · have h := mul_pos Real.pi_pos x.property.1
      linarith
    · have h := (mul_lt_mul_iff_right₀ Real.pi_pos).2 x.property.2
      linarith⟩
  invFun x := ⟨x.val / Real.pi + 1 / 2, by
    constructor
    · have h := div_lt_div_of_pos_right x.property.1 Real.pi_pos
      have hh : -(1 / 2 : ℝ) < x.val / Real.pi := by
        have hp := Real.pi_ne_zero
        field_simp at h ⊢
        linarith
      linarith
    · have h := div_lt_div_of_pos_right x.property.2 Real.pi_pos
      have hh : x.val / Real.pi < (1 / 2 : ℝ) := by
        have hp := Real.pi_ne_zero
        field_simp at h ⊢
        linarith
      linarith⟩
  left_inv x := by
    apply Subtype.ext
    have hp := Real.pi_ne_zero
    field_simp
    ring
  right_inv x := by
    apply Subtype.ext
    have hp := Real.pi_ne_zero
    field_simp
    ring
  map_rel_iff' := by
    intro x y
    change (Real.pi * x.val - Real.pi / 2 ≤ Real.pi * y.val - Real.pi / 2) ↔
      x.val ≤ y.val
    constructor
    · intro h
      exact (mul_le_mul_iff_of_pos_left Real.pi_pos).mp (by linarith)
    · intro h
      exact sub_le_sub_right ((mul_le_mul_iff_of_pos_left Real.pi_pos).mpr h) _

def unitOpenIntervalToReal : Set.Ioo (0 : ℝ) 1 ≃ₜ ℝ :=
  unitIntervalAngleOrderIso.toHomeomorph.trans Real.tanOrderIso.toHomeomorph

/-- Tangent in every scalar coordinate gives a homeomorphism from the open
cube to the ambient ordered Euclidean space. -/
def configurationCubeInteriorEuclidean (d n : ℕ) :
    configurationCubeInterior d n ≃ₜ (Fin n → Space d) := by
  let toPi : configurationCubeInterior d n ≃ₜ
      (Fin (n*d) → Set.Ioo (0 : ℝ) 1) :=
    { toFun := fun x a => ⟨(x.val a).val,x.property a⟩
      invFun := fun y => ⟨(fun a => ⟨(y a).val,(y a).property.1.le,
          (y a).property.2.le⟩),fun a => (y a).property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext a
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        funext a
        apply Subtype.ext
        rfl
      continuous_toFun := by
        apply continuous_pi
        intro a
        exact (continuous_subtype_val.comp
          ((continuous_apply a).comp continuous_subtype_val)).subtype_mk _
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro a
        exact (continuous_subtype_val.comp (continuous_apply a)).subtype_mk _ }
  let reals := Homeomorph.piCongrRight
    (fun _ : Fin (n*d) => unitOpenIntervalToReal)
  let ambient : (Fin (n*d) → ℝ) ≃ₜ (Fin n → Space d) :=
    { toFun := fun x i => (EuclideanSpace.equiv (Fin d) ℝ).symm
        (fun j => x (configurationAxisEquiv d n ⟨i,j⟩))
      invFun := fun x a =>
        let b := (configurationAxisEquiv d n).symm a
        EuclideanSpace.equiv (Fin d) ℝ (x b.1) b.2
      left_inv := by
        intro x
        funext a
        simp [configurationAxisEquiv]
      right_inv := by
        intro x
        funext i
        apply (EuclideanSpace.equiv (Fin d) ℝ).injective
        funext j
        simp
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
          (continuous_pi fun j =>
            continuous_apply (configurationAxisEquiv d n ⟨i,j⟩))
      continuous_invFun := by
        apply continuous_pi
        intro a
        let b := (configurationAxisEquiv d n).symm a
        exact (continuous_apply b.2).comp
          ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp
            (continuous_apply b.1)) }
  exact toPi.trans (reals.trans ambient)

instance configurationCubeCompact (d n : ℕ) : CompactSpace (ConfigurationCube d n) := by
  dsimp [ConfigurationCube]
  infer_instance

instance configurationCubeT2 (d n : ℕ) : T2Space (ConfigurationCube d n) := by
  dsimp [ConfigurationCube]
  infer_instance

/-- The actual continuous compact-cube map. Boundary coordinates and finite
collisions both map to the point at infinity. -/
def configurationCubeCollapse (d n : ℕ) :
    C(ConfigurationCube d n,OnePoint (Configuration d n)) := by
  let chart := configurationCubeInteriorEuclidean d n
  let compactChart := chart.onePointCongr
  exact ⟨fun x => configurationOnePointCollapse d n
      (compactChart (openCollapse (configurationCubeInterior d n) x)),
    (configurationOnePointCollapse d n).continuous.comp
      (compactChart.continuous.comp
        (continuous_openCollapse _ (isOpen_configurationCubeInterior d n)))⟩

@[simp] theorem configurationCubeCollapse_boundary {d n : ℕ}
    (x : ConfigurationCube d n)
    (hx : x ∉ configurationCubeInterior d n) :
    configurationCubeCollapse d n x = ∞ := by
  simp [configurationCubeCollapse, openCollapse, hx]

@[simp] theorem configurationCubeCollapse_interior {d n : ℕ}
    (x : configurationCubeInterior d n) :
    configurationCubeCollapse d n x.val =
      configurationOnePointCollapse d n
        ((configurationCubeInteriorEuclidean d n x : Fin n → Space d) :
          OnePoint (Fin n → Space d)) := by
  simp [configurationCubeCollapse, openCollapse]

/-- An interior cube point whose ambient coordinates are distinct maps to the
corresponding finite configuration, with no chain-level projection. -/
theorem configurationCubeCollapse_interior_configuration {d n : ℕ}
    (x : configurationCubeInterior d n)
    (h : Function.Injective (configurationCubeInteriorEuclidean d n x)) :
    configurationCubeCollapse d n x.val =
      ((⟨configurationCubeInteriorEuclidean d n x,h⟩ : Configuration d n) :
        OnePoint (Configuration d n)) := by
  rw [configurationCubeCollapse_interior]
  exact configurationOnePointCollapse_config ⟨_,h⟩

/-- Finite collisions in the open cube are genuinely collapsed to infinity. -/
theorem configurationCubeCollapse_interior_collision {d n : ℕ}
    (x : configurationCubeInterior d n)
    (h : ¬ Function.Injective (configurationCubeInteriorEuclidean d n x)) :
    configurationCubeCollapse d n x.val = ∞ := by
  rw [configurationCubeCollapse_interior]
  exact configurationOnePointCollapse_collision (configurationCubeInteriorEuclidean d n x) h

/-- The scalar coordinate of a staircase affine simplex. -/
def staircaseCoordinate {m : ℕ} (π : Equiv.Perm (Fin m))
    (j : Fin m) (x : Simplex m) : ℝ :=
  ∑ k : Fin (m+1), if (π j).val < k.val then (x k : ℝ) else 0

/-- The ordered vertices of a staircase simplex form the monotone path from
the all-zero cube vertex to the all-one cube vertex. -/
theorem staircaseCoordinate_vertex {m : ℕ} (π : Equiv.Perm (Fin m))
    (j : Fin m) (k : Fin (m+1)) :
    staircaseCoordinate π j (SimplexGeometry.vertex m k) =
      if (π j).val < k.val then 1 else 0 := by
  classical
  unfold staircaseCoordinate
  by_cases h : (π j).val < k.val
  · rw [Finset.sum_eq_single k]
    · simp [h]
    · intro b hb hbk
      simp [SimplexGeometry.vertex_apply, hbk]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hb' : (π j).val < b.val
    · have hbk : b ≠ k := by
        intro he
        subst b
        exact h hb'
      simp [hb', SimplexGeometry.vertex_apply, hbk]
    · simp [hb']

/-- One actual affine simplex of the staircase triangulation of a unit
cube, with a separate parameter for its scalar dimension. -/
def staircaseUnitCubeSimplex {m : ℕ} (π : Equiv.Perm (Fin m)) :
    C(Simplex m,Fin m → Set.Icc (0 : ℝ) 1) := by
  classical
  exact ⟨fun x a => by
      refine ⟨staircaseCoordinate π a x,?_,?_⟩
      · apply Finset.sum_nonneg
        intro k hk
        split_ifs <;> positivity
      · have hx : (∑ k : Fin (m+1), (x k : ℝ)) = 1 := by
          exact_mod_cast x.property
        rw [← hx]
        apply Finset.sum_le_sum
        intro k hk
        by_cases h : (π a).val < k.val
        · simp [h]
        · simp [h]
    , by
      apply continuous_pi
      intro a
      apply Continuous.subtype_mk
      unfold staircaseCoordinate
      exact continuous_finset_sum _ fun k _ => by
        by_cases h : (π a).val < k.val
        · simp only [if_pos h]
          change Continuous fun x : Simplex m => (x k : ℝ)
          exact NNReal.continuous_coe.comp
            ((continuous_apply k).comp continuous_subtype_val)
        · simp only [if_neg h]
          exact continuous_const⟩

/-- One actual affine singular simplex for each top simplex in the staircase
triangulation of the configuration compact cube. -/
def staircaseCubeSimplex {d n : ℕ} (π : Equiv.Perm (Fin (n*d))) :
    C(Simplex (n*d),ConfigurationCube d n) := staircaseUnitCubeSimplex π

@[simp] theorem staircaseCubeSimplex_vertex {d n : ℕ}
    (π : Equiv.Perm (Fin (n*d))) (k : Fin (n*d+1)) (a : Fin (n*d)) :
    (staircaseCubeSimplex π (SimplexGeometry.vertex (n*d) k) a).val =
      if (π a).val < k.val then 1 else 0 := by
  simp [staircaseCubeSimplex, staircaseUnitCubeSimplex, staircaseCoordinate_vertex]

/-- Precomposing a staircase coordinate by a simplicial map only depends on
the threshold values at the retained vertices. -/
theorem staircaseCoordinate_toTopMap {m k : ℕ}
    (π : Equiv.Perm (Fin m)) (f : ⦋k⦌ ⟶ ⦋m⦌)
    (x : Simplex k) (a : Fin m) :
    staircaseCoordinate π a (SimplexCategory.toTopMap f x) =
      ∑ j : Fin (k+1), if (π a).val < (f j).val then (x j : ℝ) else 0 := by
  classical
  unfold staircaseCoordinate
  simp only [SimplexCategory.coe_toTopMap, Finset.sum_filter]
  simp only [NNReal.coe_sum, apply_ite, NNReal.coe_zero]
  let p : Fin (m+1) → Prop := fun l => (π a).val < l.val
  have hmove (l : Fin (m+1)) :
      (if p l then ∑ j : Fin (k+1),
          if f j = l then (x j : ℝ) else 0 else 0) =
        ∑ j : Fin (k+1), if p l then
          (if f j = l then (x j : ℝ) else 0) else 0 := by
    by_cases hl : p l <;> simp [hl]
  change (∑ l : Fin (m+1), if p l then ∑ j : Fin (k+1),
    if f j = l then (x j : ℝ) else 0 else 0) = _
  conv_lhs => arg 2; ext l; rw [hmove l]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [p, if_pos rfl] using
    (Finset.sum_eq_single (s := Finset.univ)
      (f := fun l : Fin (m+1) => if p l then
        (if f j = l then (x j : ℝ) else 0) else 0)
      (f j) (by
        intro l hl hlj
        dsimp only
        split_ifs with hp he
        · exact (hlj he.symm).elim
        · rfl
        · rfl) (by simp))

/-- Two staircase chambers have the same actual affine face whenever their
coordinate thresholds agree on every vertex retained by that face. -/
theorem staircaseCubeSimplex_precomp_eq {d n k : ℕ}
    (π ρ : Equiv.Perm (Fin (n*d))) (f : ⦋k⦌ ⟶ ⦋n*d⦌)
    (hthreshold : ∀ a : Fin (n*d),
      ∀ j : Fin (k+1), ((π a).val < (f j).val) = ((ρ a).val < (f j).val)) :
    (staircaseCubeSimplex π).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ =
      (staircaseCubeSimplex ρ).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ := by
  apply ContinuousMap.ext
  intro x
  funext a
  apply Subtype.ext
  change staircaseCoordinate π a (SimplexCategory.toTopMap f x) =
    staircaseCoordinate ρ a (SimplexCategory.toTopMap f x)
  rw [staircaseCoordinate_toTopMap, staircaseCoordinate_toTopMap]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [hthreshold a j]

/-- Swapping consecutive coordinate ranks changes the threshold at just the
single intermediate cube vertex. -/
theorem staircaseAdjacentSwap_threshold {m : ℕ}
    (π : Equiv.Perm (Fin m)) (a b j : Fin m) (hab : b.val = a.val+1)
    (t : Fin (m+1)) (ht : t.val ≠ b.val) :
    (((Equiv.swap a b * π) j).val < t.val) ↔ ((π j).val < t.val) := by
  classical
  by_cases hja : π j = a
  · simp only [Equiv.Perm.mul_apply, hja, Equiv.swap_apply_left]
    omega
  · by_cases hjb : π j = b
    · simp only [Equiv.Perm.mul_apply, hjb, Equiv.swap_apply_right]
      omega
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hja hjb]

/-- The two adjacent staircase chambers induce exactly the same continuous
face on any simplicial map omitting their intermediate vertex. -/
theorem staircaseCubeSimplex_adjacent_face {d n k : ℕ}
    (π : Equiv.Perm (Fin (n*d))) (a b : Fin (n*d)) (hab : b.val = a.val+1)
    (f : ⦋k⦌ ⟶ ⦋n*d⦌) (hf : ∀ t, (f t).val ≠ b.val) :
    (staircaseCubeSimplex (Equiv.swap a b * π)).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ =
      (staircaseCubeSimplex π).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ := by
  apply staircaseCubeSimplex_precomp_eq
  intro j t
  exact propext (staircaseAdjacentSwap_threshold π a b j hab (f t) (hf t))

/-- The orientation signs of the two chambers sharing an internal face are
opposite. -/
theorem staircaseAdjacentSwap_sign {m : ℕ} (π : Equiv.Perm (Fin m))
    (a b : Fin m) (hab : b.val = a.val+1) :
    Equiv.Perm.sign (Equiv.swap a b * π) = - Equiv.Perm.sign π := by
  have hne : a ≠ b := by intro he; have := congrArg Fin.val he; omega
  rw [map_mul, Equiv.Perm.sign_swap hne, neg_one_mul]

/-- The staircase simplex after the actual collision/boundary collapse. -/
def configurationStaircaseSimplex {d n : ℕ}
    (π : Equiv.Perm (Fin (n*d))) :
    C(Simplex (n*d),OnePoint (Configuration d n)) :=
  (configurationCubeCollapse d n).comp
    (staircaseCubeSimplex (d := d) (n := n) π)

/-- The actual singular-set simplex underlying a collapsed staircase chamber. -/
def configurationStaircaseSSetSimplex {d n : ℕ}
    (π : Equiv.Perm (Fin (n*d))) :
    (TopCat.toSSet.obj (TopCat.of (OnePoint (Configuration d n)))).obj
        (op ⦋n*d⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of (OnePoint (Configuration d n)))
    (op ⦋n*d⦌)).symm (configurationStaircaseSimplex π)

/-- The actual basis singular-chain generator represented by a staircase
simplex. -/
def configurationStaircaseSingularGenerator (R : Type) [Ring R]
    {d n : ℕ} (π : Equiv.Perm (Fin (n*d))) :
    ModuleCat.of R R ⟶
      (Csing R (TopCat.of (OnePoint (Configuration d n)))).X (n*d) :=
  simplexι R (configurationStaircaseSSetSimplex π)

/-- The same actual singular simplex mapped to the ambient-orientation
twisted Borel--Moore source complex. -/
def configurationStaircaseTwistedGenerator (R : Type) [CommRing R]
    {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)
    (π : Equiv.Perm (Fin (n*d))) :
    ModuleCat.of R R ⟶ (associatedBMTwistedSource R (d := d) χ).X (n*d) :=
  configurationStaircaseSingularGenerator R π ≫
    (relProj R (associatedBMSourceIncl d n)).f (n*d) ≫
      (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
        (associatedBMSourceRelativeAction R)).f (n*d)

/-- The same chamber generator with the actual ambient determinant character
over prime coefficients. -/
def configurationAmbientTwistedStaircaseGenerator (p : ℕ) {d n : ℕ}
    (π : Equiv.Perm (Fin (n*d))) :
    ModuleCat.of (ZMod p) (ZMod p) ⟶
      (associatedBMTwistedSource (ZMod p) (d := d)
        (associatedAmbientOrientationMod p d n)).X (n*d) :=
  configurationStaircaseTwistedGenerator (ZMod p)
    (associatedAmbientOrientationMod p d n) π

/-- Every individual chamber generator is represented by a genuine continuous
singular simplex and all chain projections are the library's actual functorial
maps. No quotient-orbit sum is implicit in this definition. -/
theorem configurationStaircaseTwistedGenerator_is_actual (R : Type)
    [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)
    (π : Equiv.Perm (Fin (n*d))) :
    configurationStaircaseTwistedGenerator R χ π =
      configurationStaircaseSingularGenerator R π ≫
        (relProj R (associatedBMSourceIncl d n)).f (n*d) ≫
          (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
            (associatedBMSourceRelativeAction R)).f (n*d) := rfl

end NRR.PrimePowerTopology
