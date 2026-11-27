import NRR.PrimePowerTopologyFilteredChains
import NRR.PrimePowerTopologyRelativePairOrbitBasis
import NRR.SingularHomologyRelHomotopy
import NRR.SingularHomologySimplicial
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Free orbit generators for the actual relative singular chains of the Fuks filtration. -/

noncomputable section
open CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

abbrev fuksSimplex (d n b q : ℕ) :=
  (TopCat.toSSet.obj (TopCat.of (compactifiedFuksLevel d n b))).obj (op ⦋q⦌)

def fuksSimplexLower {d n b q : ℕ} (a : ℕ) (s : fuksSimplex d n b q) : Prop :=
  ∀ x, (TopCat.toSSetObjEquiv _ _ s x).val ∈ compactifiedFuksLevel d n a

def fuksRelativeSimplex (d n a b q : ℕ) :=
  {s : fuksSimplex d n b q // ¬ fuksSimplexLower a s}

private theorem fuksSimplexLower_iff {d n a b q : ℕ} (hab : a ≤ b)
    (s : fuksSimplex d n b q) :
    fuksSimplexLower a s ↔ ∃ t : fuksSimplex d n a q,
      (TopCat.toSSet.map (compactifiedFuksInclusion hab)).app _ t = s := by
  constructor
  · intro h
    let t : C((op ⦋q⦌).unop.toTopObj, compactifiedFuksLevel d n a) :=
      ⟨fun x => ⟨(TopCat.toSSetObjEquiv _ _ s x).val, h x⟩,
        (continuous_subtype_val.comp (TopCat.toSSetObjEquiv _ _ s).continuous).subtype_mk _⟩
    refine ⟨(TopCat.toSSetObjEquiv _ _).symm t, ?_⟩
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext x
    change (TopCat.toSSetObjEquiv (TopCat.of (compactifiedFuksLevel d n a)) _
      ((TopCat.toSSetObjEquiv (TopCat.of (compactifiedFuksLevel d n a)) _).symm t) x).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  · rintro ⟨t, rfl⟩ x
    exact (TopCat.toSSetObjEquiv _ _ t x).property

section Chains

variable (R : Type) [CommRing R] {d n a b q : ℕ} (hab : a ≤ b)

def fuksRelativeSimplexGenerator (s : fuksRelativeSimplex d n a b q) :
    (fuksRelativeComplex R (d := d) (n := n) hab).X q :=
  (relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s.val 1)

private theorem fuksSimplex_proj_zero (s : fuksSimplex d n b q)
    (hs : fuksSimplexLower a s) :
    simplexι R s ≫ (relProj R (compactifiedFuksInclusion hab)).f q = 0 := by
  obtain ⟨t, rfl⟩ := (fuksSimplexLower_iff hab s).mp hs
  rw [← simplexι_chainMap_f_assoc]
  change simplexι R t ≫ ((CsingMap R (compactifiedFuksInclusion hab)).f q ≫
    (cokernel.π (CsingMap R (compactifiedFuksInclusion hab))).f q) = 0
  rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, comp_zero]

private def fuksRelativeCoordinateValue (s : fuksSimplex d n b q) :
    ModuleCat.of R R ⟶ ModuleCat.of R (fuksRelativeSimplex d n a b q →₀ R) :=
  open scoped Classical in
  if hs : fuksSimplexLower a s then 0 else
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (Finsupp.single ⟨s, hs⟩ 1))

private def fuksRelativeCoordinatesOnChains :
    (Csing R (TopCat.of (compactifiedFuksLevel d n b))).X q ⟶
      ModuleCat.of R (fuksRelativeSimplex d n a b q →₀ R) :=
  ccDesc R (fuksRelativeCoordinateValue R)

private theorem fuksRelativeCoordinatesOnChains_zero :
    (CsingMap R (compactifiedFuksInclusion (d := d) (n := n) hab)).f q ≫
      fuksRelativeCoordinatesOnChains R (a := a) = 0 := by
  classical
  apply simplicialChain_hom_ext R
  intro t
  change simplexι R t ≫ (simplicialChainMap R (TopCat.toSSet.map
    (compactifiedFuksInclusion hab))).f q ≫ fuksRelativeCoordinatesOnChains R = _
  rw [simplexι_chainMap_f_assoc]
  simp only [fuksRelativeCoordinatesOnChains, ι_ccDesc, comp_zero,
    fuksRelativeCoordinateValue]
  rw [dif_pos ((fuksSimplexLower_iff hab _).mpr ⟨t, rfl⟩)]

def fuksRelativeCoordinates :
    (fuksRelativeComplex R (d := d) (n := n) hab).X q →ₗ[R]
      (fuksRelativeSimplex d n a b q →₀ R) :=
  (cokDesc R (CsingMap R (compactifiedFuksInclusion hab)) q
    (fuksRelativeCoordinatesOnChains R) (fuksRelativeCoordinatesOnChains_zero R hab)).hom

theorem fuksRelativeCoordinates_generator (s : fuksRelativeSimplex d n a b q) :
    fuksRelativeCoordinates R hab (fuksRelativeSimplexGenerator R hab s) =
      Finsupp.single s 1 := by
  classical
  have h := congrArg (fun f => f (simplexι R s.val 1))
    (π_cokDesc R (CsingMap R (compactifiedFuksInclusion hab)) q
      (fuksRelativeCoordinatesOnChains R) (fuksRelativeCoordinatesOnChains_zero R hab))
  calc
    _ = fuksRelativeCoordinatesOnChains R (simplexι R s.val 1) := h
    _ = _ := by
      change (simplexι R s.val ≫ ccDesc R (fuksRelativeCoordinateValue R (a := a))) 1 = _
      rw [ι_ccDesc]
      simp [fuksRelativeCoordinateValue, s.property, LinearMap.toSpanSingleton_apply]

private theorem fuksRelativeSimplexGenerator_coordinates :
    (Finsupp.linearCombination R (fuksRelativeSimplexGenerator R (d := d) (n := n) hab)).comp
      (fuksRelativeCoordinates R hab (q := q)) = LinearMap.id := by
  classical
  letI : Epi ((relProj R (compactifiedFuksInclusion (d := d) (n := n) hab)).f q) := by
    change Epi ((cokernel.π (CsingMap R (compactifiedFuksInclusion hab))).f q)
    infer_instance
  apply (ModuleCat.hom_ext_iff (f := ModuleCat.ofHom _) (g := ModuleCat.ofHom _)).mp
  apply (cancel_epi ((relProj R (compactifiedFuksInclusion hab)).f q)).mp
  apply simplicialChain_hom_ext R
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have hc := π_cokDesc R (CsingMap R (compactifiedFuksInclusion (d := d) (n := n) hab)) q
    (fuksRelativeCoordinatesOnChains R) (fuksRelativeCoordinatesOnChains_zero R hab)
  have hc' := congrArg (fun f => f (simplexι R s r)) hc
  by_cases hs : fuksSimplexLower a s
  · have hz := congrArg (fun f => f r) (fuksSimplex_proj_zero R hab s hs)
    have hz' : (relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s r) = 0 := hz
    change Finsupp.linearCombination R (fuksRelativeSimplexGenerator R hab)
      (fuksRelativeCoordinates R hab
        ((relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s r))) =
      (relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s r)
    rw [hz', map_zero, map_zero]
  · have hd' : fuksRelativeCoordinatesOnChains R (simplexι R s r) =
        r • Finsupp.single (⟨s, hs⟩ : fuksRelativeSimplex d n a b q) 1 := by
      change (simplexι R s ≫ ccDesc R (fuksRelativeCoordinateValue R (a := a))) r = _
      rw [ι_ccDesc]
      simp [fuksRelativeCoordinateValue, hs, LinearMap.toSpanSingleton_apply]
    change Finsupp.linearCombination R (fuksRelativeSimplexGenerator R hab)
      (fuksRelativeCoordinates R hab
        ((relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s r))) =
      (relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s r)
    have hc'' : fuksRelativeCoordinates R hab
        ((relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s r)) =
        r • Finsupp.single (⟨s, hs⟩ : fuksRelativeSimplex d n a b q) 1 := hc'.trans hd'
    rw [hc'', map_smul, Finsupp.linearCombination_single, one_smul]
    change r • ((relProj R (compactifiedFuksInclusion hab)).f q (simplexι R s 1)) = _
    have hr : simplexι R s r = r • simplexι R s 1 := by
      simpa using (simplexι R s).hom.map_smul r (1 : R)
    rw [hr, map_smul]

def fuksRelativeSimplexEquiv :
    (fuksRelativeSimplex d n a b q →₀ R) ≃ₗ[R]
      (fuksRelativeComplex R (d := d) (n := n) hab).X q :=
  LinearEquiv.ofLinear (Finsupp.linearCombination R (fuksRelativeSimplexGenerator R hab))
    (fuksRelativeCoordinates R hab)
    (fuksRelativeSimplexGenerator_coordinates R hab)
    (by
      apply Finsupp.lhom_ext
      intro s r
      simp [fuksRelativeCoordinates_generator])

def fuksRelativeSimplexBasis : Module.Basis (fuksRelativeSimplex d n a b q) R
    ((fuksRelativeComplex R (d := d) (n := n) hab).X q) :=
  (Finsupp.basisSingleOne).map (fuksRelativeSimplexEquiv R hab)

@[simp] theorem fuksRelativeSimplexBasis_apply (s : fuksRelativeSimplex d n a b q) :
    fuksRelativeSimplexBasis R hab s = fuksRelativeSimplexGenerator R hab s := by
  simp [fuksRelativeSimplexBasis, fuksRelativeSimplexEquiv,
    Finsupp.coe_basisSingleOne]

end Chains

private theorem orbitRelabel_one {d n : ℕ} (x : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel (1 : Equiv.Perm (Fin n)) x = x := by
  induction x using OnePoint.rec <;> rfl

private theorem orbitRelabel_mul {d n : ℕ} (g h : Equiv.Perm (Fin n))
    (x : OnePoint (Configuration d n)) :
    compactifiedConfigurationRelabel (g*h) x =
      compactifiedConfigurationRelabel g (compactifiedConfigurationRelabel h x) := by
  induction x using OnePoint.rec <;> rfl

def fuksSimplexRelabel {d n b q : ℕ} [NeZero n] (g : Equiv.Perm (Fin n))
    (s : fuksSimplex d n b q) : fuksSimplex d n b q :=
  (TopCat.toSSet.map (compactifiedFuksRelabelMap g)).app _ s

private theorem fuksSimplexLower_relabel_iff {d n a b q : ℕ} [NeZero n]
    (g : Equiv.Perm (Fin n)) (s : fuksSimplex d n b q) :
    fuksSimplexLower a (fuksSimplexRelabel g s) ↔ fuksSimplexLower a s := by
  constructor
  · intro h x
    exact (compactifiedFuksLevel_relabel_mem_iff g _).mp (h x)
  · intro h x
    exact (compactifiedFuksLevel_relabel_mem_iff g _).mpr (h x)

instance fuksRelativeSimplexMulAction {d n a b q : ℕ} [NeZero n] :
    MulAction (Equiv.Perm (Fin n)) (fuksRelativeSimplex d n a b q) where
  smul g s := ⟨fuksSimplexRelabel g s.val,
    fun h => s.property ((fuksSimplexLower_relabel_iff g s.val).mp h)⟩
  one_smul s := by
    apply Subtype.ext
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact orbitRelabel_one _
  mul_smul g h s := by
    apply Subtype.ext
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact orbitRelabel_mul g h _

theorem fuksRelativeSimplex_action_free {d n a b q : ℕ} [NeZero n]
    (g : Equiv.Perm (Fin n)) (s : fuksRelativeSimplex d n a b q)
    (fixed : g • s = s) : g = 1 := by
  obtain ⟨x, hx⟩ := not_forall.mp s.property
  apply nonconstantInfinityMap_action_free g
    (fun x => (TopCat.toSSetObjEquiv _ _ s.val x).val)
  · refine ⟨x, fun he => hx ?_⟩
    rw [he]
    exact Or.inl rfl
  · intro y
    exact congrArg (fun z : fuksRelativeSimplex d n a b q =>
      (TopCat.toSSetObjEquiv _ _ z.val y).val) fixed

def fuksRelativeOrbitIndex (d n a b q : ℕ) [NeZero n] :=
  MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (fuksRelativeSimplex d n a b q)

private theorem fuksRelativeSimplex_quotient_smul {d n a b q : ℕ} [NeZero n]
    (g : Equiv.Perm (Fin n)) (s : fuksRelativeSimplex d n a b q) :
    (Quotient.mk'' (g • s) : fuksRelativeOrbitIndex d n a b q) = Quotient.mk'' s :=
  Quotient.sound ⟨g, rfl⟩

def fuksRelativeOrbitEquiv {d n a b q : ℕ} [NeZero n] :
    (Equiv.Perm (Fin n) × fuksRelativeOrbitIndex d n a b q) ≃
      fuksRelativeSimplex d n a b q :=
  freeOrbitEquiv (S := fuksRelativeSimplex d n a b q)
    (fun g s fixed => fuksRelativeSimplex_action_free g s fixed)

@[simp] theorem fuksRelativeOrbitEquiv_apply {d n a b q : ℕ} [NeZero n]
    (g : Equiv.Perm (Fin n)) (i : fuksRelativeOrbitIndex d n a b q) :
    fuksRelativeOrbitEquiv (g, i) = g • i.out := rfl

theorem fuksRelativeOrbitEquiv_mul {d n a b q : ℕ} [NeZero n]
    (g h : Equiv.Perm (Fin n)) (i : fuksRelativeOrbitIndex d n a b q) :
    fuksRelativeOrbitEquiv (g*h, i) = g • fuksRelativeOrbitEquiv (h, i) :=
  mul_smul g h i.out

section OrbitBasis

variable (R : Type) [CommRing R] {d n a b : ℕ} [NeZero n] (hab : a ≤ b) (q : ℕ)

theorem fuksRelativeSimplexGenerator_relabel (g : Equiv.Perm (Fin n))
    (s : fuksRelativeSimplex d n a b q) :
    (fuksRelativeRelabel R (d := d) hab g).f q (fuksRelativeSimplexGenerator R hab s) =
      fuksRelativeSimplexGenerator R hab (g • s) := by
  have h : simplexι R s.val ≫ (relProj R (compactifiedFuksInclusion hab)).f q ≫
      (fuksRelativeRelabel R (d := d) hab g).f q =
      simplexι R (g • s).val ≫ (relProj R (compactifiedFuksInclusion hab)).f q := by
    rw [← HomologicalComplex.comp_f, fuksRelativeRelabel, relProj_comp_relComplexMap,
      HomologicalComplex.comp_f]
    change simplexι R s.val ≫ (simplicialChainMap R
      (TopCat.toSSet.map (compactifiedFuksRelabelMap g))).f q ≫ _ = _
    rw [simplexι_chainMap_f_assoc]
    rfl
  exact congrArg (fun f => f 1) h

/-- Each actual relative singular chain module is free on a disjoint union
of regular permutation orbits. -/
def fuksRelativeOrbitBasis :
    Module.Basis (Equiv.Perm (Fin n) × fuksRelativeOrbitIndex d n a b q) R
      ((fuksRelativeComplex R (d := d) (n := n) hab).X q) :=
  freeOrbitBasis R (fuksRelativeSimplexBasis R hab)
    (fuksRelativeSimplex_action_free (d := d) (n := n) (a := a) (b := b) (q := q))

theorem fuksRelativeOrbitBasis_relabel (g h : Equiv.Perm (Fin n))
    (i : fuksRelativeOrbitIndex d n a b q) :
    (fuksRelativeRelabel R (d := d) hab g).f q (fuksRelativeOrbitBasis R hab q (h, i)) =
      fuksRelativeOrbitBasis R hab q (g*h, i) := by
  simpa only [fuksRelativeOrbitBasis] using
    freeOrbitBasis_relabel R (fuksRelativeSimplexBasis R hab)
      (fuksRelativeSimplex_action_free (d := d) (n := n) (a := a) (b := b) (q := q))
      (fun g => ((fuksRelativeRelabel R hab g).f q).hom)
      (fun g s => by
        rw [fuksRelativeSimplexBasis_apply, fuksRelativeSimplexBasis_apply]
        exact fuksRelativeSimplexGenerator_relabel R hab q g s)
      g h i

/-- The lifting property for a module with a basis consisting of free group orbits.
The target actions are genuine left actions by linear endomorphisms. -/
theorem equivariant_lift_of_orbit_basis
    {G I X M N : Type*} [Group G]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (B : Module.Basis (G × I) R X) (ρ : G → Module.End R X)
    (hB : ∀ g h i, ρ g (B (h, i)) = B (g*h, i))
    (α : G →* Module.End R M) (β : G →* Module.End R N)
    (p : M →ₗ[R] N) (hp : Function.Surjective p)
    (hp_eq : ∀ g x, p (α g x) = β g (p x))
    (f : X →ₗ[R] N) (hf : ∀ g x, f (ρ g x) = β g (f x)) :
    ∃ l : X →ₗ[R] M, p.comp l = f ∧ ∀ g x, l (ρ g x) = α g (l x) := by
  classical
  choose v hv using fun i : I => hp (f (B (1, i)))
  let l : X →ₗ[R] M := B.constr R (fun j => α j.1 (v j.2))
  have hl (g : G) (i : I) : l (B (g, i)) = α g (v i) := B.constr_basis R _ _
  refine ⟨l, B.ext (fun j => ?_), fun g => ?_⟩
  · rcases j with ⟨h, i⟩
    change p (l (B (h, i))) = f (B (h, i))
    rw [hl, hp_eq, hv]
    have h := hf h (B (1, i))
    rw [hB, mul_one] at h
    exact h.symm
  · have he : l.comp (ρ g) = (α g).comp l := by
      apply B.ext
      rintro ⟨h, i⟩
      change l (ρ g (B (h, i))) = α g (l (B (h, i)))
      rw [hB, hl, hl, map_mul]
      rfl
    exact fun x => LinearMap.congr_fun he x

/-- Equivariant projective lifting for every degree of the actual Fuks relative complex. -/
theorem fuksRelative_equivariant_lift
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (α : Equiv.Perm (Fin n) →* Module.End R M)
    (β : Equiv.Perm (Fin n) →* Module.End R N)
    (p : M →ₗ[R] N) (hp : Function.Surjective p)
    (hp_eq : ∀ g x, p (α g x) = β g (p x))
    (f : (fuksRelativeComplex R (d := d) (n := n) hab).X q →ₗ[R] N)
    (hf : ∀ g x, f ((fuksRelativeRelabel R hab g).f q x) = β g (f x)) :
    ∃ l : (fuksRelativeComplex R (d := d) (n := n) hab).X q →ₗ[R] M,
      p.comp l = f ∧ ∀ g x, l ((fuksRelativeRelabel R hab g).f q x) = α g (l x) :=
  equivariant_lift_of_orbit_basis R (fuksRelativeOrbitBasis R hab q)
    (fun g => ((fuksRelativeRelabel R hab g).f q).hom)
    (fuksRelativeOrbitBasis_relabel R hab q) α β p hp hp_eq f hf

end OrbitBasis
end NRR.PrimePowerTopology
