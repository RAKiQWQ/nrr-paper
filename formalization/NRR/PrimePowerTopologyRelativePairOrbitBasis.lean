import NRR.SingularHomologyRelHomotopy
import NRR.SingularHomologySimplicial
import NRR.TopologyPort.SingularPrism
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Generic orbit bases for relative singular chains of a topological pair.

The relative simplex labels are precisely the singular simplices not contained
in the chosen invariant subspace. If the action is pointwise free outside
that subspace, those labels split into regular group orbits.
-/

noncomputable section
open CategoryTheory Limits Opposite Simplicial
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

abbrev relativePairSimplex (X : TopCat.{0}) (q : ℕ) :=
  (TopCat.toSSet.obj X).obj (op ⦋q⦌)

def relativePairSimplexInSubspace {X : TopCat.{0}} (A : Set X) {q : ℕ}
    (s : relativePairSimplex X q) : Prop :=
  ∀ x, (TopCat.toSSetObjEquiv X _ s x) ∈ A

def relativePairSimplexOutside (X : TopCat.{0}) (A : Set X) (q : ℕ) :=
  {s : relativePairSimplex X q // ¬ relativePairSimplexInSubspace A s}

def relativePairInclusion {X : TopCat.{0}} (A : Set X) : TopCat.of A ⟶ X :=
  subIncl (Y := X) A

instance mono_relativePairInclusion {X : TopCat.{0}} (A : Set X) :
    Mono (relativePairInclusion A) := mono_subIncl (Y := X) A

private theorem relativePairSimplexInSubspace_iff {X : TopCat.{0}} {A : Set X}
    {q : ℕ} (s : relativePairSimplex X q) :
    relativePairSimplexInSubspace A s ↔
      ∃ t : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋q⦌),
        (TopCat.toSSet.map (relativePairInclusion A)).app _ t = s := by
  constructor
  · intro h
    let f : C((op ⦋q⦌).unop.toTopObj, X) := TopCat.toSSetObjEquiv X _ s
    let t : C((op ⦋q⦌).unop.toTopObj, TopCat.of A) :=
      ⟨fun x => ⟨f x, h x⟩, by
        exact f.continuous.subtype_mk _⟩
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of A) _).symm t, ?_⟩
    apply (TopCat.toSSetObjEquiv X _).injective
    change (relativePairInclusion A).hom.comp
      (TopCat.toSSetObjEquiv (TopCat.of A) _
        ((TopCat.toSSetObjEquiv (TopCat.of A) _).symm t)) =
      TopCat.toSSetObjEquiv X _ s
    apply ContinuousMap.ext
    intro x
    change (TopCat.toSSetObjEquiv (TopCat.of A) _
      ((TopCat.toSSetObjEquiv (TopCat.of A) _).symm t) x).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  · rintro ⟨t, rfl⟩ x
    exact (TopCat.toSSetObjEquiv (TopCat.of A) _ t x).property

section Chains

variable (R : Type) [CommRing R] {X : TopCat.{0}} {A : Set X} {q : ℕ}

def relativePairSimplexGenerator (s : relativePairSimplexOutside X A q) :
    (relComplex R (relativePairInclusion A)).X q :=
  (relProj R (relativePairInclusion A)).f q (simplexι R s.val 1)

private theorem relativePairSimplex_proj_zero (s : relativePairSimplex X q)
    (hs : relativePairSimplexInSubspace A s) :
    simplexι R s ≫ (relProj R (relativePairInclusion A)).f q = 0 := by
  obtain ⟨t, rfl⟩ := (relativePairSimplexInSubspace_iff s).mp hs
  rw [← simplexι_chainMap_f_assoc]
  change simplexι R t ≫ ((CsingMap R (relativePairInclusion A)).f q ≫
    (cokernel.π (CsingMap R (relativePairInclusion A))).f q) = 0
  rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, comp_zero]

private def relativePairCoordinateValue (s : relativePairSimplex X q) :
    ModuleCat.of R R ⟶ ModuleCat.of R (relativePairSimplexOutside X A q →₀ R) :=
  open scoped Classical in
  if hs : relativePairSimplexInSubspace A s then 0 else
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _
      (Finsupp.single ⟨s, hs⟩ 1))

private def relativePairCoordinatesOnChains :
    (Csing R X).X q ⟶ ModuleCat.of R (relativePairSimplexOutside X A q →₀ R) :=
  ccDesc R (relativePairCoordinateValue R)

private theorem relativePairCoordinatesOnChains_zero :
    (CsingMap R (relativePairInclusion A)).f q ≫
      relativePairCoordinatesOnChains R (A := A) = 0 := by
  classical
  apply simplicialChain_hom_ext R
  intro t
  change simplexι R t ≫ (simplicialChainMap R (TopCat.toSSet.map
    (relativePairInclusion A))).f q ≫ relativePairCoordinatesOnChains R = _
  rw [simplexι_chainMap_f_assoc]
  simp only [relativePairCoordinatesOnChains, ι_ccDesc, comp_zero,
    relativePairCoordinateValue]
  rw [dif_pos ((relativePairSimplexInSubspace_iff (A := A)
    ((TopCat.toSSet.map (relativePairInclusion A)).app _ t)).mpr ⟨t, rfl⟩)]

def relativePairCoordinates :
    (relComplex R (relativePairInclusion A)).X q →ₗ[R]
      (relativePairSimplexOutside X A q →₀ R) :=
  (cokDesc R (CsingMap R (relativePairInclusion A)) q
    (relativePairCoordinatesOnChains R) (relativePairCoordinatesOnChains_zero R)).hom

theorem relativePairCoordinates_generator (s : relativePairSimplexOutside X A q) :
    relativePairCoordinates R (A := A) (q := q)
      (relativePairSimplexGenerator R s) = Finsupp.single s 1 := by
  classical
  have h := congrArg (fun f => f (simplexι R s.val 1))
    (π_cokDesc R (CsingMap R (relativePairInclusion A)) q
      (relativePairCoordinatesOnChains R) (relativePairCoordinatesOnChains_zero R))
  calc
    _ = relativePairCoordinatesOnChains R (simplexι R s.val 1) := h
    _ = _ := by
      change (simplexι R s.val ≫ ccDesc R (relativePairCoordinateValue R)) 1 = _
      rw [ι_ccDesc]
      simp [relativePairCoordinateValue, s.property, LinearMap.toSpanSingleton_apply]

private theorem relativePairSimplexGenerator_coordinates :
    (Finsupp.linearCombination R
      (relativePairSimplexGenerator R (X := X) (A := A))).comp
      (relativePairCoordinates R (A := A) (q := q)) = LinearMap.id := by
  classical
  letI : Epi ((relProj R (relativePairInclusion A)).f q) := by
    change Epi ((cokernel.π (CsingMap R (relativePairInclusion A))).f q)
    infer_instance
  apply (ModuleCat.hom_ext_iff (f := ModuleCat.ofHom _) (g := ModuleCat.ofHom _)).mp
  apply (cancel_epi ((relProj R (relativePairInclusion A)).f q)).mp
  apply simplicialChain_hom_ext R
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have hc := π_cokDesc R (CsingMap R (relativePairInclusion A)) q
    (relativePairCoordinatesOnChains R) (relativePairCoordinatesOnChains_zero R)
  have hc' := congrArg (fun f => f (simplexι R s r)) hc
  by_cases hs : relativePairSimplexInSubspace A s
  · have hz := congrArg (fun f => f r) (relativePairSimplex_proj_zero R s hs)
    have hz' : (relProj R (relativePairInclusion A)).f q (simplexι R s r) = 0 := hz
    change Finsupp.linearCombination R (relativePairSimplexGenerator R)
      (relativePairCoordinates R (A := A)
        ((relProj R (relativePairInclusion A)).f q (simplexι R s r))) =
      (relProj R (relativePairInclusion A)).f q (simplexι R s r)
    rw [hz', map_zero, map_zero]
  · have hd' : relativePairCoordinatesOnChains R (simplexι R s r) =
        r • Finsupp.single (⟨s, hs⟩ : relativePairSimplexOutside X A q) 1 := by
      change (simplexι R s ≫ ccDesc R (relativePairCoordinateValue R)) r = _
      rw [ι_ccDesc]
      simp [relativePairCoordinateValue, hs, LinearMap.toSpanSingleton_apply]
    change Finsupp.linearCombination R (relativePairSimplexGenerator R)
      (relativePairCoordinates R (A := A)
        ((relProj R (relativePairInclusion A)).f q (simplexι R s r))) =
      (relProj R (relativePairInclusion A)).f q (simplexι R s r)
    have hc'' : relativePairCoordinates R (A := A)
        ((relProj R (relativePairInclusion A)).f q (simplexι R s r)) =
        r • Finsupp.single (⟨s, hs⟩ : relativePairSimplexOutside X A q) 1 := hc'.trans hd'
    rw [hc'', map_smul, Finsupp.linearCombination_single, one_smul]
    change r • ((relProj R (relativePairInclusion A)).f q (simplexι R s 1)) = _
    have hr : simplexι R s r = r • simplexι R s 1 := by
      simpa using (simplexι R s).hom.map_smul r (1 : R)
    rw [hr, map_smul]

def relativePairSimplexEquiv :
    (relativePairSimplexOutside X A q →₀ R) ≃ₗ[R]
      (relComplex R (relativePairInclusion A)).X q :=
  LinearEquiv.ofLinear
    (Finsupp.linearCombination R (relativePairSimplexGenerator R (X := X) (A := A)))
    (relativePairCoordinates R (A := A) (q := q))
    (relativePairSimplexGenerator_coordinates R)
    (by
      apply Finsupp.lhom_ext
      intro s r
      simp [relativePairCoordinates_generator])

def relativePairSimplexBasis : Module.Basis (relativePairSimplexOutside X A q) R
    ((relComplex R (relativePairInclusion A)).X q) :=
  (Finsupp.basisSingleOne).map (relativePairSimplexEquiv R)

@[simp] theorem relativePairSimplexBasis_apply (s : relativePairSimplexOutside X A q) :
    relativePairSimplexBasis R s = relativePairSimplexGenerator R s := by
  simp [relativePairSimplexBasis, relativePairSimplexEquiv,
    Finsupp.coe_basisSingleOne]

end Chains

section PairAction

variable {G : Type*} [Group G] {X : TopCat.{0}} {A : Set X}

def relativePairSimplexRelabel (α : G → X ≃ₜ X) (g : G) {q : ℕ}
    (s : relativePairSimplex X q) : relativePairSimplex X q :=
  (TopCat.toSSet.map (TopCat.ofHom ⟨α g, (α g).continuous⟩)).app _ s

omit [Group G] in
theorem relativePairSimplexRelabel_point (α : G → X ≃ₜ X) (g : G) {q : ℕ}
    (s : relativePairSimplex X q) (x : ⦋q⦌.toTopObj) :
    (TopCat.toSSetObjEquiv X _ (relativePairSimplexRelabel α g s)) x =
      α g ((TopCat.toSSetObjEquiv X _ s) x) := rfl

omit [Group G] in
theorem relativePairSimplexInSubspace_relabel_iff (α : G → X ≃ₜ X)
    (hA : ∀ g x, α g x ∈ A ↔ x ∈ A) (g : G) {q : ℕ}
    (s : relativePairSimplex X q) :
    relativePairSimplexInSubspace A (relativePairSimplexRelabel α g s) ↔
      relativePairSimplexInSubspace A s := by
  constructor
  · intro hs x
    have hx : α g ((TopCat.toSSetObjEquiv X _ s) x) ∈ A := by
      simpa only [relativePairSimplexRelabel_point] using hs x
    exact (hA g _).mp hx
  · intro hs x
    have hx : α g ((TopCat.toSSetObjEquiv X _ s) x) ∈ A := (hA g _).mpr (hs x)
    simpa only [relativePairSimplexRelabel_point] using hx

def relativePairSimplexOutsideMulAction (α : G → X ≃ₜ X)
    (hA : ∀ g x, α g x ∈ A ↔ x ∈ A)
    (h1 : ∀ x, α 1 x = x)
    (hmul : ∀ g h x, α (g * h) x = α g (α h x))
    (q : ℕ) : MulAction G (relativePairSimplexOutside X A q) where
  smul g s := ⟨relativePairSimplexRelabel α g s.val,
    fun hs => s.property ((relativePairSimplexInSubspace_relabel_iff α hA g s.val).mp hs)⟩
  one_smul s := by
    apply Subtype.ext
    apply (TopCat.toSSetObjEquiv X _).injective
    apply ContinuousMap.ext
    intro x
    change (TopCat.toSSetObjEquiv X _
      (relativePairSimplexRelabel α 1 s.val)) x = _
    rw [relativePairSimplexRelabel_point]
    exact h1 _
  mul_smul g h s := by
    apply Subtype.ext
    apply (TopCat.toSSetObjEquiv X _).injective
    apply ContinuousMap.ext
    intro x
    change (TopCat.toSSetObjEquiv X _
      (relativePairSimplexRelabel α (g * h) s.val)) x =
      (TopCat.toSSetObjEquiv X _
        (relativePairSimplexRelabel α g (relativePairSimplexRelabel α h s.val))) x
    rw [relativePairSimplexRelabel_point, relativePairSimplexRelabel_point,
      relativePairSimplexRelabel_point]
    exact hmul g h _

theorem relativePairSimplex_action_free (α : G → X ≃ₜ X)
    (hfree : ∀ g x, x ∉ A → α g x = x → g = 1)
    {q : ℕ} (act : MulAction G (relativePairSimplexOutside X A q))
    (hact : ∀ g s, (act.smul g s).val = relativePairSimplexRelabel α g s.val)
    (g : G) (s : relativePairSimplexOutside X A q)
    (fixed : act.smul g s = s) : g = 1 := by
  obtain ⟨x, hx⟩ := not_forall.mp s.property
  apply hfree g ((TopCat.toSSetObjEquiv X _ s.val) x) hx
  have he := congrArg (fun z : relativePairSimplexOutside X A q =>
    (TopCat.toSSetObjEquiv X _ z.val) x) fixed
  have hpt : (TopCat.toSSetObjEquiv X _ (act.smul g s).val) x =
      α g ((TopCat.toSSetObjEquiv X _ s.val) x) := by
    rw [hact]
    exact relativePairSimplexRelabel_point α g s.val x
  change (TopCat.toSSetObjEquiv X _ (act.smul g s).val) x =
    (TopCat.toSSetObjEquiv X _ s.val) x at he
  rw [hpt] at he
  exact he

end PairAction

section FreeOrbit

variable {G S M I : Type*} [Group G] [MulAction G S]

def freeOrbitIndex := MulAction.orbitRel.Quotient G S

private theorem freeOrbitQuotient_smul (g : G) (s : S) :
    (Quotient.mk'' (g • s) : freeOrbitIndex (G := G) (S := S)) = Quotient.mk'' s :=
  Quotient.sound ⟨g, rfl⟩

def freeOrbitEquiv (hfree : ∀ (g : G) (s : S), g • s = s → g = (1 : G)) :
    (G × freeOrbitIndex (G := G) (S := S)) ≃ S :=
  Equiv.ofBijective (fun p => p.1 • p.2.out) (by
    constructor
    · rintro ⟨g, i⟩ ⟨h, j⟩ he
      have hi : i = j := by
        have := congrArg (fun s =>
          (Quotient.mk'' s : freeOrbitIndex (G := G) (S := S))) he
        simpa only [freeOrbitQuotient_smul, Quotient.out_eq'] using this
      subst j
      change g • i.out = h • i.out at he
      refine Prod.ext ?_ rfl
      have hf : (h⁻¹*g) • i.out = i.out := by
        rw [mul_smul, he, inv_smul_smul]
      have hg := hfree (h⁻¹*g) i.out hf
      exact (inv_mul_eq_one.mp hg).symm
    · intro s
      let i : freeOrbitIndex (G := G) (S := S) := Quotient.mk'' s
      have hi' : (Quotient.mk'' i.out : freeOrbitIndex (G := G) (S := S)) =
          Quotient.mk'' s := Quotient.out_eq' i
      have hi : s ∈ MulAction.orbit G i.out := Quotient.exact hi'.symm
      obtain ⟨g, hg⟩ := hi
      exact ⟨(g, i), hg⟩)

@[simp] theorem freeOrbitEquiv_apply
    (hfree : ∀ (g : G) (s : S), g • s = s → g = (1 : G))
    (g : G) (i : freeOrbitIndex (G := G) (S := S)) :
    freeOrbitEquiv hfree (g, i) = g • i.out := rfl

theorem freeOrbitEquiv_mul
    (hfree : ∀ (g : G) (s : S), g • s = s → g = (1 : G))
    (g h : G) (i : freeOrbitIndex (G := G) (S := S)) :
    freeOrbitEquiv hfree (g*h, i) = g • freeOrbitEquiv hfree (h, i) :=
  mul_smul g h i.out

variable (R : Type) [CommRing R] [AddCommGroup M] [Module R M]

def freeOrbitBasis (B : Module.Basis S R M)
    (hfree : ∀ (g : G) (s : S), g • s = s → g = (1 : G)) :
    Module.Basis (G × freeOrbitIndex (G := G) (S := S)) R M :=
  B.reindex (freeOrbitEquiv hfree).symm

theorem freeOrbitBasis_relabel (B : Module.Basis S R M)
    (hfree : ∀ (g : G) (s : S), g • s = s → g = (1 : G))
    (ρ : G → Module.End R M)
    (hB : ∀ g s, ρ g (B s) = B (g • s))
    (g h : G) (i : freeOrbitIndex (G := G) (S := S)) :
    ρ g (freeOrbitBasis R B hfree (h, i)) = freeOrbitBasis R B hfree (g*h, i) := by
  simp only [freeOrbitBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    freeOrbitEquiv_mul]
  exact hB g (freeOrbitEquiv hfree (h, i))

end FreeOrbit

end NRR.PrimePowerTopology
