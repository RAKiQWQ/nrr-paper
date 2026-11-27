import NRR.PrimePowerTopologyTwistedHomotopy
import NRR.SingularHomologySimplicial
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! Equivariant degreewise splittings on the actual singular simplex
basis. The splittings are established before forming twisted coinvariants,
so no semisimplicity assumption on prime coefficients is involved. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

/-- The simplex-support retraction is genuinely equivariant under
automorphisms preserving the included simplicial subset. The unique lift
of a simplex is used; no averaging or arbitrary complement is selected. -/
theorem simplicialRetraction_equivariant {A X : SSet.{0}} (i : A ⟶ X)
    (a : A ⟶ A) (b : X ⟶ X) [IsIso a] [IsIso b]
    (comm : i ≫ b = a ≫ i) (n : ℕ)
    (injective : Function.Injective (i.app (op ⦋n⦌))) :
    (simplicialChainMap R b).f n ≫ mvRetr R i n =
      mvRetr R i n ≫ (simplicialChainMap R a).f n := by
  have natural (z : A _⦋n⦌) : b.app _ (i.app _ z) = i.app _ (a.app _ z) := by
    exact congrArg (fun u => u z) (NatTrans.congr_app comm (op ⦋n⦌))
  have asurj : Function.Surjective (a.app (op ⦋n⦌)) :=
    (CategoryTheory.isIso_iff_bijective (a.app (op ⦋n⦌))).mp inferInstance |>.surjective
  have binj : Function.Injective (b.app (op ⦋n⦌)) :=
    (CategoryTheory.isIso_iff_bijective (b.app (op ⦋n⦌))).mp inferInstance |>.injective
  apply simplicialChain_hom_ext R
  intro y
  by_cases hy : ∃ z,i.app (op ⦋n⦌) z = y
  · obtain ⟨z,rfl⟩ := hy
    rw [simplexι_chainMap_f_assoc,natural,ι_mvRetr R i injective,
      ι_mvRetr_assoc R i injective,simplexι_chainMap_f]
  · have hby : ¬ ∃ z,i.app (op ⦋n⦌) z = b.app (op ⦋n⦌) y := by
      rintro ⟨z,hz⟩
      obtain ⟨u,rfl⟩ := asurj z
      exact hy ⟨u,binj ((natural u).trans hz)⟩
    rw [simplexι_chainMap_f_assoc,ι_mvRetr_of_not_mem R i _ hby,
      ι_mvRetr_of_not_mem_assoc R i _ hy,zero_comp]

section CoinvariantSplitting

variable {G : Type} [Group G] (χ : G →* Rˣ)
  {K L : ChainComplex (ModuleCat R) ℕ}
  (ρ : G → (K ⟶ K)) (τ : G → (L ⟶ L))

private theorem chainRelation_comp_equivariantComponent
    {i j : ℕ} (r : L.X i ⟶ K.X j)
    (equiv : ∀ g,(τ g).f i ≫ r = r ≫ (ρ g).f j) :
    (chainActionRelations R χ L τ).f i ≫ r ≫
      (twistedChainProj R χ K ρ).f j = 0 := by
  apply (isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i)
    (coproductIsCoproduct (fun _g : G => L))).hom_ext
  intro ⟨g⟩
  simp only [Functor.mapCocone_ι_app,HomologicalComplex.eval_map]
  have hi : (Sigma.ι (fun _g : G => L) g).f i ≫
      (chainActionRelations R χ L τ).f i = (chainActionRelation R χ L τ g).f i := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun m => m.f i) (Sigma.ι_desc (chainActionRelation R χ L τ) g)
  change (Sigma.ι (fun _g : G => L) g).f i ≫
    (chainActionRelations R χ L τ).f i ≫ r ≫
      (twistedChainProj R χ K ρ).f j = 0
  rw [← Category.assoc,hi]
  simp only [chainActionRelation,HomologicalComplex.sub_f_apply,
    HomologicalComplex.smul_f_apply,HomologicalComplex.id_f,Preadditive.sub_comp,
    Linear.smul_comp,Category.id_comp]
  have hπ := congrArg (fun m => m.f j) (chainAction_proj R χ K ρ g)
  simp only [HomologicalComplex.comp_f,HomologicalComplex.smul_f_apply] at hπ
  change (ρ g).f j ≫ (twistedChainProj R χ K ρ).f j =
    (χ g : R) • (twistedChainProj R χ K ρ).f j at hπ
  rw [← Category.assoc, equiv g, Category.assoc, hπ, Linear.comp_smul, sub_self]

/-- Descend an equivariant map between two chain modules in arbitrary degrees. -/
def twistedComponentMap {i j : ℕ} (r : L.X i ⟶ K.X j)
    (equiv : ∀ g, (τ g).f i ≫ r = r ≫ (ρ g).f j) :
    (twistedChainComplex R χ L τ).X i ⟶ (twistedChainComplex R χ K ρ).X j :=
  cokDesc R (chainActionRelations R χ L τ) i
    (r ≫ (twistedChainProj R χ K ρ).f j)
    (chainRelation_comp_equivariantComponent R χ ρ τ r equiv)

@[reassoc (attr := simp)] theorem twistedProj_componentMap {i j : ℕ} (r : L.X i ⟶ K.X j)
    (equiv : ∀ g, (τ g).f i ≫ r = r ≫ (ρ g).f j) :
    (twistedChainProj R χ L τ).f i ≫ twistedComponentMap R χ ρ τ r equiv =
      r ≫ (twistedChainProj R χ K ρ).f j := π_cokDesc R _ _ _ _

/-- Descend an equivariant degreewise linear map through the actual
orientation-twisted chain quotients. The descended family need not itself
be a chain map; it is the module-level operation used for split exactness. -/
def twistedDegreeMap (r : ∀ n,L.X n ⟶ K.X n)
    (equiv : ∀ g n,(τ g).f n ≫ r n = r n ≫ (ρ g).f n) (n : ℕ) :
    (twistedChainComplex R χ L τ).X n ⟶ (twistedChainComplex R χ K ρ).X n :=
  twistedComponentMap R χ ρ τ (r n) (fun g => equiv g n)

@[reassoc (attr := simp)] theorem twistedProj_degreeMap
    (r : ∀ n,L.X n ⟶ K.X n)
    (equiv : ∀ g n,(τ g).f n ≫ r n = r n ≫ (ρ g).f n) (n : ℕ) :
    (twistedChainProj R χ L τ).f n ≫ twistedDegreeMap R χ ρ τ r equiv n =
      r n ≫ (twistedChainProj R χ K ρ).f n :=
  twistedProj_componentMap R χ ρ τ (r n) (fun g => equiv g n)

end CoinvariantSplitting

section Exactness

variable {G : Type} [Group G] (χ : G →* Rˣ)

/-- An equivariant retraction in each chain degree suffices for injectivity
after passing to twisted coinvariants. -/
theorem mono_twistedChainMap_of_retraction
    {K L : ChainComplex (ModuleCat R) ℕ} (ρ : G → (K ⟶ K)) (τ : G → (L ⟶ L))
    (f : K ⟶ L) (hf : ∀ a, ρ a ≫ f = f ≫ τ a)
    (r : ∀ n, L.X n ⟶ K.X n) (hr : ∀ a n, (τ a).f n ≫ r n = r n ≫ (ρ a).f n)
    (split : ∀ n, f.f n ≫ r n = 𝟙 _) : Mono (twistedChainMap R χ K ρ τ f hf) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  suffices h : (twistedChainMap R χ K ρ τ f hf).f n ≫ twistedDegreeMap R χ ρ τ r hr n =
      𝟙 _ from mono_of_mono_fac h
  have hπ : Epi ((twistedChainProj R χ K ρ).f n) :=
    inferInstanceAs (Epi ((cokernel.π (chainActionRelations R χ K ρ)).f n))
  apply hπ.left_cancellation
  have fac := congrArg (fun u => u.f n) (twistedChainProj_map R χ K ρ τ f hf)
  simp only [HomologicalComplex.comp_f] at fac
  rw [← Category.assoc, fac, Category.assoc, twistedProj_degreeMap,
    ← Category.assoc, split, Category.id_comp, Category.comp_id]

variable (S : ShortComplex (ChainComplex (ModuleCat R) ℕ))
    (α : G → (S.X₁ ⟶ S.X₁)) (β : G → (S.X₂ ⟶ S.X₂)) (γ : G → (S.X₃ ⟶ S.X₃))
    (hf : ∀ a, α a ≫ S.f = S.f ≫ β a) (hg : ∀ a, β a ≫ S.g = S.g ≫ γ a)

def twistedShortComplex : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (twistedChainMap R χ _ α β S.f hf) (twistedChainMap R χ _ β γ S.g hg) (by
    have hπ : Epi (twistedChainProj R χ _ α) := coequalizer.π_epi
    apply hπ.left_cancellation
    rw [twistedChainProj_map_assoc, twistedChainProj_map, ← Category.assoc, S.zero,
      zero_comp, comp_zero])

/-- Twisted coinvariants preserve a cokernel. The two quotient operations
are justified by their universal properties over the coefficient ring. -/
theorem twistedShortComplex_exact (hs : S.Exact) [Epi S.g] :
    (twistedShortComplex R χ S α β γ hf hg).Exact ∧
      Epi (twistedShortComplex R χ S α β γ hf hg).g := by
  let T := twistedShortComplex R χ S α β γ hf hg
  let πα := twistedChainProj R χ _ α
  let πβ := twistedChainProj R χ _ β
  let πγ := twistedChainProj R χ _ γ
  letI : Epi πβ := coequalizer.π_epi
  letI : Epi πγ := coequalizer.π_epi
  have fac₁ : πα ≫ T.f = S.f ≫ πβ := twistedChainProj_map R χ _ α β S.f hf
  have fac₂ : πβ ≫ T.g = S.g ≫ πγ := twistedChainProj_map R χ _ β γ S.g hg
  letI : Epi T.g := epi_of_epi_fac fac₂
  apply T.exact_and_epi_g_iff_g_is_cokernel.mpr
  refine ⟨CokernelCofork.IsColimit.ofπ' T.g T.zero ?_⟩
  intro Z k hk
  have vanishes : S.f ≫ πβ ≫ k = 0 := by
    rw [← Category.assoc, ← fac₁, Category.assoc, hk, comp_zero]
  let l := hs.desc (πβ ≫ k) vanishes
  have hl : S.g ≫ l = πβ ≫ k := hs.g_desc _ _
  have hχ (a : G) : γ a ≫ l = (χ a : R) • l := by
    apply (cancel_epi S.g).mp
    rw [← Category.assoc, ← hg a, Category.assoc, Linear.comp_smul, hl, ← Category.assoc]
    change (β a ≫ twistedChainProj R χ _ β) ≫ k = _
    rw [chainAction_proj, Linear.smul_comp]
  have relations : chainActionRelations R χ _ γ ≫ l = 0 := by
    apply Sigma.hom_ext
    intro a
    simp only [← Category.assoc, chainActionRelations, Sigma.ι_desc, comp_zero,
      chainActionRelation, Preadditive.sub_comp, Linear.smul_comp, Category.id_comp, hχ, sub_self]
  refine ⟨cokernel.desc _ l relations, ?_⟩
  apply (cancel_epi πβ).mp
  rw [← Category.assoc, fac₂, Category.assoc]
  change S.g ≫ cokernel.π _ ≫ cokernel.desc _ l relations = _
  rw [cokernel.π_desc, hl]

end Exactness

end NRR.PrimePowerTopology
