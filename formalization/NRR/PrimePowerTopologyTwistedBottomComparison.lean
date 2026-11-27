import NRR.PrimePowerTopologyTwistedCycleLifting

/-! In the bottom possible degree of a complex free on group orbits,
every character-covariant ordinary homology map factors uniquely through
the actual twisted homology projection. -/

noncomputable section
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {R G : Type} [CommRing R] [Group G]
variable {K : ChainComplex (ModuleCat R) ℕ} (ρ : G → (K ⟶ K))

private theorem equivariantCycleRetract_of_projector (q : ℕ) (p : K.X q ⟶ K.X q)
    (hp : p ≫ K.d q (q-1) = 0) (hfix : K.iCycles q ≫ p = K.iCycles q)
    (he : ∀ g, (ρ g).f q ≫ p = p ≫ (ρ g).f q) :
    ∃ r : K.X q ⟶ K.cycles q, K.iCycles q ≫ r = 𝟙 _ ∧
      ∀ g, (ρ g).f q ≫ r = r ≫ HomologicalComplex.cyclesMap (ρ g) q := by
  have hn : (ComplexShape.down ℕ).next q = q-1 := by cases q <;> simp
  let r := K.liftCycles p (q-1) hn hp
  have hr : r ≫ K.iCycles q = p := K.liftCycles_i p (q-1) hn hp
  refine ⟨r, (cancel_mono (K.iCycles q)).mp ?_, ?_⟩
  · rw [Category.assoc, hr, hfix, Category.id_comp]
  · intro g
    apply (cancel_mono (K.iCycles q)).mp
    rw [Category.assoc, hr, Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hr, he]

private theorem exists_equivariantCycleRetract (q : ℕ)
    (fill : ∀ i < q, ∃ s : K.X i ⟶ K.X (i+1),
      (∀ g, (ρ g).f i ≫ s = s ≫ (ρ g).f (i+1)) ∧
      ∀ z : K.X i, K.d i (i-1) z = 0 → K.d (i+1) i (s z) = z) :
    ∃ r : K.X q ⟶ K.cycles q, K.iCycles q ≫ r = 𝟙 _ ∧
      ∀ g, (ρ g).f q ≫ r = r ≫ HomologicalComplex.cyclesMap (ρ g) q := by
  cases q with
  | zero =>
      apply equivariantCycleRetract_of_projector ρ 0 (𝟙 _)
      · rw [K.shape 0 0 (by decide), comp_zero]
      · simp
      · simp
  | succ i =>
      obtain ⟨s, hs, h⟩ := fill i (Nat.lt_succ_self i)
      let D := K.d (i+1) i
      apply equivariantCycleRetract_of_projector ρ (i+1) (𝟙 _ - D ≫ s)
      · ext x
        change D (x - s (D x)) = 0
        rw [map_sub, h (D x) (congrArg (fun f : K.X (i+1) ⟶ K.X (i-1) => f x)
          (K.d_comp_d (i+1) i (i-1))), sub_self]
      · rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
          K.iCycles_d, zero_comp, sub_zero]
      · intro g
        rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
          Category.id_comp, ← Category.assoc, (ρ g).comm (i+1) i, Category.assoc, hs,
          Category.assoc]

variable (χ : G →* Rˣ)

private theorem chainActionRelations_comp_zero_of_character {q : ℕ} {M : ModuleCat R}
    (φ : K.X q ⟶ M) (hφ : ∀ g, (ρ g).f q ≫ φ = (χ g : R) • φ) :
    (chainActionRelations R χ K ρ).f q ≫ φ = 0 := by
  apply (isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) q)
    (coproductIsCoproduct (fun _g : G => K))).hom_ext
  rintro ⟨g⟩
  change (Sigma.ι (fun _g : G => K) g).f q ≫ (chainActionRelations R χ K ρ).f q ≫ φ = _ ≫ 0
  rw [comp_zero, ← Category.assoc, ← HomologicalComplex.comp_f,
    show Sigma.ι (fun _g : G => K) g ≫ chainActionRelations R χ K ρ =
      chainActionRelation R χ K ρ g from Sigma.ι_desc _ _]
  simp only [chainActionRelation, HomologicalComplex.sub_f_apply,
    HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, Preadditive.sub_comp,
    Linear.smul_comp, Category.id_comp, hφ, sub_self]

/-- A character-covariant map out of ordinary homology descends uniquely
to the homology of the twisted chain cokernel at its first possible degree. -/
theorem existsUnique_twistedHomology_desc_of_free_orbits
    (law : ∀ g h, ρ (g*h) = ρ h ≫ ρ g) {I : ℕ → Type*}
    (b : ∀ i, Module.Basis (G × I i) R (K.X i))
    (hb : ∀ i g h a, (ρ g).f i (b i (h,a)) = b i (g*h,a))
    (q : ℕ) (hK : ∀ i < q, IsZero (K.homology i)) {M : ModuleCat R}
    (u : K.homology q ⟶ M)
    (hu : ∀ g, HomologicalComplex.homologyMap (ρ g) q ≫ u = (χ g : R) • u) :
    ∃! ψ : (twistedChainComplex R χ K ρ).homology q ⟶ M,
      HomologicalComplex.homologyMap (twistedChainProj R χ K ρ) q ≫ ψ = u := by
  let T := twistedChainComplex R χ K ρ
  let π := twistedChainProj R χ K ρ
  obtain ⟨r,hr,hrg⟩ := exists_equivariantCycleRetract ρ q
    (exists_equivariantBoundarySection_of_basis ρ law b hb q hK)
  let φ := r ≫ K.homologyπ q ≫ u
  have he (g : G) : (ρ g).f q ≫ φ = (χ g : R) • φ := by
    change (ρ g).f q ≫ r ≫ K.homologyπ q ≫ u = _
    rw [← Category.assoc, hrg, Category.assoc, ← Category.assoc _ (K.homologyπ q),
      ← HomologicalComplex.homologyπ_naturality, Category.assoc, hu,
      Linear.comp_smul, Linear.comp_smul]
  let φ' : T.X q ⟶ M := cokDesc R (chainActionRelations R χ K ρ) q φ
    (chainActionRelations_comp_zero_of_character ρ χ φ he)
  have hφ : π.f q ≫ φ' = φ := π_cokDesc R _ _ _ _
  have hd : K.d (q+1) q ≫ φ = 0 := by
    change K.d (q+1) q ≫ r ≫ K.homologyπ q ≫ u = 0
    rw [← K.toCycles_i (q+1) q, Category.assoc, ← Category.assoc (K.iCycles q),
      hr, Category.id_comp, K.toCycles_comp_homologyπ_assoc, zero_comp]
  have hd' : T.d (q+1) q ≫ φ' = 0 := by
    have hπ : Epi (π.f (q+1)) :=
      inferInstanceAs (Epi ((cokernel.π (chainActionRelations R χ K ρ)).f (q+1)))
    apply hπ.left_cancellation
    rw [← Category.assoc, π.comm, Category.assoc, hφ, hd, comp_zero]
  let ψ := T.homologyι q ≫ T.descOpcycles' φ' (q+1) rfl hd'
  have hψ : HomologicalComplex.homologyMap π q ≫ ψ = u := by
    apply (cancel_epi (K.homologyπ q)).mp
    change K.homologyπ q ≫ HomologicalComplex.homologyMap π q ≫
      T.homologyι q ≫ T.descOpcycles' φ' (q+1) rfl hd' = _
    rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc (T.homologyπ q),
      T.homology_π_ι, Category.assoc, T.p_descOpcycles, ← Category.assoc,
      HomologicalComplex.cyclesMap_i, Category.assoc, hφ]
    change K.iCycles q ≫ r ≫ K.homologyπ q ≫ u = _
    rw [← Category.assoc, hr, Category.id_comp]
  have hπ : Epi (HomologicalComplex.homologyMap π q) :=
    epi_twistedProjection_of_free_orbits χ ρ law b hb q hK
  exact ⟨ψ, hψ, fun v h => hπ.left_cancellation v ψ (h.trans hψ.symm)⟩

/-- A character-covariant ordinary detector nonzero on a cycle detects its
image in twisted homology at the first possible degree. -/
theorem twistedProjection_ne_zero_of_covariant_detector
    (law : ∀ g h, ρ (g*h) = ρ h ≫ ρ g) {I : ℕ → Type*}
    (b : ∀ i, Module.Basis (G × I i) R (K.X i))
    (hb : ∀ i g h a, (ρ g).f i (b i (h,a)) = b i (g*h,a))
    (q : ℕ) (hK : ∀ i < q, IsZero (K.homology i)) {M : ModuleCat R}
    (u : K.homology q ⟶ M)
    (hu : ∀ g, HomologicalComplex.homologyMap (ρ g) q ≫ u = (χ g : R) • u)
    (x : K.homology q) (hx : u x ≠ 0) :
    HomologicalComplex.homologyMap (twistedChainProj R χ K ρ) q x ≠ 0 := by
  obtain ⟨ψ, he, _⟩ := existsUnique_twistedHomology_desc_of_free_orbits ρ χ law b hb q hK u hu
  intro hz
  apply hx
  rw [← he, ModuleCat.comp_apply, hz, map_zero]

end NRR.PrimePowerTopology
