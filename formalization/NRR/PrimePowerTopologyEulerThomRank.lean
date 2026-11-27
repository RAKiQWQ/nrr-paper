import NRR.PrimePowerTopologyEulerThomChambers

/-! The compactified point-relative normal model has one twisted generator
in the ambient configuration degree. Geometric maps in the factorization
are induced by the based open collapse and the proper closed inclusion. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology
namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]

/-- The split lowest Fuks generator spans its whole twisted group. -/
def minimalTwistedRankOne (χ : ConfigurationGroup n →* Rˣ) (hd : 0 < d)
    (hn : 2 ≤ n) (i₀ : Fin n) :
    ModuleCat.of R R ≅ (twistedFuksRelativeComplex R (d := d) χ (Nat.sub_le d 1)).homology (d+n) := by
  let f := coherentTwistedMinimalMap R χ hd i₀
  let π := HomologicalComplex.homologyMap (twistedFuksRelativeProj R (d := d) χ (Nat.sub_le d 1)) (d+n)
  letI : Epi π := by
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    exact epi_twistedFuksRelativeProj_through_cell_degree R χ hn (le_refl _)
  letI : Epi f := (ModuleCat.epi_iff_surjective _).mpr (by
    intro z
    obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
    let c := ∑ g : ConfigurationGroup n, coherentMinimalRelativeCoefficient R hd i₀ g y * (χ g : R)
    refine ⟨c,?_⟩
    change f c = π y
    rw [show π y = c • f 1 from minimalTwistedProjection_eq_character_sum R χ hd i₀ y]
    simpa only [smul_eq_mul,mul_one] using (f.hom.map_smul c (1 : R)))
  letI : Mono f := (ModuleCat.mono_iff_injective _).mpr (coherentTwistedMinimalMap_injective R χ hd i₀)
  letI := isIso_of_mono_of_epi f
  exact asIso f

abbrev verticalNormalPointIncl (d n : ℕ) [NeZero n] :=
  homologyPointIncl (X := TopCat.of (OnePoint (VerticalAssociated d n))) ∞

theorem verticalNormalPointIncl_equivariant (g : ConfigurationGroup n) :
    verticalNormalPointIncl d n ≫ canonicalEulerThomRelabelMap g =
      𝟙 _ ≫ verticalNormalPointIncl d n := rfl

def verticalNormalPointAction (g : ConfigurationGroup n) :=
  relComplexMap R (verticalNormalPointIncl d n) (verticalNormalPointIncl d n)
    (verticalNormalPointIncl_equivariant g)

def verticalNormalPointTwisted (χ : ConfigurationGroup n →* Rˣ) :=
  twistedChainComplex R χ (relComplex R (verticalNormalPointIncl d n))
    (verticalNormalPointAction R)

private def minimalLowerPoint (D n : ℕ) [NeZero n] (hD : 0 < D) :
    Unit ≃ₜ compactifiedFuksLevel D n (D-1) where
  toFun _ := ⟨∞,Or.inl rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact ((compactifiedFuksLevel_eq_infty_of_lt (d := D) (n := n)
      (by omega : D-1 < D)).subset x.property : x.val = ∞).symm
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The equivariant comparison is an isomorphism before taking homology. -/
def verticalNormalTwistedMinimalIso (χ : ConfigurationGroup n →* Rˣ)
    (hd : 0 < d) (i₀ : Fin n) :
    verticalNormalPointTwisted R (d := d) χ ≅
      twistedFuksRelativeComplex R (d := d*n) χ (Nat.sub_le (d*n) 1) := by
  let h := Nat.sub_le (d*n) 1
  let i := verticalNormalPointIncl d n
  let j := compactifiedFuksInclusion (d := d*n) (n := n) h
  let u := TopCat.isoOfHomeo (X := TopCat.of Unit)
    (Y := TopCat.of (compactifiedFuksLevel (d*n) n (d*n-1)))
    (minimalLowerPoint (d*n) n (Nat.mul_pos hd (NeZero.pos n)))
  let v := TopCat.isoOfHomeo (X := TopCat.of (OnePoint (VerticalAssociated d n)))
    (Y := TopCat.of (compactifiedFuksLevel (d*n) n (d*n))) (verticalAssociatedMinimalLevel i₀)
  have w : i ≫ v.hom = u.hom ≫ j := rfl
  let e := singularPairChainIso (R := R) i j u v w
  apply twistedChainIsoOfEquivariant χ (verticalNormalPointAction R) (fuksRelativeRelabel R h) e
  intro g
  change relComplexMap R i i _ ≫ relComplexMap R i j w = relComplexMap R i j w ≫ relComplexMap R j j _
  apply relativeSingularChainMap_equivariant R i j (fun _ => 𝟙 _) canonicalEulerThomRelabelMap
    (fun g => compactifiedFuksRelabelMap g) (fun g => compactifiedFuksRelabelMap g)
    verticalNormalPointIncl_equivariant (compactifiedFuksInclusion_equivariant h) w
  intro σ
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact verticalAssociatedMinimalLevel_relabel i₀ σ

def verticalNormalTopIso (χ : ConfigurationGroup n →* Rˣ) (hd : 0 < d)
    (hn : 2 ≤ n) (i₀ : Fin n) :
    ModuleCat.of R R ≅ (verticalNormalPointTwisted R (d := d) χ).homology (d*n+n) :=
  minimalTwistedRankOne R χ (Nat.mul_pos hd (NeZero.pos n)) hn i₀ ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) (d*n+n)).mapIso
      (verticalNormalTwistedMinimalIso R χ hd i₀)).symm

theorem verticalNormalCollapse_square :
    associatedBMSourceIncl (d+1) n ≫ TopCat.ofHom canonicalEulerThomCollapse =
      homologyPointCollapse _ ≫ verticalNormalPointIncl d n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨z,hz⟩
  have he : z = ∞ := hz
  subst z
  rfl

def verticalNormalTwistedCollapse (χ : ConfigurationGroup n →* Rˣ) :
    associatedBMTwistedSource R (d := d+1) χ ⟶ verticalNormalPointTwisted R (d := d) χ :=
  twistedChainMap R χ _ (associatedBMSourceRelativeAction R) (verticalNormalPointAction R)
    (relComplexMap R _ _ verticalNormalCollapse_square)
    (relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) associatedBMSourceRelabelMap
      (fun _ => 𝟙 _) canonicalEulerThomRelabelMap associatedBMSourceIncl_equivariant
      verticalNormalPointIncl_equivariant verticalNormalCollapse_square canonicalEulerThomCollapseMap_equivariant)

theorem verticalNormalInclude_square :
    verticalNormalPointIncl d n ≫ TopCat.ofHom canonicalEulerThomIncludeCompact =
      homologyPointIncl (X := TopCat.of (associatedBMComplement (d+1) n))
        ⟨∞,associatedBMComplement_infty _ _⟩ ≫ associatedBMTargetIncl (d+1) n := rfl

def verticalNormalTwistedInclude (χ : ConfigurationGroup n →* Rˣ) :
    verticalNormalPointTwisted R (d := d) χ ⟶ associatedBMTwistedTarget R (d := d+1) χ :=
  twistedChainMap R χ _ (verticalNormalPointAction R) (associatedBMTargetRelativeAction R)
    (relComplexMap R _ _ verticalNormalInclude_square)
    (relativeSingularChainMap_equivariant R _ _ (fun _ => 𝟙 _) canonicalEulerThomRelabelMap
      associatedBMComplementRelabelMap associatedBMCoverRelabelMap verticalNormalPointIncl_equivariant
      associatedBMTargetIncl_equivariant verticalNormalInclude_square canonicalEulerThomIncludeMap_equivariant)

/-- The global Euler homomorphism factors through the compactified
point-relative normal model, whose top group is explicitly rank one. -/
theorem associatedBMTwistedEulerMap_eq_pointNormal (χ : ConfigurationGroup n →* Rˣ) (q : ℕ) :
    associatedBMTwistedEulerMap R (d := d+1) χ q =
      HomologicalComplex.homologyMap (verticalNormalTwistedCollapse R χ) q ≫
        HomologicalComplex.homologyMap (verticalNormalTwistedInclude R χ) q := by
  rw [associatedBMTwistedEulerMap_eq_vertical, ← HomologicalComplex.homologyMap_comp]
  congr 1
  symm
  let π := twistedChainProj R χ _ (associatedBMSourceRelativeAction R (d := d+1))
  have hπ : Epi π := coequalizer.π_epi
  apply hπ.left_cancellation
  change twistedChainProj R χ _ _ ≫ twistedChainMap R χ _ _ _ _ _ ≫ twistedChainMap R χ _ _ _ _ _ =
    twistedChainProj R χ _ _ ≫ twistedChainMap R χ _ _ _ _ _
  rw [twistedChainProj_map_assoc, twistedChainProj_map, twistedChainProj_map,
    ← Category.assoc,relComplexMap_comp]
  congr 2
  exact canonicalEulerVertical_eq_thom_factor.symm

end NRR.PrimePowerTopology
