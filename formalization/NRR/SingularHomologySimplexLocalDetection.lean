import NRR.SingularHomologySimplexColoring
import NRR.SingularHomologyRelHomotopy

/-! Explicit split detection of the identity simplex class relative to
any subspace containing its boundary and covered by the color-avoiding
coordinate neighborhoods. In particular the subspace may be the puncture
at the uniform barycenter. -/

noncomputable section
set_option maxHeartbeats 300000
open Set Topology CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open NRR.SingularHomology.SimplexGeometry

namespace NRR.SingularHomology.SimplexFundamental

theorem faceMapC_coordinate_self (n : ℕ) (i : Fin (n+2)) (x : GeometricSimplex n) :
    faceMapC n i x i = 0 := by
  simp [faceMapC, SimplexCategory.coe_toTopMap]
  intro j h
  exact False.elim (Fin.succAbove_ne i j h)

theorem boundary_exists_zero {n : ℕ} (x : boundary n) : ∃ i : Fin (n+1), x.val i = 0 := by
  cases n with
  | zero => exact False.elim x.property
  | succ n =>
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp x.property
    exact ⟨i, hy ▸ faceMapC_coordinate_self n i y⟩

structure ColoringSubspace (n : ℕ) where
  carrier : Set (GeometricSimplex n)
  boundary_subset : boundary n ⊆ carrier
  small : ∀ x : carrier, ∃ i : Fin (n+1), (x.val i : ℝ) < (1 : ℝ)/(n+1)

namespace ColoringSubspace

variable {n : ℕ} (P : ColoringSubspace n)

def incl : TopCat.of P.carrier ⟶ TopCat.of (GeometricSimplex n) :=
  subIncl (Y := TopCat.of (GeometricSimplex n)) P.carrier

instance : Mono P.incl := inferInstanceAs (Mono (subIncl (Y := TopCat.of (GeometricSimplex n)) P.carrier))

def fromBoundary : TopCat.of (boundary n) ⟶ TopCat.of P.carrier :=
  TopCat.ofHom ⟨fun x => ⟨x.val, P.boundary_subset x.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem square : boundaryIncl n ≫ 𝟙 _ = P.fromBoundary ≫ P.incl := rfl

def cover (i : Fin (n+1)) : Set P.carrier := {x | (x.val i : ℝ) < (1 : ℝ)/(n+1)}

theorem isOpen_cover (i : Fin (n+1)) : IsOpen (P.cover i) := by
  apply isOpen_lt _ continuous_const
  exact NNReal.continuous_coe.comp ((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_subtype_val))

theorem cover_condition : SmallSimplicesCondition (X := TopCat.of P.carrier) P.cover := by
  constructor
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := P.small x
  exact Set.mem_iUnion.mpr ⟨i, (P.isOpen_cover i).interior_eq.symm ▸ hi⟩

variable (R : Type) [CommRing R]

def smallIncl : smallChainComplex R (X := TopCat.of P.carrier) P.cover ⟶
    Csing R (TopCat.of (GeometricSimplex n)) :=
  smallChainIncl R (X := TopCat.of P.carrier) P.cover ≫ CsingMap R P.incl

instance : Mono (P.smallIncl R) := by unfold smallIncl; infer_instance

abbrev smallRelative := cokernel (P.smallIncl R)

def proj : Csing R (TopCat.of (GeometricSimplex n)) ⟶ P.smallRelative R := cokernel.π (P.smallIncl R)

def toRelative : P.smallRelative R ⟶ relComplex R P.incl :=
  cokernel.map (P.smallIncl R) (CsingMap R P.incl) (smallChainIncl R (X := TopCat.of P.carrier) P.cover) (𝟙 _)
    (by simp [smallIncl])

@[reassoc (attr := simp)] theorem proj_toRelative :
    P.proj R ≫ P.toRelative R = relProj R P.incl := cokernel.π_desc _ _ _

def shortComplex : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (P.smallIncl R) (P.proj R) (cokernel.condition _)

theorem shortExact : (P.shortComplex R).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by change Mono (P.smallIncl R); infer_instance
  epi_g := coequalizer.π_epi

def shortComplexMap : P.shortComplex R ⟶ relShortComplex R P.incl where
  τ₁ := smallChainIncl R (X := TopCat.of P.carrier) P.cover
  τ₂ := 𝟙 _
  τ₃ := P.toRelative R
  comm₁₂ := by simp [shortComplex, smallIncl, relShortComplex]
  comm₂₃ := (P.proj_toRelative R).symm

theorem isIso_toRelative (k : ℕ) : IsIso (HomologicalComplex.homologyMap (P.toRelative R) k) := by
  have h₁ : QuasiIso (P.shortComplexMap R).τ₁ := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_smallChainIncl_homologyMap R (X := TopCat.of P.carrier) P.cover P.cover_condition k
  have h₂ : QuasiIso (P.shortComplexMap R).τ₂ := by change QuasiIso (𝟙 _); infer_instance
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (P.shortComplexMap R) (P.shortExact R) (relShortComplex_shortExact R P.incl) h₁ h₂
  exact (quasiIsoAt_iff_isIso_homologyMap _ k).mp ((quasiIso_iff _).mp h k)

theorem smallIncl_coloring : (P.smallIncl R).f n ≫ coloringCochain R n = 0 := by
  apply simplicialChain_hom_ext R
  intro s
  rw [smallIncl, HomologicalComplex.comp_f, smallChainIncl, Category.assoc, simplexι_chainMap_f_assoc,
    simplexι_CsingMap_f_assoc, simplexι_coloringCochain, comp_zero]
  obtain ⟨i, hi⟩ := (mem_smallSubcomplex_iff (X := TopCat.of P.carrier) (U := P.cover) s.val).mp s.property
  have hz : colorOrientation R (simplexVertexColors ((TopCat.toSSet.map P.incl).app _ s.val)) = 0 := by
    apply colorOrientation_eq_zero_of_omitted R _ i
    intro j
    apply barycentricColor_ne_of_small
    exact hi ⟨vertex n j, rfl⟩
  change ModuleCat.ofHom (colorOrientation R (simplexVertexColors
    ((TopCat.toSSet.map P.incl).app _ s.val)) • LinearMap.id) = 0
  rw [hz, zero_smul]
  rfl

def faceSimplex {m : ℕ} (P : ColoringSubspace (m+1)) (i : Fin (m+2)) :
    (TopCat.toSSet.obj (TopCat.of P.carrier)).obj (op ⦋m⦌) :=
  (TopCat.toSSet.map P.fromBoundary).app _ (faceSingularSimplex m i)

theorem faceSimplex_topMap {m : ℕ} (P : ColoringSubspace (m+1)) (i : Fin (m+2)) :
    TopCat.toSSetObjEquiv _ _ (P.faceSimplex i) = P.fromBoundary.hom.comp (faceToBoundary m i) := rfl

theorem faceSimplex_small {m : ℕ} (P : ColoringSubspace (m+1)) (i : Fin (m+2)) :
    P.faceSimplex i ∈ (smallSubcomplex (X := TopCat.of P.carrier) P.cover).obj (op ⦋m⦌) := by
  rw [mem_smallSubcomplex_iff]
  refine ⟨i, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [P.faceSimplex_topMap]
  change (faceMapC m i x i : ℝ) < (1 : ℝ)/(↑(m+1)+1)
  rw [faceMapC_coordinate_self, NNReal.coe_zero]
  positivity

theorem identity_small_cycle : identityChain R n ≫ (P.proj R).f n ≫
    (P.smallRelative R).d n (n-1) = 0 := by
  cases n with
  | zero => simp
  | succ m =>
    change identityChain R (m+1) ≫ (P.proj R).f (m+1) ≫ (P.smallRelative R).d (m+1) m = 0
    rw [HomologicalComplex.Hom.comm, ← Category.assoc, identityChain_boundary,
      boundaryChain, Preadditive.sum_comp, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp]
    have hf : simplexι R (faceSingularSimplex m i) ≫ (CsingMap R (boundaryIncl (m+1))).f m =
        simplexι R (Y := smallSubcomplex (X := TopCat.of P.carrier) P.cover)
          ⟨P.faceSimplex i, P.faceSimplex_small i⟩ ≫ (P.smallIncl R).f m := by
      rw [smallIncl, HomologicalComplex.comp_f, smallChainIncl, simplexι_chainMap_f_assoc, simplexι_CsingMap_f,
        simplexι_CsingMap_f]
      rfl
    rw [hf, Category.assoc, ← HomologicalComplex.comp_f,
      show P.smallIncl R ≫ P.proj R = 0 from cokernel.condition _,
      HomologicalComplex.zero_f, comp_zero, smul_zero]

def identitySmallCycle : ModuleCat.of R R ⟶ (P.smallRelative R).cycles n :=
  (P.smallRelative R).liftCycles (identityChain R n ≫ (P.proj R).f n) (n-1)
    (by cases n <;> simp) (P.identity_small_cycle R)

@[reassoc (attr := simp)] theorem identitySmallCycle_i :
    P.identitySmallCycle R ≫ (P.smallRelative R).iCycles n = identityChain R n ≫ (P.proj R).f n :=
  (P.smallRelative R).liftCycles_i _ _ _ _

def identitySmallClassMap : ModuleCat.of R R ⟶ (P.smallRelative R).homology n :=
  P.identitySmallCycle R ≫ (P.smallRelative R).homologyπ n

theorem identitySmallClassMap_toRelative :
    P.identitySmallClassMap R ≫ HomologicalComplex.homologyMap (P.toRelative R) n =
      identityClassMap R n ≫ HrelMap R n (boundaryIncl n) P.incl P.square := by
  change _ = identityClassMap R n ≫ HomologicalComplex.homologyMap (relComplexMap R _ _ P.square) n
  rw [identitySmallClassMap, identityClassMap, Category.assoc, Category.assoc,
    HomologicalComplex.homologyπ_naturality, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun m => m ≫ (relComplex R P.incl).homologyπ n)
  apply (cancel_mono ((relComplex R P.incl).iCycles n)).mp
  rw [Category.assoc, Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, identitySmallCycle_i_assoc, identityRelativeCycle_i_assoc,
    identityRelativeChain, Category.assoc,
    ← HomologicalComplex.comp_f, P.proj_toRelative, ← HomologicalComplex.comp_f,
    relProj_comp_relComplexMap, CsingMap_id, Category.id_comp]

def cochainDesc : (P.smallRelative R).X n ⟶ ModuleCat.of R R :=
  cokDesc R (P.smallIncl R) n (coloringCochain R n) (P.smallIncl_coloring R)

@[reassoc (attr := simp)] theorem proj_cochainDesc :
    (P.proj R).f n ≫ P.cochainDesc R = coloringCochain R n := π_cokDesc R _ _ _ _

theorem cochainDesc_cocycle : (P.smallRelative R).d (n+1) n ≫ P.cochainDesc R = 0 := by
  haveI : Epi ((P.proj R).f (n+1)) :=
    inferInstanceAs (Epi ((cokernel.π (P.smallIncl R)).f (n+1)))
  apply (cancel_epi ((P.proj R).f (n+1))).mp
  rw [← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc,
    proj_cochainDesc, coloringCochain_cocycle, comp_zero]

def smallDetector : (P.smallRelative R).homology n ⟶ ModuleCat.of R R :=
  (P.smallRelative R).homologyι n ≫ (P.smallRelative R).descOpcycles'
    (P.cochainDesc R) (n+1) rfl (P.cochainDesc_cocycle R)

@[reassoc (attr := simp)] theorem identitySmallClassMap_detector :
    P.identitySmallClassMap R ≫ P.smallDetector R = 𝟙 _ := by
  rw [identitySmallClassMap, smallDetector, Category.assoc,
    ← Category.assoc ((P.smallRelative R).homologyπ n),
    HomologicalComplex.homology_π_ι, Category.assoc, HomologicalComplex.p_descOpcycles,
    ← Category.assoc, identitySmallCycle_i, Category.assoc, proj_cochainDesc, identityChain_coloringCochain]

def detector : Hrel R n P.incl ⟶ ModuleCat.of R R := by
  letI := P.isIso_toRelative R n
  exact inv (HomologicalComplex.homologyMap (P.toRelative R) n) ≫ P.smallDetector R

@[reassoc (attr := simp)] theorem identityClassMap_detector :
    identityClassMap R n ≫ HrelMap R n (boundaryIncl n) P.incl P.square ≫ P.detector R = 𝟙 _ := by
  letI := P.isIso_toRelative R n
  rw [← Category.assoc, ← P.identitySmallClassMap_toRelative R, detector, Category.assoc,
    IsIso.hom_inv_id_assoc, identitySmallClassMap_detector]

theorem identityClass_image_ne_zero [Nontrivial R] :
    HrelMap R n (boundaryIncl n) P.incl P.square (identityClass R n) ≠ 0 := by
  intro hz
  have h := congrArg (fun m => m 1) (P.identityClassMap_detector R)
  change P.detector R (HrelMap R n (boundaryIncl n) P.incl P.square (identityClass R n)) = 1 at h
  rw [hz, map_zero] at h
  exact zero_ne_one h

end ColoringSubspace

def boundaryColoringSubspace (n : ℕ) : ColoringSubspace n where
  carrier := boundary n
  boundary_subset := Set.Subset.rfl
  small x := by
    obtain ⟨i, hi⟩ := boundary_exists_zero x
    refine ⟨i, ?_⟩
    rw [hi, NNReal.coe_zero]
    positivity

/-- The uniform barycenter is characterized by its actual coordinates;
no convention for a chosen barycenter definition is imposed downstream. -/
def puncturedColoringSubspace (n : ℕ) (b : GeometricSimplex n)
    (hb : ∀ i : Fin (n+1), (b i : ℝ) = (1 : ℝ)/(n+1)) : ColoringSubspace n where
  carrier := {b}ᶜ
  boundary_subset := by
    intro x hx he
    obtain ⟨i, hi⟩ := boundary_exists_zero ⟨x, hx⟩
    have hp : 0 < (1 : ℝ)/(n+1) := by positivity
    have hzero : (b i : ℝ) = 0 := by rw [← he, hi, NNReal.coe_zero]
    rw [hb i] at hzero
    exact (ne_of_gt hp) hzero
  small x := by
    by_contra hn
    push_neg at hn
    have hx : ∑ i : Fin (n+1), (x.val i : ℝ) = 1 := by exact_mod_cast x.val.property
    have hs : ∑ _i : Fin (n+1), (1 : ℝ)/(n+1) = ∑ i : Fin (n+1), (x.val i : ℝ) := by
      rw [hx]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      exact mul_one_div_cancel (by positivity)
    have heq := (Finset.sum_eq_sum_iff_of_le (fun i (_hi : i ∈ (Finset.univ : Finset (Fin (n+1)))) => hn i)).mp hs
    apply x.property
    apply Subtype.ext
    funext i
    apply NNReal.coe_injective
    exact (heq i (Finset.mem_univ i)).symm.trans (hb i).symm

variable (R : Type) [CommRing R]

/-- The identity simplex class itself is nonzero in actual relative
singular homology, in every dimension and every nonzero coefficient ring. -/
theorem identityClass_ne_zero [Nontrivial R] (n : ℕ) : identityClass R n ≠ 0 := by
  have h := (boundaryColoringSubspace n).identityClass_image_ne_zero R
  intro hz
  exact h (by rw [hz, map_zero])

/-- Local homology at the uniform barycenter detects the identity simplex
with coefficient one. This is the interface for a single staircase chart. -/
theorem identityClass_local_ne_zero [Nontrivial R] (n : ℕ) (b : GeometricSimplex n)
    (hb : ∀ i : Fin (n+1), (b i : ℝ) = (1 : ℝ)/(n+1)) :
    HrelMap R n (boundaryIncl n) (puncturedColoringSubspace n b hb).incl
      (puncturedColoringSubspace n b hb).square (identityClass R n) ≠ 0 :=
  (puncturedColoringSubspace n b hb).identityClass_image_ne_zero R

end NRR.SingularHomology.SimplexFundamental
