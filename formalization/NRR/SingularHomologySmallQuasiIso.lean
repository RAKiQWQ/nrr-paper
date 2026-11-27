import NRR.SingularHomologySmallSubdivision
import NRR.SingularHomologySubdivisionMesh
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-! The finite-chain subdivision argument for the actual small-chain inclusion. -/
noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
namespace NRR.SingularHomology
variable (R : Type) [Ring R]

def chainEndIter {K : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ K) : ℕ → (K ⟶ K)
  | 0 => 𝟙 _
  | k+1 => chainEndIter f k ≫ f

theorem chainEndIter_homologyMap {K : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ K) (h : ∀ n, HomologicalComplex.homologyMap f n = 𝟙 _) (k n : ℕ) :
    HomologicalComplex.homologyMap (chainEndIter R f k) n = 𝟙 _ := by
  induction k with
  | zero => simp [chainEndIter]
  | succ k ih => rw [chainEndIter, HomologicalComplex.homologyMap_comp, ih, h, Category.id_comp]

variable {X : TopCat.{0}} {ι : Type} (U : ι → Set X)

theorem smallChainIter_incl (k : ℕ) :
    chainEndIter R (smallChainSubdivision R U) k ≫ smallChainIncl R U =
      smallChainIncl R U ≫ chainEndIter R (singularChainSubdivision R X) k := by
  induction k with
  | zero => simp [chainEndIter]
  | succ k ih =>
    rw [chainEndIter, chainEndIter, Category.assoc, smallChainSubdivision_incl,
      ← Category.assoc, ih, Category.assoc]

theorem simplexι_chainEndIter_comp_zero {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    ∀ (k : ℕ) {T : ModuleCat R} (q : (Csing R X).X n ⟶ T),
      (∀ a : Fin k → SubdivisionIndex n,
        simplexι R (subdivisionSimplexIter k s a) ≫ q = 0) →
      simplexι R s ≫ (chainEndIter R (singularChainSubdivision R X) k).f n ≫ q = 0
  | 0, T, q, small => by
    simpa only [chainEndIter, HomologicalComplex.id_f, Category.comp_id,
      subdivisionSimplexIter] using small (fun i => Fin.elim0 i)
  | k+1, T, q, small => by
    rw [chainEndIter, HomologicalComplex.comp_f, Category.assoc]
    apply simplexι_chainEndIter_comp_zero s k ((singularChainSubdivision R X).f n ≫ q)
    intro a
    rw [simplexι_singularChainSubdivision_eq_sum_assoc, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro b _
    rw [Preadditive.zsmul_comp]
    have hb := small (Fin.cases b a)
    simpa only [subdivisionSimplexIter, Fin.cases_succ, Fin.cases_zero, smul_zero] using
      congrArg (fun t => subdivisionSign n b • t) hb

theorem simplexι_smallChainIncl_cokernel_zero {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (small : s ∈ (smallSubcomplex U).obj _) :
    simplexι R s ≫ cokernel.π ((smallChainIncl R U).f n) = 0 := by
  have hs := simplexι_chainMap_f R (smallSubcomplex U).ι ⟨s, small⟩
  change simplexι R (Y := (smallSubcomplex U : SSet.{0})) ⟨s, small⟩ ≫ (simplicialChainMap R (smallSubcomplex U).ι).f n = simplexι R s at hs
  rw [← hs, Category.assoc, show
    (simplicialChainMap R (smallSubcomplex U).ι).f n ≫
      cokernel.π ((smallChainIncl R U).f n) = 0 from
        cokernel.condition ((smallChainIncl R U).f n), comp_zero]

theorem exists_small_lift_simplex (cover : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (r : R) :
    ∃ k, ∃ y : (smallChainComplex R U).X n,
      (smallChainIncl R U).f n y =
        (chainEndIter R (singularChainSubdivision R X) k).f n (simplexι R s r) := by
  obtain ⟨k, hk⟩ := exists_subdivisionSimplexIter_small U cover s
  have zero := simplexι_chainEndIter_comp_zero R s k
    (cokernel.π ((smallChainIncl R U).f n))
    (fun a => simplexι_smallChainIncl_cokernel_zero R U _ (hk a))
  have hr := congrArg (fun f : ModuleCat.of R R ⟶ _ => f r) zero
  change cokernel.π ((smallChainIncl R U).f n)
    ((chainEndIter R (singularChainSubdivision R X) k).f n (simplexι R s r)) = 0 at hr
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (ShortComplex.exact_cokernel ((smallChainIncl R U).f n)) _ hr
  exact ⟨k, y, hy⟩

theorem small_lift_mono {n k l : ℕ} (hkl : k ≤ l) (x : (Csing R X).X n)
    (lift : ∃ y : (smallChainComplex R U).X n,
      (smallChainIncl R U).f n y =
        (chainEndIter R (singularChainSubdivision R X) k).f n x) :
    ∃ y : (smallChainComplex R U).X n,
      (smallChainIncl R U).f n y =
        (chainEndIter R (singularChainSubdivision R X) l).f n x := by
  induction l, hkl using Nat.le_induction with
  | base => exact lift
  | succ l _ ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨(smallChainSubdivision R U).f n y, ?_⟩
    have comm := congrArg (fun f => f.f n y) (smallChainSubdivision_incl R U)
    change (smallChainIncl R U).f n ((smallChainSubdivision R U).f n y) =
      (singularChainSubdivision R X).f n ((smallChainIncl R U).f n y) at comm
    rw [comm, hy]
    rfl

/-- Every finite singular chain has a single subdivision depth at which the
entire chain lies in the actual small-chain image. -/
theorem exists_small_lift_chain (cover : SmallSimplicesCondition U) (n : ℕ)
    (x : (Csing R X).X n) :
    ∃ k, ∃ y : (smallChainComplex R U).X n,
      (smallChainIncl R U).f n y =
        (chainEndIter R (singularChainSubdivision R X) k).f n x := by
  let P : Submodule R ((Csing R X).X n) := {
    carrier := {x | ∃ k, ∃ y : (smallChainComplex R U).X n,
      (smallChainIncl R U).f n y =
        (chainEndIter R (singularChainSubdivision R X) k).f n x}
    zero_mem' := ⟨0, 0, by simp [chainEndIter]⟩
    add_mem' := by
      rintro x z ⟨k,y,hy⟩ ⟨l,w,hw⟩
      obtain ⟨y',hy'⟩ := small_lift_mono R U (Nat.le_max_left k l) x ⟨y,hy⟩
      obtain ⟨w',hw'⟩ := small_lift_mono R U (Nat.le_max_right k l) z ⟨w,hw⟩
      exact ⟨max k l,y'+w', by simp only [map_add,hy',hw']⟩
    smul_mem' := by
      rintro r x ⟨k,y,hy⟩
      exact ⟨k,r • y, by simp only [map_smul,hy]⟩ }
  let lift : (Csing R X).X n ⟶ ModuleCat.of R P := ccDesc R fun s =>
    ModuleCat.ofHom {
      toFun := fun r => ⟨simplexι R s r, exists_small_lift_simplex R U cover s r⟩
      map_add' := fun r t => Subtype.ext ((simplexι R s).hom.map_add r t)
      map_smul' := fun r t => Subtype.ext ((simplexι R s).hom.map_smul r t) }
  have factor : lift ≫ ModuleCat.ofHom P.subtype = 𝟙 _ := by
    apply simplicialChain_hom_ext R
    intro s
    simp only [lift, ι_ccDesc_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    rfl
  have hx := congrArg (fun f : (Csing R X).X n ⟶ (Csing R X).X n => f x) factor
  change (lift x).val = x at hx
  exact hx ▸ (lift x).property


section ModuleHomology
variable {K L : ChainComplex (ModuleCat R) ℕ}

def moduleCyclesMk (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (x : K.X n) (h : (K.sc n).g x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x,h⟩

@[simp] theorem iCycles_moduleCyclesMk (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (x : K.X n) (h : (K.sc n).g x = 0) :
    K.iCycles n (moduleCyclesMk R K n x h) = x := by
  have e := congrArg (fun f => f ⟨x,h⟩) (K.sc n).moduleCatCyclesIso_inv_iCycles
  exact e

@[simp] theorem moduleCyclesMap_i (f : K ⟶ L) (n : ℕ) (z : K.cycles n) :
    L.iCycles n (HomologicalComplex.cyclesMap f n z) = f.f n (K.iCycles n z) := by
  have e := congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i f n)
  exact e

@[simp] theorem moduleHomologyMap_π (f : K ⟶ L) (n : ℕ) (z : K.cycles n) :
    HomologicalComplex.homologyMap f n (K.homologyπ n z) =
      L.homologyπ n (HomologicalComplex.cyclesMap f n z) := by
  have e := congrArg (fun q => q z) (HomologicalComplex.homologyπ_naturality f n)
  exact e

@[simp] theorem moduleToCycles_i (K : ChainComplex (ModuleCat R) ℕ)
    (m n : ℕ) (x : K.X m) :
    K.iCycles n (K.toCycles m n x) = K.d m n x := by
  have e := congrArg (fun q => q x) (K.toCycles_i m n)
  exact e

@[simp] theorem moduleToCycles_π (K : ChainComplex (ModuleCat R) ℕ)
    (m n : ℕ) (x : K.X m) : K.homologyπ n (K.toCycles m n x) = 0 := by
  have e := congrArg (fun q => q x) (K.toCycles_comp_homologyπ m n)
  exact e

theorem moduleHomologyπ_kernel (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (z : K.cycles n) (hz : K.homologyπ n z = 0) :
    ∃ w : K.X (n+1), K.toCycles (n+1) n w = z := by
  let S := ShortComplex.mk (K.toCycles (n+1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n+1) n)
  have exactS : S.Exact :=
    S.exact_of_g_is_cokernel (K.homologyIsCokernel (n+1) n (by simp))
  exact (ShortComplex.moduleCat_exact_iff S).mp exactS z hz

theorem moduleCycle_of_image_cycle (f : K ⟶ L) [Mono f] (n : ℕ) (w : K.X n)
    (cycle : (L.sc n).g (f.f n w) = 0) : (K.sc n).g w = 0 := by
  let j := (ComplexShape.down ℕ).next n
  have comm := congrArg (fun q => q w) (f.comm n j)
  change L.d n j (f.f n w) = f.f j (K.d n j w) at comm
  have hz : f.f j (K.d n j w) = f.f j 0 := by
    rw [← comm]
    simpa only [map_zero] using cycle
  exact (ModuleCat.mono_iff_injective (f.f j)).mp inferInstance hz

theorem moduleIter_image_cycle (f : L ⟶ L) (n : ℕ) (z : L.cycles n) :
    (L.sc n).g (f.f n (L.iCycles n z)) = 0 := by
  let j := (ComplexShape.down ℕ).next n
  have comm := congrArg (fun q => q (L.iCycles n z)) (f.comm n j)
  change L.d n j (f.f n (L.iCycles n z)) =
    f.f j (L.d n j (L.iCycles n z)) at comm
  have cyc := congrArg (fun q => q z) (L.iCycles_d n j)
  change L.d n j (L.iCycles n z) = 0 at cyc
  rw [cyc, map_zero] at comm
  exact comm

end ModuleHomology


/-- The standard finite-chain subdivision argument, stated for honest chain
maps and their homology maps. Eventual chain lifts prove both surjectivity
and injectivity; no chain-level inverse is postulated. -/
theorem isIso_homologyMap_of_eventual_lifts
    {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) [Mono f]
    (a : ℕ → (K ⟶ K)) (b : ℕ → (L ⟶ L))
    (commute : ∀ k, a k ≫ f = f ≫ b k)
    (a_id : ∀ k n, HomologicalComplex.homologyMap (a k) n = 𝟙 _)
    (b_id : ∀ k n, HomologicalComplex.homologyMap (b k) n = 𝟙 _)
    (lift : ∀ n (x : L.X n), ∃ k, ∃ y : K.X n, f.f n y = (b k).f n x)
    (n : ℕ) : IsIso (HomologicalComplex.homologyMap f n) := by
  have surjective : Function.Surjective (HomologicalComplex.homologyMap f n) := by
    intro z
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ n)).mp inferInstance z
    obtain ⟨k, w, hw⟩ := lift n (L.iCycles n c)
    have hc : (K.sc n).g w = 0 := moduleCycle_of_image_cycle R f n w (by
      rw [hw]
      exact moduleIter_image_cycle R (b k) n c)
    let d := moduleCyclesMk R K n w hc
    have eqcyc : HomologicalComplex.cyclesMap f n d =
        HomologicalComplex.cyclesMap (b k) n c := by
      apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
      rw [moduleCyclesMap_i, moduleCyclesMap_i, iCycles_moduleCyclesMk]
      exact hw
    refine ⟨K.homologyπ n d, ?_⟩
    rw [moduleHomologyMap_π, eqcyc, ← moduleHomologyMap_π, b_id]
    rfl
  have kernel_zero : ∀ z : K.homology n,
      HomologicalComplex.homologyMap f n z = 0 → z = 0 := by
    intro z hz
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
    rw [moduleHomologyMap_π] at hz
    obtain ⟨v, hv⟩ := moduleHomologyπ_kernel R L n _ hz
    obtain ⟨k, w, hw⟩ := lift (n+1) v
    have boundary : K.toCycles (n+1) n w = HomologicalComplex.cyclesMap (a k) n c := by
      apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
      rw [moduleToCycles_i, moduleCyclesMap_i]
      apply (ModuleCat.mono_iff_injective (f.f n)).mp inferInstance
      have ef := congrArg (fun q => q w) (f.comm (n+1) n)
      change L.d (n+1) n (f.f (n+1) w) = f.f n (K.d (n+1) n w) at ef
      have eb := congrArg (fun q => q v) ((b k).comm (n+1) n)
      change L.d (n+1) n ((b k).f (n+1) v) = (b k).f n (L.d (n+1) n v) at eb
      have ev := congrArg (L.iCycles n) hv
      rw [moduleToCycles_i, moduleCyclesMap_i] at ev
      have ec := congrArg (fun q => q.f n (K.iCycles n c)) (commute k)
      change f.f n ((a k).f n (K.iCycles n c)) =
        (b k).f n (f.f n (K.iCycles n c)) at ec
      calc
        _ = L.d (n+1) n (f.f (n+1) w) := ef.symm
        _ = L.d (n+1) n ((b k).f (n+1) v) := by rw [hw]
        _ = (b k).f n (L.d (n+1) n v) := eb
        _ = (b k).f n (f.f n (K.iCycles n c)) := by rw [ev]
        _ = f.f n ((a k).f n (K.iCycles n c)) := ec.symm
    have hb := congrArg (K.homologyπ n) boundary
    rw [moduleToCycles_π, ← moduleHomologyMap_π, a_id] at hb
    exact hb.symm
  have injective : Function.Injective (HomologicalComplex.homologyMap f n) := by
    intro z w he
    have h : HomologicalComplex.homologyMap f n (z-w) = 0 := by
      simp only [map_sub, he, sub_self]
    exact sub_eq_zero.mp (kernel_zero (z-w) h)
  letI : Mono (HomologicalComplex.homologyMap f n) :=
    (ModuleCat.mono_iff_injective _).mpr injective
  letI : Epi (HomologicalComplex.homologyMap f n) :=
    (ModuleCat.epi_iff_surjective _).mpr surjective
  exact isIso_of_mono_of_epi _

instance mono_smallChainIncl : Mono (smallChainIncl R U) := by
  unfold smallChainIncl
  infer_instance

/-- The actual covering-small-chain inclusion induces an isomorphism in every
homological degree, with arbitrary ring coefficients. -/
theorem isIso_smallChainIncl_homologyMap
    (cover : SmallSimplicesCondition U) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallChainIncl R U) n) := by
  apply isIso_homologyMap_of_eventual_lifts R (smallChainIncl R U)
    (chainEndIter R (smallChainSubdivision R U))
    (chainEndIter R (singularChainSubdivision R X))
    (smallChainIter_incl R U)
  · intro k j
    exact chainEndIter_homologyMap R _ (smallChainSubdivision_homologyMap R U) k j
  · intro k j
    exact chainEndIter_homologyMap R _ (singularChainSubdivision_homologyMap R X) k j
  · exact exists_small_lift_chain R U cover

theorem isIso_mvSmallIncl_homologyMap {X : TopCat.{0}}
    (A B : Set X) (cover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (mvSmallIncl (R := R) A B) n) := by
  apply isIso_smallChainIncl_homologyMap R (mvFamily A B)
  constructor
  have e : (⋃ i : Bool, interior (mvFamily A B i)) = interior A ∪ interior B := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i,hi⟩
      cases i with
      | false => exact Or.inl hi
      | true => exact Or.inr hi
    · rintro (hx | hx)
      · exact ⟨false,hx⟩
      · exact ⟨true,hx⟩
  exact e.trans cover


end NRR.SingularHomology
