import NRR.PrimePowerTopologyAssociatedBM
import NRR.PrimePowerTopologyOnePointHomology
import NRR.PrimePowerTopologyOrientationRows

/-!
Explicit compactified fundamental-class representatives for the BM Euler
map.  The configuration representative is the actual image of the ambient
Euclidean one-point fundamental class under the open-locus collapse.
Its projected Euler image vanishes whenever the fiber has positive rank.
Detecting the twisted Euler map requires a class outside this ordinary image.
-/

noncomputable section
open Set Topology Filter CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

section Collapse
variable {X : Type*} [TopologicalSpace X] [T2Space X] (S : Set X)

/-- Collapse the complement of an open locus, including ambient infinity. -/
def onePointOpenCollapse : OnePoint X → OnePoint S :=
  fun z => z.elim ∞ (openCollapse S)

omit [TopologicalSpace X] [T2Space X] in
@[simp] theorem onePointOpenCollapse_infty : onePointOpenCollapse S ∞ = ∞ := rfl

omit [TopologicalSpace X] [T2Space X] in
@[simp] theorem onePointOpenCollapse_coe (x : X) :
    onePointOpenCollapse S (x : OnePoint X) = openCollapse S x := rfl

/-- The open-locus collapse extends continuously also at ambient infinity. -/
theorem continuous_onePointOpenCollapse (hS : IsOpen S) :
    Continuous (onePointOpenCollapse S) := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_,continuous_openCollapse S hS⟩
  change Filter.map (openCollapse S) (coclosedCompact X) ≤ 𝓝 ∞
  apply OnePoint.le_nhds_infty.mpr
  intro K hKc hKk
  let A : Set X := Subtype.val '' K
  have hAk : IsCompact A := hKk.image continuous_subtype_val
  have hAc : IsClosed A := hAk.isClosed
  apply Filter.mem_of_superset (hAk.compl_mem_coclosedCompact_of_isClosed hAc)
  intro x hx
  by_cases hxS : x ∈ S
  · apply Or.inl
    refine ⟨⟨x,hxS⟩,?_,(openCollapse_of_mem S hxS).symm⟩
    intro hxK
    exact hx ⟨⟨x,hxS⟩,hxK,rfl⟩
  · apply Or.inr
    exact openCollapse_of_not_mem S hxS

end Collapse

/-- The genuine ambient-to-configuration compactified collapse. -/
def configurationOnePointCollapse (d n : ℕ) :
    C(OnePoint (Fin n → Space d),OnePoint (Configuration d n)) :=
  ⟨onePointOpenCollapse {x | Function.Injective x},
    continuous_onePointOpenCollapse _ (isOpen_injectiveSites d n)⟩

@[simp] theorem configurationOnePointCollapse_infty (d n : ℕ) :
    configurationOnePointCollapse d n ∞ = ∞ := rfl

@[simp] theorem configurationOnePointCollapse_config {d n : ℕ} (x : Configuration d n) :
    configurationOnePointCollapse d n (x.val : OnePoint (Fin n → Space d)) =
      (x : OnePoint (Configuration d n)) := openCollapse_of_mem _ x.property

@[simp] theorem configurationOnePointCollapse_collision {d n : ℕ}
    (x : Fin n → Space d) (hx : ¬ Function.Injective x) :
    configurationOnePointCollapse d n (x : OnePoint (Fin n → Space d)) = ∞ :=
  openCollapse_of_not_mem _ hx

theorem finrank_configurationAmbient (d n : ℕ) :
    Module.finrank ℝ (Fin n → Space d) = n*d := by
  simp only [Module.finrank_pi_fintype,finrank_euclideanSpace_fin,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- An explicit actual BM source class, obtained by collapse from ambient
Euclidean space and then the canonical infinity-relative projection. -/
def configurationBMFundamentalClass (R : Type) [Ring R] (d n : ℕ)
    (hpos : 0 < n*d) : Hrel R (n*d) (associatedBMSourceIncl d n) :=
  relJ R (n*d) (associatedBMSourceIncl d n)
    (HabsMap R (n*d) (TopCat.ofHom (configurationOnePointCollapse d n))
      (vectorOnePointFundamentalClass R (Fin n → Space d) (n*d)
        (finrank_configurationAmbient d n) hpos))

/-- The image of the ordered ambient class under the chain quotient. -/
def associatedBMTwistedFundamentalClass (R : Type) [CommRing R] (d n : ℕ)
    (χ : ConfigurationGroup n →* Rˣ) (hpos : 0 < n*d) :
    (associatedBMTwistedSource R (d := d) χ).homology (n*d) :=
  HomologicalComplex.homologyMap
    (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
      (associatedBMSourceRelativeAction R)) (n*d)
    (configurationBMFundamentalClass R d n hpos)

/-- The BM Euler image of this particular projected representative. -/
def associatedBMTwistedEulerClass (R : Type) [CommRing R] (d n : ℕ)
    (χ : ConfigurationGroup n →* Rˣ) (hpos : 0 < n*d) :
    (associatedBMTwistedTarget R (d := d) χ).homology (n*d) :=
  associatedBMTwistedEulerMap R χ (n*d)
    (associatedBMTwistedFundamentalClass R d n χ hpos)

/-- Naturality with the quotient of chains forces the twisted Euler map to
annihilate the image of ordinary homology in every degree. On the ordered
cover a constant nonzero fiber vector displaces the zero section. -/
theorem associatedBMProjection_comp_twistedEulerMap_eq_zero
    (R : Type) [CommRing R] {d n : ℕ} [Nontrivial (ReducedValues d n)]
    (χ : ConfigurationGroup n →* Rˣ) (k : ℕ) :
    HomologicalComplex.homologyMap
      (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
        (associatedBMSourceRelativeAction R)) k ≫
      associatedBMTwistedEulerMap R (d := d) χ k = 0 := by
  obtain ⟨v,hv⟩ := exists_ne (0 : ReducedValues d n)
  have hz := associatedBMZeroRelative_eq_zero_of_nonzero R k
    (ContinuousMap.const (Configuration d n) v) (fun _ => hv)
  unfold associatedBMTwistedEulerMap associatedBMTwistedZeroMap associatedBMTwistedGraphMap
  rw [← HomologicalComplex.homologyMap_comp, twistedChainProj_map,
    HomologicalComplex.homologyMap_comp]
  change HrelMap R k _ _ (associatedBMGraph_pair_comm (ContinuousMap.const _ 0)) ≫ _ = 0
  rw [hz, zero_comp]

/-- Throughout the classification range, this projected representative has
zero Euler image, over every commutative coefficient ring and character. -/
theorem associatedBMTwistedEulerClass_eq_zero
    (R : Type) [CommRing R] {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (χ : ConfigurationGroup n →* Rˣ) (hpos : 0 < n*d) :
    associatedBMTwistedEulerClass R d n χ hpos = 0 := by
  have hr : 0 < Module.finrank ℝ (ReducedValues d n) := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [finrank_reducedValues]
    exact Nat.mul_pos (by omega) (by omega)
  letI := Module.nontrivial_of_finrank_pos hr
  exact congrArg (fun f : Hrel R (n*d) (associatedBMSourceIncl d n) ⟶
    (associatedBMTwistedTarget R (d := d) χ).homology (n*d) =>
      f (configurationBMFundamentalClass R d n hpos))
    (associatedBMProjection_comp_twistedEulerMap_eq_zero R χ (n*d))

/-- Quotient of twisted source homology by the image of the ordinary
ordered cover. The Euler morphism factors canonically through this module. -/
def associatedBMEulerOnCokernel (R : Type) [CommRing R] {d n : ℕ}
    [Nontrivial (ReducedValues d n)] (χ : ConfigurationGroup n →* Rˣ) (k : ℕ) :
    cokernel (HomologicalComplex.homologyMap
      (twistedChainProj R χ (relComplex R (associatedBMSourceIncl d n))
        (associatedBMSourceRelativeAction R)) k) ⟶
      (associatedBMTwistedTarget R (d := d) χ).homology k :=
  cokernel.desc _ (associatedBMTwistedEulerMap R χ k)
    (associatedBMProjection_comp_twistedEulerMap_eq_zero R χ k)

@[reassoc (attr := simp)]
theorem associatedBMTwistedEulerMap_factor (R : Type) [CommRing R] {d n : ℕ}
    [Nontrivial (ReducedValues d n)] (χ : ConfigurationGroup n →* Rˣ) (k : ℕ) :
    cokernel.π _ ≫ associatedBMEulerOnCokernel R (d := d) χ k =
      associatedBMTwistedEulerMap R χ k :=
  cokernel.π_desc _ _ _

theorem associatedBMEulerOnCokernel_ne_zero_iff (R : Type) [CommRing R] {d n : ℕ}
    [Nontrivial (ReducedValues d n)] (χ : ConfigurationGroup n →* Rˣ) (k : ℕ) :
    associatedBMEulerOnCokernel R (d := d) χ k ≠ 0 ↔
      associatedBMTwistedEulerMap R (d := d) χ k ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    rw [← associatedBMTwistedEulerMap_factor, h, comp_zero]
  · intro h
    apply (cancel_epi (cokernel.π _)).mp
    rw [associatedBMTwistedEulerMap_factor, h, comp_zero]

theorem associatedBMTwistedEulerClass_eq_zero_of_nonzero
    (R : Type) [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)
    (hpos : 0 < n*d) (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x)
    (hnz : ∀ x, f x ≠ 0) :
    associatedBMTwistedEulerClass R d n χ hpos = 0 := by
  unfold associatedBMTwistedEulerClass
  rw [associatedBMTwistedEulerMap_eq_zero_of_nonzero R χ (n*d) f he hnz]
  rfl

/-- A formal implication for the projected class. Its premise is ruled out
in the classification range by `associatedBMTwistedEulerClass_eq_zero`. -/
theorem equivariant_has_zero_of_associatedBMTwistedEulerClass_ne_zero
    (R : Type) [CommRing R] {d n : ℕ} (χ : ConfigurationGroup n →* Rˣ)
    (hpos : 0 < n*d) (h : associatedBMTwistedEulerClass R d n χ hpos ≠ 0)
    (f : C(Configuration d n,ReducedValues d n))
    (he : ∀ (σ : ConfigurationGroup n) x, f (σ • x) = σ • f x) : ∃ x, f x = 0 := by
  by_contra hnz
  exact h (associatedBMTwistedEulerClass_eq_zero_of_nonzero R χ hpos f he
    (fun x hx => hnz ⟨x,hx⟩))


/-- The real ambient relabeling homeomorphism, extended at infinity. -/
def associatedCompactifiedAmbientRelabel (d : ℕ) {n : ℕ} (σ : ConfigurationGroup n) :
    OnePoint (Fin n → Space d) ≃ₜ OnePoint (Fin n → Space d) :=
  (ambientRelabel d σ).toContinuousLinearEquiv.toHomeomorph.onePointCongr

theorem associatedAmbientRelabel_injective_iff {d n : ℕ} (σ : ConfigurationGroup n)
    (x : Fin n → Space d) :
    Function.Injective (ambientRelabel d σ x) ↔ Function.Injective x := by
  change Function.Injective (x ∘ σ.symm) ↔ Function.Injective x
  constructor
  · intro h
    have hh := h.comp σ.injective
    simpa only [Function.comp_def,Equiv.symm_apply_apply] using hh
  · intro h
    exact h.comp σ.symm.injective

/-- The actual compactified collapse is equivariant before passing to any
chains, orientation coefficients, or group quotient. -/
theorem configurationOnePointCollapse_equivariant {d n : ℕ} (σ : ConfigurationGroup n)
    (z : OnePoint (Fin n → Space d)) :
    configurationOnePointCollapse d n (associatedCompactifiedAmbientRelabel d σ z) =
      compactifiedConfigurationRelabel σ (configurationOnePointCollapse d n z) := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change openCollapse {y : Fin n → Space d | Function.Injective y} (ambientRelabel d σ x) =
      compactifiedConfigurationRelabel σ (openCollapse {y : Fin n → Space d | Function.Injective y} x)
    by_cases hx : Function.Injective x
    · have hσx := (associatedAmbientRelabel_injective_iff σ x).mpr hx
      rw [openCollapse_of_mem _ hσx,openCollapse_of_mem _ hx]
      rfl
    · have hσx := mt (associatedAmbientRelabel_injective_iff σ x).mp hx
      rw [openCollapse_of_not_mem _ hσx,openCollapse_of_not_mem _ hx]
      rfl

/-- The ambient orientation coefficient character over prime coefficients. -/
def associatedAmbientOrientationMod (p d n : ℕ) : ConfigurationGroup n →* (ZMod p)ˣ :=
  (permutationOrientationMod p n)^d

/-- The fiber determinant character of the reduced-value representation. -/
def associatedFiberOrientationMod (p d n : ℕ) : ConfigurationGroup n →* (ZMod p)ˣ :=
  (permutationOrientationMod p n)^(d-1)

/-- Exact cancellation of the computed ambient and fiber determinant twists.
This records the coefficient system required by a Thom comparison, without
postulating such a comparison or the nonvanishing of its Euler image. -/
theorem associatedThomOrientationMod (p d n : ℕ) :
    associatedAmbientOrientationMod p (d+1) n * associatedFiberOrientationMod p (d+1) n =
      permutationOrientationMod p n := by
  apply MonoidHom.ext
  intro σ
  change (permutationOrientationMod p n σ)^(d+1) *
    (permutationOrientationMod p n σ)^((d+1)-1) = permutationOrientationMod p n σ
  rw [Nat.add_sub_cancel]
  have hs : (permutationOrientationMod p n σ)^2 = 1 := by
    change (Units.map (Int.castRingHom (ZMod p)).toMonoidHom (Equiv.Perm.sign σ))^2 = 1
    rw [← map_pow]
    have hi : (Equiv.Perm.sign σ)^2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hi,map_one]
  rw [pow_succ]
  calc
    (permutationOrientationMod p n σ ^ d * permutationOrientationMod p n σ) *
        permutationOrientationMod p n σ ^ d =
      permutationOrientationMod p n σ *
        (permutationOrientationMod p n σ * permutationOrientationMod p n σ)^d := by
      rw [mul_pow]
      ac_rfl
    _ = permutationOrientationMod p n σ := by rw [← pow_two,hs,one_pow,mul_one]
end NRR.PrimePowerTopology
