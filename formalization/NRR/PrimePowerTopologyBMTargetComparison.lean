import NRR.PrimePowerTopologyBMComplement
import NRR.PrimePowerTopologyStabilizedHomology

/-! At the first possible degree, an ordinary geometric calculation on
the entire associated space determines the genuine twisted Euler target. -/

noncomputable section
open CategoryTheory Limits
open NRR.SingularHomology NRR.PrimePower
namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ}

/-- A regular orbit basis detects the group law already on chain maps. -/
private theorem chainAction_mul_of_basis {G : Type} [Group G]
    {K : ChainComplex (ModuleCat R) ℕ} (ρ : G → (K ⟶ K)) {I : ℕ → Type*}
    (b : ∀ i, Module.Basis (G × I i) R (K.X i))
    (hb : ∀ i g h a, (ρ g).f i (b i (h,a)) = b i (g*h,a)) (g h : G) :
    ρ (g*h) = ρ h ≫ ρ g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply (b i).ext
  rintro ⟨s,a⟩
  change (ρ (g*h)).f i (b i (s,a)) = (ρ g).f i ((ρ h).f i (b i (s,a)))
  rw [hb,hb,hb,mul_assoc]

def associatedBMCoverToTarget :
    relComplex R (associatedBMCoverInfinityIncl d n) ⟶
      relComplex R (associatedBMTargetIncl d n) :=
  relComplexMap R _ _ associatedBMPointToComplement_square

theorem associatedBMCoverToTarget_equivariant (g : ConfigurationGroup n) :
    associatedBMCoverInfinityRelativeAction R g ≫ associatedBMCoverToTarget R =
      associatedBMCoverToTarget R (d := d) ≫ associatedBMTargetRelativeAction R g := by
  exact relativeSingularChainMap_equivariant R _ _
    (fun _ => 𝟙 _) associatedBMCoverRelabelMap
    associatedBMComplementRelabelMap associatedBMCoverRelabelMap
    associatedBMCoverInfinityIncl_equivariant associatedBMTargetIncl_equivariant
    associatedBMPointToComplement_square (fun _ => rfl) g

theorem isZero_associatedBMTarget_below {q : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (hq : q < d*n) : IsZero (Hrel R q (associatedBMTargetIncl d n)) := by
  let e := HrelMap R q (associatedBMCoverInfinityIncl d n) (associatedBMTargetIncl d n)
    associatedBMPointToComplement_square
  letI : IsIso e := isIso_associatedBMPointToComplement R q
  exact IsZero.of_epi e (isZero_associatedBMCoverInfinity_below R hd hn hq)

variable (χ : ConfigurationGroup n →* Rˣ)

private theorem target_action_law (g h : ConfigurationGroup n) :
    associatedBMTargetRelativeAction R (d := d) (g*h) =
      associatedBMTargetRelativeAction R h ≫ associatedBMTargetRelativeAction R g :=
  chainAction_mul_of_basis R _ (fun i => associatedBMTargetRelativeOrbitBasis R i)
    (fun i => associatedBMTargetRelativeOrbitBasis_relabel R i) g h

/-- This is surjectivity on homology of the actual Euler target. -/
theorem epi_associatedBMTargetProjection {q : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (hq : q ≤ d*n) :
    Epi (HomologicalComplex.homologyMap (twistedChainProj R χ
      (relComplex R (associatedBMTargetIncl d n)) (associatedBMTargetRelativeAction R)) q) :=
  epi_twistedProjection_of_free_orbits χ (associatedBMTargetRelativeAction R)
    (target_action_law R) (fun i => associatedBMTargetRelativeOrbitBasis R i)
    (fun i => associatedBMTargetRelativeOrbitBasis_relabel R i) q
    (fun i hi => isZero_associatedBMTarget_below R hd hn (hi.trans_le hq))

theorem isZero_associatedBMTwistedTarget_below {q : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (hq : q < d*n) : IsZero ((associatedBMTwistedTarget R (d := d) χ).homology q) := by
  let π := HomologicalComplex.homologyMap (twistedChainProj R χ
    (relComplex R (associatedBMTargetIncl d n)) (associatedBMTargetRelativeAction R)) q
  letI : Epi π := epi_associatedBMTargetProjection R χ hd hn hq.le
  exact IsZero.of_epi π (isZero_associatedBMTarget_below R hd hn hq)

/-- Ordinary point-relative homology of the total space represents the
twisted Euler target in the bottom degree, with exactly the character
relations. No choice of a splitting on group coinvariants is required. -/
theorem existsUnique_associatedBMTargetDetector (hd : 0 < d) (hn : 2 ≤ n)
    {M : ModuleCat R} (u : Hrel R (d*n) (associatedBMCoverInfinityIncl d n) ⟶ M)
    (hu : ∀ g, HomologicalComplex.homologyMap
      (associatedBMCoverInfinityRelativeAction R g) (d*n) ≫ u = (χ g : R) • u) :
    ∃! ψ : (associatedBMTwistedTarget R (d := d) χ).homology (d*n) ⟶ M,
      HomologicalComplex.homologyMap (associatedBMCoverToTarget R) (d*n) ≫
        HomologicalComplex.homologyMap (twistedChainProj R χ (relComplex R
          (associatedBMTargetIncl d n)) (associatedBMTargetRelativeAction R)) (d*n) ≫ ψ = u := by
  let q := d*n
  let f := HomologicalComplex.homologyMap (associatedBMCoverToTarget R (d := d) (n := n)) q
  letI : IsIso f := isIso_associatedBMPointToComplement R q
  let v := inv f ≫ u
  have hv (g : ConfigurationGroup n) :
      HomologicalComplex.homologyMap (associatedBMTargetRelativeAction R g) q ≫ v =
        (χ g : R) • v := by
    have w : HomologicalComplex.homologyMap (associatedBMCoverInfinityRelativeAction R g) q ≫ f =
        f ≫ HomologicalComplex.homologyMap (associatedBMTargetRelativeAction R g) q := by
      simp only [f, ← HomologicalComplex.homologyMap_comp, associatedBMCoverToTarget_equivariant]
    apply (cancel_epi f).mp
    rw [← Category.assoc, ← w, Category.assoc, show f ≫ v = u by simp [v],
      Linear.comp_smul, show f ≫ v = u by simp [v], hu]
  obtain ⟨ψ,hψ,uniq⟩ := existsUnique_twistedHomology_desc_of_free_orbits
    (associatedBMTargetRelativeAction R) χ (target_action_law R)
    (fun i => associatedBMTargetRelativeOrbitBasis R i)
    (fun i => associatedBMTargetRelativeOrbitBasis_relabel R i) q
    (fun i hi => isZero_associatedBMTarget_below R hd hn hi) v hv
  refine ⟨ψ,?_,?_⟩
  · exact (congrArg (fun m => f ≫ m) hψ).trans (IsIso.hom_inv_id_assoc f u)
  · intro ψ' hψ'
    apply uniq
    apply (cancel_epi f).mp
    exact hψ'.trans (IsIso.hom_inv_id_assoc f u).symm

end NRR.PrimePowerTopology
