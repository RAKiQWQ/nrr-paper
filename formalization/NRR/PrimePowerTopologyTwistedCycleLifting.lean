import NRR.PrimePowerTopologyTwistedRelativeExact
import NRR.PrimePowerTopologyEquivariantFill
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Lifting cycles through character coinvariants at the first possible
homology degree, using equivariant fillers in lower degrees. -/

noncomputable section
open CategoryTheory Limits

namespace NRR.PrimePowerTopology

variable {R : Type} [CommRing R] {G : Type} [Group G]
variable {K L : ChainComplex (ModuleCat R) ℕ}

private theorem epi_homologyMap_of_cycle_lifting (f : K ⟶ L) (q : ℕ)
    (lift : ∀ y : L.X q, L.d q (q-1) y = 0 →
      ∃ x : K.X q, K.d q (q-1) x = 0 ∧ f.f q x = y) :
    Epi (HomologicalComplex.homologyMap f q) := by
  have hnext : (ComplexShape.down ℕ).next q = q-1 := by cases q <;> simp
  letI : Epi (HomologicalComplex.cyclesMap f q) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    obtain ⟨x,hx,hy⟩ := lift (L.iCycles q y)
      (congrArg (fun u : L.cycles q ⟶ L.X (q-1) => u y) (L.iCycles_d q (q-1)))
    let S := K.sc q
    let v : LinearMap.ker S.g.hom := ⟨x, by
      change K.d q ((ComplexShape.down ℕ).next q) x = 0
      rwa [hnext]⟩
    let z := S.moduleCatCyclesIso.inv v
    refine ⟨z, (ModuleCat.mono_iff_injective (L.iCycles q)).mp inferInstance ?_⟩
    have hz : K.iCycles q z = x :=
      congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f v)
        S.moduleCatCyclesIso_inv_iCycles
    have hn := congrArg (fun u : K.cycles q ⟶ L.X q => u z)
      (HomologicalComplex.cyclesMap_i f q)
    exact hn.trans ((congrArg (f.f q) hz).trans hy)
  exact epi_of_epi_fac (HomologicalComplex.homologyπ_naturality f q)

variable (χ : G →* Rˣ) (ρ : G → (K ⟶ K))

/-- Below the first possible ordinary homology degree, equivariant fillers
for ordinary cycles suffice to lift every twisted cycle in the next degree.
This includes degree zero without any hypothesis about fillers. -/
theorem epi_twistedProjection_of_fillers (q : ℕ)
    (fill : ∀ i < q, ∃ s : K.X i ⟶ K.X (i+1),
      (∀ g, (ρ g).f i ≫ s = s ≫ (ρ g).f (i+1)) ∧
      ∀ z : K.X i, K.d i (i-1) z = 0 → K.d (i+1) i (s z) = z) :
    Epi (HomologicalComplex.homologyMap (twistedChainProj R χ K ρ) q) := by
  let π := twistedChainProj R χ K ρ
  apply epi_homologyMap_of_cycle_lifting π q
  intro y hy
  have hepi : Epi (π.f q) :=
    inferInstanceAs (Epi ((cokernel.π (chainActionRelations R χ K ρ)).f q))
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective (π.f q)).mp hepi y
  cases q with
  | zero =>
      refine ⟨x, ?_, hx⟩
      rw [K.shape 0 0 (by decide)]
      rfl
  | succ i =>
      obtain ⟨s,hs,hfill⟩ := fill i (Nat.lt_succ_self i)
      let w := K.d (i+1) i x
      have hw : K.d i (i-1) w = 0 :=
        congrArg (fun f : K.X (i+1) ⟶ K.X (i-1) => f x) (K.d_comp_d (i+1) i (i-1))
      have hπw : π.f i w = 0 := by
        have h := congrArg (fun f : K.X (i+1) ⟶ (twistedChainComplex R χ K ρ).X i => f x)
          (π.comm (i+1) i).symm
        change π.f i w = (twistedChainComplex R χ K ρ).d (i+1) i (π.f (i+1) x) at h
        exact h.trans ((congrArg ((twistedChainComplex R χ K ρ).d (i+1) i) hx).trans hy)
      have hsπ := congrArg (fun f : K.X i ⟶ (twistedChainComplex R χ K ρ).X (i+1) => f w)
        (twistedProj_componentMap R χ ρ ρ s hs)
      change twistedComponentMap R χ ρ ρ s hs (π.f i w) = π.f (i+1) (s w) at hsπ
      have hz : π.f (i+1) (s w) = 0 := by rw [← hsπ, hπw, map_zero]
      refine ⟨x - s w, ?_, ?_⟩
      · change K.d (i+1) i (x - s w) = 0
        rw [map_sub, hfill w hw, sub_self]
      · rw [map_sub, hz, sub_zero, hx]

/-- For ordinary chain modules free on group orbits, projection onto
twisted homology is surjective through the first possible nonzero degree. -/
theorem epi_twistedProjection_of_free_orbits
    (law : ∀ g h, ρ (g*h) = ρ h ≫ ρ g) {I : ℕ → Type*}
    (b : ∀ i, Module.Basis (G × I i) R (K.X i))
    (hb : ∀ i g h a, (ρ g).f i (b i (h,a)) = b i (g*h,a))
    (q : ℕ) (hK : ∀ i < q, IsZero (K.homology i)) :
    Epi (HomologicalComplex.homologyMap (twistedChainProj R χ K ρ) q) :=
  epi_twistedProjection_of_fillers χ ρ q
    (exists_equivariantBoundarySection_of_basis ρ law b hb q hK)

end NRR.PrimePowerTopology
