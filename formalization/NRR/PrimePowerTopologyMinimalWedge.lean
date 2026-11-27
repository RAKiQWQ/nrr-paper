import NRR.PrimePowerTopologyMinimalSkeleton

/-! The lowest compactified configuration stratum is an actual finite wedge
of spheres.  We give the continuous quotient from the disjoint union of the
compactified cells and identify all its fibers.  In particular this is a
topological presentation of the real stratum, not a formal cellular module. -/

noncomputable section
open Set Topology
open scoped OnePoint
open NRR.PrimePower

namespace NRR.PrimePowerTopology

abbrev MinimalSphereSum (d n : ℕ) :=
  Σ σ : Equiv.Perm (Fin n), OnePoint (Space d × heightChamber n σ)

def minimalCellInclusion {d n : ℕ} (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    C(OnePoint (Space d × heightChamber n σ),minimalSkeleton d n) where
  toFun p := ⟨compactifiedVerticalCell i₀ σ p,by
    rw [minimalSkeleton_eq_iUnion_cellRanges i₀]
    exact mem_iUnion.mpr ⟨σ,p,rfl⟩⟩
  continuous_toFun := (compactifiedVerticalCell i₀ σ).continuous.subtype_mk _

def minimalWedgeProjection {d n : ℕ} (i₀ : Fin n) :
    C(MinimalSphereSum d n,minimalSkeleton d n) where
  toFun p := minimalCellInclusion i₀ p.1 p.2
  continuous_toFun := continuous_sigma fun σ => (minimalCellInclusion i₀ σ).continuous

theorem minimalWedgeProjection_surjective {d n : ℕ} (i₀ : Fin n) :
    Function.Surjective (minimalWedgeProjection (d := d) i₀) := by
  intro x
  have hx : x.val ∈ ⋃ σ,range (compactifiedVerticalCell i₀ σ) :=
    (minimalSkeleton_eq_iUnion_cellRanges i₀).le x.property
  obtain ⟨σ,p,hp⟩ := mem_iUnion.mp hx
  exact ⟨⟨σ,p⟩,Subtype.ext hp⟩

/-- Compactness of the finite union and Hausdorffness of the actual stratum
make the cell presentation a genuine topological quotient. -/
theorem isQuotientMap_minimalWedgeProjection {d n : ℕ} (i₀ : Fin n) :
    IsQuotientMap (minimalWedgeProjection (d := d) i₀) := by
  exact (minimalWedgeProjection i₀).continuous.isClosedMap.isQuotientMap
    (minimalWedgeProjection i₀).continuous (minimalWedgeProjection_surjective i₀)

@[simp] theorem minimalCellInclusion_infty {d n : ℕ}
    (i₀ : Fin n) (σ : Equiv.Perm (Fin n)) :
    (minimalCellInclusion (d := d) i₀ σ ∞).val = ∞ := rfl

/-- Distinct compactified cells meet at exactly their common point at infinity. -/
theorem minimalWedgeProjection_fiber {d n : ℕ} (i₀ : Fin n)
    (p q : MinimalSphereSum d n) :
    minimalWedgeProjection i₀ p = minimalWedgeProjection i₀ q ↔
      p = q ∨ p.2 = ∞ ∧ q.2 = ∞ := by
  rcases p with ⟨σ,p⟩
  rcases q with ⟨τ,q⟩
  constructor
  · intro he
    have he' := congrArg Subtype.val he
    change compactifiedVerticalCell i₀ σ p = compactifiedVerticalCell i₀ τ q at he'
    induction p using OnePoint.rec with
    | infty =>
      right
      refine ⟨rfl,?_⟩
      induction q using OnePoint.rec with
      | infty => rfl
      | coe q => exact False.elim (Option.noConfusion he')
    | coe p =>
      induction q using OnePoint.rec with
      | infty => exact False.elim (Option.noConfusion he')
      | coe q =>
        have cellEq : verticalCellEmbedding i₀ σ p = verticalCellEmbedding i₀ τ q :=
          Option.some.inj he'
        have same : σ = τ := by
          by_contra hn
          have hs : verticalCellEmbedding i₀ σ p ∈ verticalCellSet d n σ :=
            ((verticalCellCoordinates i₀ σ).symm p).property
          have ht : verticalCellEmbedding i₀ τ q ∈ verticalCellSet d n τ :=
            ((verticalCellCoordinates i₀ τ).symm q).property
          exact Set.disjoint_left.mp (verticalCellSets_pairwise_disjoint d n hn) hs
            (cellEq.symm ▸ ht)
        subst τ
        have pq := (isClosedEmbedding_verticalCell i₀ σ).injective cellEq
        subst q
        exact Or.inl rfl
  · rintro (he | ⟨hp,hq⟩)
    · exact congrArg (minimalWedgeProjection i₀) he
    · change p = ∞ at hp
      change q = ∞ at hq
      subst p
      subst q
      apply Subtype.ext
      rfl

/-- Continuity on the true minimal skeleton can be tested cell by cell. -/
theorem continuous_minimalSkeleton_iff {d n : ℕ} (i₀ : Fin n)
    {Y : Type*} [TopologicalSpace Y] (f : minimalSkeleton d n → Y) :
    Continuous f ↔ ∀ σ,Continuous (fun p => f (minimalCellInclusion i₀ σ p)) := by
  rw [(isQuotientMap_minimalWedgeProjection i₀).continuous_iff]
  exact continuous_sigma_iff

end NRR.PrimePowerTopology
