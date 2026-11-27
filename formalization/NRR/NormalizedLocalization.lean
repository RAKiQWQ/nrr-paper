import NRR.ProductPartitions
import NRR.InnerCylinder

/-! The weighted localization construction for every actual equal-mass
partition of a normalized body, with the prescribed measure unchanged. -/

noncomputable section
open Set Filter Topology MeasureTheory Metric
open NRR.Coordinates

namespace NRR.Localization

variable {d n : ℕ}

local instance productVolumeHaar : Measure.IsAddHaarMeasure (volume : Measure (Space d × ℝ)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure (Space d)).prod (volume : Measure ℝ))
  infer_instance

/-- All analytic choices for a single prescribed body and measure. The
mass and height conditions range over the full convex partition space. -/
structure MomentCylinder (K : ConvexBody (Space d × ℝ))
    (μ : Measure (Space d × ℝ)) (n : ℕ) where
  ρ : Measure (Space d × ℝ)
  finite : IsFiniteMeasure ρ
  ac : ρ ≪ volume
  support : ρ (bodyPoints K)ᶜ = 0
  first : Integrable id ρ
  centered : (∫ q, q ∂ρ) = 0
  a : ℝ
  h : ℝ
  radius_pos : 0 < a
  height_pos : 0 < h
  height_lt_one : h < 1
  inner : solidCylinder a h ⊆ interior (bodyPoints K)
  mass : ∀ S ∈ equalMassPartitions (n := n) K μ, ∀ i, 0 < ρ (bodyPoints (S i))
  height : ∀ S ∈ equalMassPartitions (n := n) K μ, ∀ i,
    |⨍ q in bodyPoints (S i), q.2 ∂ρ| < h

/-- The normalized vertical chord and positive prescribed cell mass suffice
to make all choices uniformly. Absolute continuity allows density gaps. -/
theorem exists_momentCylinder (K : ConvexBody (Space d × ℝ))
    (μ : Measure (Space d × ℝ)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (hK : 0 < μ (bodyPoints K))
    (strip : bodyPoints K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    (axis : ∀ z : ℝ, |z| < 1 → ((0 : Space d),z) ∈ interior (bodyPoints K)) :
    Nonempty (MomentCylinder K μ n) := by
  let s := convexConfigurations '' equalMassPartitions (n := n) K μ
  have compact : IsCompact s :=
    compact_convexConfigurations (horizontalHeight d) K μ hμ hK
  have subsets : ∀ C ∈ s, ∀ i, ConvexLimits.points (C i) ⊆ bodyPoints K := by
    rintro C ⟨S,hS,rfl⟩ i
    rw [← hS.1.covers]
    exact subset_iUnion (fun j => bodyPoints (S j)) i
  have mass : ∀ C ∈ s, ∀ i, 0 < μ (ConvexLimits.points (C i)) := by
    rintro C ⟨S,hS,rfl⟩ i
    change 0 < μ (bodyPoints (S i))
    rw [hS.1.mass_eq_div μ hμ hS.2 i]
    exact ENNReal.div_pos hK.ne' (by simp)
  obtain ⟨ρ,finite,ac,_,supp,first,centered,a,h,ha,hh,h1,inner,bounds⟩ :=
    exists_background_innerCylinder K.val.isCompact strip axis μ hμ s compact subsets mass
  refine ⟨⟨ρ,finite,ac,supp,first,centered,a,h,ha,hh,h1,inner,?_,?_⟩⟩
  · intro S hS i
    exact (bounds (convexConfigurations S) (mem_image_of_mem _ hS) i).1
  · intro S hS i
    exact (bounds (convexConfigurations S) (mem_image_of_mem _ hS) i).2

/-- The localization cylinder may be required to contain any preassigned
closed subsegment of the normalized open chord, for example all quantile
windows. Enlarging its height preserves every strict centroid bound. -/
theorem exists_momentCylinder_above (K : ConvexBody (Space d × ℝ))
    (μ : Measure (Space d × ℝ)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    (hK : 0 < μ (bodyPoints K))
    (strip : bodyPoints K ⊆ univ ×ˢ Icc (-1 : ℝ) 1)
    (axis : ∀ z : ℝ, |z| < 1 → ((0 : Space d),z) ∈ interior (bodyPoints K))
    {hmin : ℝ} (hmin_lt : hmin < 1) :
    ∃ A : MomentCylinder K μ n, hmin < A.h := by
  obtain ⟨A⟩ := exists_momentCylinder (n := n) K μ hμ hK strip axis
  let h := (max A.h hmin + 1) / 2
  have maxlt : max A.h hmin < 1 := max_lt A.height_lt_one hmin_lt
  have oldlt : A.h < h := by
    have := le_max_left A.h hmin
    dsimp [h]
    linarith
  have hh : 0 < h := A.height_pos.trans oldlt
  have h1 : h < 1 := by dsimp [h]; linarith
  obtain ⟨a,ha,inner⟩ := exists_innerCylinder axis hh h1
  refine ⟨⟨A.ρ,A.finite,A.ac,A.support,A.first,A.centered,a,h,ha,hh,h1,inner,
    A.mass,fun S hS i => (A.height S hS i).trans oldlt⟩,?_⟩
  have := le_max_right A.h hmin
  change hmin < h
  dsimp [h]
  linarith

namespace MomentCylinder

variable {K : ConvexBody (Space d × ℝ)} {μ : Measure (Space d × ℝ)}
    (A : MomentCylinder K μ n)

def moment (δ : ℝ) : C(ConvexLimits.ConvexCompact (Space d × ℝ),Space d) :=
  weightedHorizontalMoment A.ρ A.ac
    ((ContinuousLinearMap.fst ℝ (Space d) ℝ).integrable_comp A.first) A.a A.h δ

/-- The total horizontal moment vanishes for every actual partition of K,
independently of its prescribed mass constraints. -/
theorem balanced (δ : ℝ) (S : Fin n → ConvexBody (Space d × ℝ))
    (part : Partition K S) :
    ∑ i, A.moment δ (bodyToConvexCompact (S i)) = 0 := by
  have centered : (∫ q in bodyPoints K, q.1 ∂A.ρ) = 0 := by
    have aeK : ∀ᵐ q ∂A.ρ, q ∈ bodyPoints K := ae_iff.mpr A.support
    rw [Measure.restrict_eq_self_of_ae_mem aeK]
    have H := (ContinuousLinearMap.fst ℝ (Space d) ℝ).integral_comp_comm A.first
    change (∫ q, q.1 ∂A.ρ) = (∫ q, q ∂A.ρ).1 at H
    rw [A.centered] at H
    exact H
  exact weightedHorizontalMoment_balanced A.ρ A.ac
    ((ContinuousLinearMap.fst ℝ (Space d) ℝ).integrable_comp A.first)
    A.a A.h δ (convexConfigurations S) part.disjoint part.covers
    (A.inner.trans interior_subset) centered

/-- Any open neighborhood of all horizontal-clip limits captures every
common zero of the genuine additive moments for small positive tail weight. -/
theorem localizes [IsFiniteMeasure μ] (hμ : μ ≪ volume) (hK : 0 < μ (bodyPoints K))
    (U : Set (Fin n → ConvexLimits.ConvexCompact (Space d × ℝ))) (openU : IsOpen U)
    (slabsInU : ∀ S ∈ equalMassPartitions (n := n) K μ,
      (∀ i, ∃ lo hi : ℝ, lo < hi ∧ bodyPoints (S i) ∩ solidCylinder A.a A.h =
        closedBall 0 A.a ×ˢ Icc lo hi) → convexConfigurations S ∈ U) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ S ∈ equalMassPartitions (n := n) K μ,
        (∀ i, A.moment δ (bodyToConvexCompact (S i)) = 0) → convexConfigurations S ∈ U := by
  letI := A.finite
  let s := convexConfigurations '' equalMassPartitions (n := n) K μ
  have compact : IsCompact s :=
    compact_convexConfigurations (horizontalHeight d) K μ hμ hK
  have mass : ∀ C ∈ s, ∀ i, 0 < A.ρ (ConvexLimits.points (C i)) := by
    rintro C ⟨S,hS,rfl⟩ i
    exact A.mass S hS i
  have height : ∀ C ∈ s, ∀ i,
      |⨍ q in ConvexLimits.points (C i), q.2 ∂A.ρ| < A.h := by
    rintro C ⟨S,hS,rfl⟩ i
    exact A.height S hS i
  have covers : ∀ C ∈ s, solidCylinder A.a A.h ⊆ ⋃ i, ConvexLimits.points (C i) := by
    rintro C ⟨S,hS,rfl⟩
    exact hS.1.covers.symm ▸ A.inner.trans interior_subset
  have disjoint : ∀ C ∈ s, Pairwise fun i j => Disjoint
      (interior (ConvexLimits.points (C i))) (interior (ConvexLimits.points (C j))) := by
    rintro C ⟨S,hS,rfl⟩
    exact hS.1.disjoint
  have slabs : ∀ C ∈ s, (∀ i, ∃ lo hi : ℝ, lo < hi ∧
      ConvexLimits.points (C i) ∩ solidCylinder A.a A.h = closedBall 0 A.a ×ˢ Icc lo hi) → C ∈ U := by
    rintro C ⟨S,hS,rfl⟩ hc
    exact slabsInU S hS hc
  obtain ⟨δ₀,hδ₀,loc⟩ := compact_cylinder_localization A.ρ A.ac
    ((ContinuousLinearMap.fst ℝ (Space d) ℝ).integrable_comp A.first)
    s compact A.radius_pos A.height_pos mass height covers disjoint U openU slabs
  exact ⟨δ₀,hδ₀,fun δ hp hs S hS zero => loc δ hp hs
    (convexConfigurations S) (mem_image_of_mem _ hS) zero⟩

end MomentCylinder

end NRR.Localization
