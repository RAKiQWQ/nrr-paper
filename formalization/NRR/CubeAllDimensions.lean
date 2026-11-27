import NRR.CubePolynomialProductPartitions
import NRR.CubeProductRigidity

/-! The same two rational polynomials and the passive first moments on
the full Hausdorff space of compact convex sets in every product dimension. -/

noncomputable section
open Set Topology MeasureTheory

namespace NRR.CubeAllDimensions
open CubeProductMoments CubeSectionMass RationalMomentApproximation

abbrev Ambient (k : ℕ) := Active × Passive k

instance ambientHaar (k : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (Ambient k)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Passive k)) :=
    isAddHaarMeasure_volume_pi (Fin k)
  rw [Measure.volume_eq_prod]
  infer_instance

theorem continuous_density (i : Fin 4) : Continuous (density i) := by
  change Continuous (fun x : Active => density i x)
  fin_cases i <;> simp [density] <;> fun_prop

/-- The actual four normalized volume moments of any compact convex set. -/
def volumeMoments (k : ℕ) (n : ℝ) (C : Set (Ambient k)) : Fin 4 → ℝ :=
  fun a => n / 2 ^ (k+3) * ∫ p in C, density a p.1 ∂volume

theorem continuous_volumeMoments (k : ℕ) (n : ℝ) :
    Continuous (fun C : ConvexLimits.ConvexCompact (Ambient k) =>
      volumeMoments k n (ConvexLimits.points C)) := by
  apply continuous_pi
  intro a
  apply Continuous.mul continuous_const
  exact ConvexLimits.continuous_integral_of_locallyIntegrable
    volume volume Measure.AbsolutelyContinuous.rfl
    (((continuous_density a).comp continuous_fst).locallyIntegrable)

/-- Each polynomial readout is defined and continuous even on sets of
zero ambient volume. -/
def polynomialFeature (k : ℕ) (n : ℝ) (P : Fin 2 → MvPolynomial (Fin 4) ℚ)
    (a : Fin 2) : C(ConvexLimits.ConvexCompact (Ambient k), ℝ) :=
  ⟨fun C => eval (P a) (volumeMoments k n (ConvexLimits.points C)),
    (continuous_eval (P a)).comp (continuous_volumeMoments k n)⟩

def passiveFeature (k : ℕ) (j : Fin k) :
    C(ConvexLimits.ConvexCompact (Ambient k), ℝ) :=
  ⟨fun C => ∫ p in ConvexLimits.points C, p.2 j ∂volume,
    ConvexLimits.continuous_integral_of_locallyIntegrable
      volume volume Measure.AbsolutelyContinuous.rfl
      (show Continuous (fun p : Ambient k => p.2 j) by fun_prop).locallyIntegrable⟩

/-- Exactly `k+2 = (k+3)-1` real continuous characteristics: the two
fixed polynomial readouts followed by the passive coordinate moments. -/
def characteristics (k : ℕ) (n : ℝ) (P : Fin 2 → MvPolynomial (Fin 4) ℚ) :
    Fin (k+2) → C(ConvexLimits.ConvexCompact (Ambient k), ℝ) :=
  fun a => if h : a.val < 2 then polynomialFeature k n P ⟨a.val,h⟩
    else passiveFeature k ⟨a.val-2,by omega⟩

def polynomialIndex (k : ℕ) (a : Fin 2) : Fin (k+2) := ⟨a.val,by omega⟩
def passiveIndex (k : ℕ) (j : Fin k) : Fin (k+2) := ⟨j.val+2,by omega⟩

@[simp] theorem characteristics_polynomial (k : ℕ) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (a : Fin 2) :
    characteristics k n P (polynomialIndex k a) = polynomialFeature k n P a := by
  simp [characteristics, polynomialIndex, a.isLt]

@[simp] theorem characteristics_passive (k : ℕ) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (j : Fin k) :
    characteristics k n P (passiveIndex k j) = passiveFeature k j := by
  simp [characteristics, passiveIndex]

@[simp] theorem volumeMoments_product (k : ℕ) (n : ℝ) (B : Set Active) :
    volumeMoments k n (B ×ˢ passiveCube k) = moments3 n B :=
  productMoments_eq k n B

theorem compact_activeCube : IsCompact CubePlaneCoordinates.coordinateCube :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

/-- A single pair, chosen solely from `n`, rejects every actual convex
partition in every dimension once the passive moments are fair. The same
strict positive gap works in all passive dimensions. -/
theorem exists_polynomials_for_all_actual_partitions (n : ℕ)
    (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ (k : ℕ) (C : Fin n → Set (Ambient k)),
        (∀ i, IsCompact (C i)) → (∀ i, Convex ℝ (C i)) →
        (∀ i, 0 < volume.real (C i)) →
        Pairwise (fun i j => Disjoint (interior (C i)) (interior (C j))) →
        (⋃ i, C i) = CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k →
        (∀ i j, volume.real (C i) = volume.real (C j)) →
        (∀ i l (j : Fin k), (∫ p in C i, p.2 j ∂volume) =
          ∫ p in C l, p.2 j ∂volume) →
        ∃ i j a, γ < |eval (P a) (volumeMoments k n (C i)) -
          eval (P a) (volumeMoments k n (C j))| := by
  obtain ⟨P,γ,hγ,gap⟩ :=
    CubePolynomialProductPartitions.exists_polynomials_for_actual_sets n hn hpow
  refine ⟨P,γ,hγ,?_⟩
  intro k C compact convex positive disjoint cover equal passiveEqual
  have hn0 : 0 < n := by omega
  have centered := passive_centered_of_equal hn0 C compact convex disjoint
    compact_activeCube cover passiveEqual
  have sections := interior_section_partition_of_concavity hn0 C compact convex positive
    centered disjoint compact_activeCube cover equal
    (fun i => CubeProductRigidity.rootMass_concave (compact i) (convex i))
    (zero_mem_interior_passiveCube k)
  have products := CubeProductRigidity.eq_prod_of_equal_passive_moments_of_partition
    hn0 C compact convex positive disjoint compact_activeCube cover equal passiveEqual
  obtain ⟨i,j,a,h⟩ := gap (fun i => fiber (C i) 0)
    (fun i => compact_fiber (compact i) 0) (fun i => convex_fiber (convex i) 0)
    sections.2.1 sections.1.covers sections.1.disjoint
    (fun i j => (sections.2.2 i).trans (sections.2.2 j).symm)
  have moments (l : Fin n) : volumeMoments k n (C l) = moments3 n (fiber (C l) 0) :=
    (congrArg (volumeMoments k n) (products l)).trans
      (volumeMoments_product k n (fiber (C l) 0))
  refine ⟨i,j,a,?_⟩
  simpa only [moments i, moments j] using h

/-- The domain of every characteristic is the entire Hausdorff space,
including lower-dimensional nonempty compact convex sets. For each `n`
the same polynomial pair supplies exactly dimension minus one continuous
characteristics, excluding all fair equal-volume convex cube partitions. -/
theorem exists_characteristics_for_all_dimensions (n : ℕ)
    (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    ∃ P : Fin 2 → MvPolynomial (Fin 4) ℚ,
      ∀ (k : ℕ) (C : Fin n → ConvexLimits.ConvexCompact (Ambient k)),
        (∀ i, (interior (ConvexLimits.points (C i))).Nonempty) →
        Pairwise (fun i j => Disjoint (interior (ConvexLimits.points (C i)))
          (interior (ConvexLimits.points (C j)))) →
        (⋃ i, ConvexLimits.points (C i)) =
          CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k →
        (∀ i j, volume.real (ConvexLimits.points (C i)) =
          volume.real (ConvexLimits.points (C j))) →
        ∃ a i j, characteristics k n P a (C i) ≠ characteristics k n P a (C j) := by
  classical
  obtain ⟨P,γ,hγ,gap⟩ := exists_polynomials_for_all_actual_partitions n hn hpow
  refine ⟨P,?_⟩
  intro k C full disjoint cover equal
  by_contra! fair
  have passiveEqual (i l : Fin n) (j : Fin k) :
      (∫ p in ConvexLimits.points (C i), p.2 j ∂volume) =
        ∫ p in ConvexLimits.points (C l), p.2 j ∂volume := by
    simpa only [characteristics_passive, passiveFeature, ContinuousMap.coe_mk]
      using fair (passiveIndex k j) i l
  have positive (i : Fin n) : 0 < volume.real (ConvexLimits.points (C i)) :=
    ENNReal.toReal_pos
      (ne_of_gt (Measure.measure_pos_of_nonempty_interior volume (full i)))
      (C i).val.isCompact.measure_lt_top.ne
  obtain ⟨i,j,a,h⟩ := gap k (fun i => ConvexLimits.points (C i))
    (fun i => (C i).val.isCompact) (fun i => (C i).property)
    positive disjoint cover equal passiveEqual
  have he := fair (polynomialIndex k a) i j
  simp only [characteristics_polynomial, polynomialFeature, ContinuousMap.coe_mk] at he
  rw [he, sub_self, abs_zero] at h
  exact (not_lt_of_ge hγ.le) h

end NRR.CubeAllDimensions
