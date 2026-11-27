import NRR.CubeSectionMidpoint
import NRR.BrunnMinkowskiWeighted
import NRR.BrunnMinkowskiRigidity

/-! Product rigidity of actual high-dimensional partitions. The final
interface discharges both standard Brunn--Minkowski inputs with the proved
three-dimensional inequality and its translation equality theorem. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.CubeProductRigidity
open CubeProductMoments CubeSectionMass CubeSectionTranslation CubeSectionMidpoint

variable {k : ℕ}

/-- The actual cube-root section masses are concave, including every
possibly degenerate boundary section. -/
theorem rootMass_concave {C : Set (Active × Passive k)}
    (compact : IsCompact C) (convex : Convex ℝ C) :
    ConcaveOn ℝ (projection C) (rootMass C) := by
  exact BrunnMinkowskiWeighted.section_root_concave compact convex

theorem midpoint_eq_minkowskiMidpoint (A B : Set Active) :
    midpoint A B = BrunnMinkowskiGeometry.minkowskiMidpoint A B := by
  simp only [CubeSectionMidpoint.midpoint,
    BrunnMinkowskiGeometry.minkowskiMidpoint, smul_add]

theorem neg_mem_passiveCube_iff (u : Passive k) :
    -u ∈ passiveCube k ↔ u ∈ passiveCube k := by
  change ((∀ j, -1 ≤ -u j) ∧ (∀ j, -u j ≤ 1)) ↔
    ((∀ j, -1 ≤ u j) ∧ (∀ j, u j ≤ 1))
  constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> intro j <;>
    have h1 := ha j <;> have h2 := hb j <;> linarith

theorem neg_mem_interior_passiveCube {u : Passive k}
    (hu : u ∈ interior (passiveCube k)) :
    -u ∈ interior (passiveCube k) := by
  apply mem_interior_iff_mem_nhds.mpr
  have near : ∀ᶠ v : Passive k in 𝓝 (-u), -v ∈ passiveCube k :=
    (continuous_neg.tendsto' (-u) u (neg_neg u)).eventually
      (mem_interior_iff_mem_nhds.mp hu)
  filter_upwards [near] with v hv
  exact (neg_mem_passiveCube_iff v).mp hv

/-- All geometric bookkeeping for arbitrary genuine partitions is discharged:
only actual cube-root section concavity and the ordinary three-dimensional
equal-volume midpoint inequality with its translation equality case remain
as inputs. In particular paired section translations are not assumed. -/
theorem eq_prod_of_concavity_and_midpoint_rigidity {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (centered : ∀ i, ∫ p in C i, p.2 ∂volume = (0 : Passive k))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (concavity : ∀ i, ConcaveOn ℝ (projection (C i)) (rootMass (C i)))
    (midpointRigidity : ∀ (A B : Set Active),
      IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B →
      0 < volume.real A → volume.real A = volume.real B →
      volume.real A ≤ volume.real (midpoint A B) ∧
        (volume.real (midpoint A B) = volume.real A →
          ∃ w : Active, B = translate A w)) :
    ∀ i, C i = fiber (C i) 0 ×ˢ passiveCube k := by
  have masses := interior_mass_of_partition_concavity
    hn C hc hv hm centered disj hD cover equal concavity
  have parts := fun u hu => interior_section_partition_of_concavity
    hn C hc hv hm centered disj hD cover equal concavity (u := u) hu
  have zeroCube := zero_mem_interior_passiveCube k
  have central (i) : 0 < volume.real (fiber (C i) 0) :=
    central_mass_pos (hc i) (hv i) (hm i) (centered i)
  have paired (u : Passive k) (hu : u ∈ interior (passiveCube k)) :
      ∃ v : Fin n → Active,
        (∀ i, fiber (C i) u = translate (fiber (C i) 0) (v i)) ∧
          ∀ i, fiber (C i) (-u) = translate (fiber (C i) 0) (-v i) := by
    have hneg := neg_mem_interior_passiveCube hu
    have pair (i : Fin n) : ∃ v : Active,
        fiber (C i) u = translate (fiber (C i) 0) v ∧
        fiber (C i) (-u) = translate (fiber (C i) 0) (-v) := by
      have eq0 : mass (C i) u = mass (C i) 0 :=
        ((masses i).2 u hu).trans ((masses i).2 0 zeroCube).symm
      have eqNeg : mass (C i) u = mass (C i) (-u) :=
        ((masses i).2 u hu).trans ((masses i).2 (-u) hneg).symm
      have pos : 0 < volume.real (fiber (C i) u) := by
        change 0 < mass (C i) u
        rw [eq0]
        exact central i
      obtain ⟨lower,rigid⟩ := midpointRigidity _ _
        (compact_fiber (hc i) u) (compact_fiber (hc i) (-u))
        (convex_fiber (hv i) u) (convex_fiber (hv i) (-u)) pos eqNeg
      have middle := midpoint_fiber_eq_of_volume_lower (hc i) (hv i)
        ((parts 0 zeroCube).2.1 i) u eq0 lower
      have volumeEqual : volume.real (midpoint (fiber (C i) u) (fiber (C i) (-u))) =
          volume.real (fiber (C i) u) := by
        rw [middle]
        exact eq0.symm
      exact paired_fiber_translations_of_midpoint_eq (hv i) u middle (rigid volumeEqual)
    choose v hv using pair
    exact ⟨v,fun i => (hv i).1,fun i => (hv i).2⟩
  exact eq_prod_of_paired_translated_sections
    (passiveCube k) isClosed_Icc (convex_Icc _ _) ⟨0,zeroCube⟩
    (fun _ hu => neg_mem_interior_passiveCube hu)
    D hD C (fun i => (hc i).isClosed) hv
    (fun i p hp => ⟨mem_univ _,(show C i ⊆ D ×ˢ passiveCube k from
      cover ▸ subset_iUnion C i) hp |>.2⟩)
    (fun i => fiber (C i) 0) (fun i => compact_fiber (hc i) 0) central
    (parts 0 zeroCube).1 (fun u hu => (parts u hu).1) paired

/-- Equality of the actual extra first moments supplies the zero passive
centroids required by product rigidity, without imposing them separately. -/
theorem eq_prod_of_equal_passive_moments {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (passiveEqual : ∀ i l (j : Fin k),
      (∫ p in C i, p.2 j ∂volume) = ∫ p in C l, p.2 j ∂volume)
    (concavity : ∀ i, ConcaveOn ℝ (projection (C i)) (rootMass (C i)))
    (midpointRigidity : ∀ (A B : Set Active),
      IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B →
      0 < volume.real A → volume.real A = volume.real B →
      volume.real A ≤ volume.real (midpoint A B) ∧
        (volume.real (midpoint A B) = volume.real A →
          ∃ w : Active, B = translate A w)) :
    ∀ i, C i = fiber (C i) 0 ×ˢ passiveCube k :=
  eq_prod_of_concavity_and_midpoint_rigidity hn C hc hv hm
    (passive_centered_of_equal hn C hc hv disj hD cover passiveEqual)
    disj hD cover equal concavity midpointRigidity

/-- Actual Brunn--Minkowski section concavity discharges the analytic
input of product rigidity. Only the equal-volume midpoint equality case
remains in this intermediate interface. -/
theorem eq_prod_of_equal_passive_moments_and_midpoint_rigidity
    {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (passiveEqual : ∀ i l (j : Fin k),
      (∫ p in C i, p.2 j ∂volume) = ∫ p in C l, p.2 j ∂volume)
    (midpointRigidity : ∀ (A B : Set Active),
      IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B →
      0 < volume.real A → volume.real A = volume.real B →
      volume.real A ≤ volume.real (midpoint A B) ∧
        (volume.real (midpoint A B) = volume.real A →
          ∃ w : Active, B = translate A w)) :
    ∀ i, C i = fiber (C i) 0 ×ˢ passiveCube k :=
  eq_prod_of_equal_passive_moments hn C hc hv hm disj hD cover equal
    passiveEqual (fun i => rootMass_concave (hc i) (hv i)) midpointRigidity

/-- Every genuine equal-volume convex partition of an active body times
the passive cube, fair for the passive first moments, consists of products.
There are no additional Brunn--Minkowski or section-shape hypotheses. -/
theorem eq_prod_of_equal_passive_moments_of_partition
    {n : ℕ} (hn : 0 < n)
    (C : Fin n → Set (Active × Passive k))
    (hc : ∀ i, IsCompact (C i)) (hv : ∀ i, Convex ℝ (C i))
    (hm : ∀ i, 0 < volume.real (C i))
    (disj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    {D : Set Active} (hD : IsCompact D)
    (cover : (⋃ i, C i) = D ×ˢ passiveCube k)
    (equal : ∀ i j, volume.real (C i) = volume.real (C j))
    (passiveEqual : ∀ i l (j : Fin k),
      (∫ p in C i, p.2 j ∂volume) = ∫ p in C l, p.2 j ∂volume) :
    ∀ i, C i = fiber (C i) 0 ×ˢ passiveCube k :=
  eq_prod_of_equal_passive_moments_and_midpoint_rigidity hn C hc hv hm disj hD
    cover equal passiveEqual (fun A B hA hB vA vB pA eq => by
      simpa only [midpoint_eq_minkowskiMidpoint] using
        BrunnMinkowskiRigidity.midpoint_rigidity A B hA hB vA vB pA eq)

end NRR.CubeProductRigidity
