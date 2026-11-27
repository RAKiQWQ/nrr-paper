import NRR.OddLoop
import NRR.AngularPrescription
import NRR.PlanarAssembly

/-! Unconditional realization of the binomial profile and the resulting
two-interface planar correction for every non-prime-power block count. -/

noncomputable section
open Set Topology
open scoped unitInterval

namespace NRR.AngularMap

open Surface AngularLoops

theorem realize_degreeProfile {n : ℕ} (hn : 2 ≤ n) (a : ℕ → ℤ) :
    ∃ (h : ℂ ≃ₜ ℂ) (avoid : ∀ z ≠ 0, ∀ j ≤ n, LocalModel.branchSum h n j z ≠ 0),
      h 0 = 0 ∧ (∀ z, h z - h (-z) = 2*z) ∧
      (∀ r : ℝ, 0 < r → ∀ z, h ((r:ℂ)*z) = (r:ℂ)*h z) ∧
      (∀ t : I, Function.Injective (fun z => straightAction h (t,z))) ∧
      ∀ j (hj : j ≤ n), complexWinding (branchLoop h n j)
        (fun u => avoid u u.coe_ne_zero j hj) = (Binomial.degreeProfile n a j : ℝ) := by
  obtain ⟨δ, hδ, _, p, hp⟩ := exists_binomial_half_profile hn a
  let hQ := profilePunctures_neg (by omega : 0 < n)
  let P := doubledLoop hQ p
  let c (i : Fin (n+1)) := center n i.val
  have mem (j : ℕ) (hj : j ≤ n) : center n j ∈ profilePunctures n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  have miss (i : Fin (n+1)) (u : Circle) : shifted P (c i) u ≠ 0 :=
    doubledLoop_avoids hQ p _ (mem i.val (by omega)) u
  obtain ⟨coords, avoid, hw⟩ := approximate_loop P (doubledLoop_odd hQ p)
    (fun u => (circleOfPath (doubled hQ p) u).property.1) c miss
  have avoid' (j : ℕ) (hj : j ≤ n) (u : Circle) :
      shifted coords.loop (center n j) u ≠ 0 := avoid ⟨j, by omega⟩ u
  obtain ⟨h, hnz, hzero, hdiff, hhom, hinj, hwind⟩ :=
    realize_coordinates coords (by omega) avoid'
  refine ⟨h, hnz, hzero, hdiff, hhom, hinj, fun j hj => ?_⟩
  rw [hwind j hj]
  have wind := hw (⟨j, by omega⟩ : Fin (n+1))
  change complexWinding (shifted coords.loop (center n j)) _ =
    complexWinding (shifted P (center n j)) _ at wind
  rw [wind]
  have pathwind := doubledLoop_winding hQ p (center n j) (mem j hj)
  change complexWinding (shifted P (center n j)) _ = _ at pathwind
  rw [pathwind, hp j hj]
  ring

end NRR.AngularMap

namespace NRR.LocalModel

open Surface RootSums

/-- All angular and surface witnesses are constructed. This is a planar
local-model existence theorem, not yet a theorem about convex partitions. -/
theorem exists_planar_correction (r : ℕ) (hn : ¬ IsPrimePow (r+2)) :
    ∃ (h : ℂ ≃ₜ ℂ), h 0 = 0 ∧
      (∀ z, h z - h (-z) = 2*z) ∧
      (∀ t : ℝ, 0 < t → ∀ z, h ((t:ℂ)*z) = (t:ℂ)*h z) ∧
      (∀ z ≠ 0, ∀ j ≤ r+2, branchSum h (r+2) j z ≠ 0) ∧
      ∃ (M : ℝ) (D : C(ℂ × ℂ, ℂ)), 0 < M ∧ (∀ y, ‖D y‖ ≤ M) ∧
        ∀ (w : Fin (r+1) → ℂ) (w₂ q : ℂ), (∑ i, w i) + w₂ = 0 →
          (∀ i, squareTest h (w i) - shift i = q) →
          squareTest h w₂ + D (w 0, (∑ i, w i) - w 0) ≠ q := by
  obtain ⟨a, correction⟩ := planar_correction_of_winding_realization r hn
  obtain ⟨h, avoid, hzero, hdiff, hhom, hinj, degrees⟩ :=
    AngularMap.realize_degreeProfile (by omega : 2 ≤ r+2) a
  refine ⟨h, hzero, hdiff, hhom, avoid, ?_⟩
  exact correction h hzero hdiff hhom (straightAction h) hinj
    (fun z => by simp [straightAction])
    (fun z => by simp [straightAction]) avoid degrees

end NRR.LocalModel
