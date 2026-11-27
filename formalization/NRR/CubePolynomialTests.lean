import NRR.CubeLayerExclusion
import NRR.RationalMomentApproximation

/-! Global four-moment polynomial tests from local affine charts. -/

noncomputable section
open Set Filter Topology

namespace NRR.CubeFourMomentReadout

open CubeMomentCorrection RationalMomentApproximation

private def coordinateInput (x : Fin 4 → ℝ) : Input := ((x 0,x 1),(x 2,x 3))

private theorem coordinateInput_fourCoordinates (x : Input) : coordinateInput (fourCoordinates x) = x :=
  rfl

/-- The compact set on which approximation is needed is the union of the
actual cell moment images. A complex-valued readout gives two rational polynomials. -/
theorem rationalize_cube_test {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (cell : Fin n → C(X,Input)) (G : C(Input,ℂ))
    (reject : ∀ x, ∃ i j, G (cell i x) ≠ G (cell j x)) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ x, ∃ i j k, γ < |eval (P k) (fourCoordinates (cell i x)) -
        eval (P k) (fourCoordinates (cell j x))| := by
  let c (i : Fin n) := fun x : X => fourCoordinates (cell i x)
  have cont (i) : Continuous (c i) := continuous_fourCoordinates.comp (cell i).continuous
  let K := ⋃ i, Set.range (c i)
  have hK : IsCompact K := isCompact_iUnion fun i => isCompact_range (cont i)
  let z (i : Fin n) : C(X,K) := ⟨fun x => ⟨c i x, mem_iUnion.mpr ⟨i, x, rfl⟩⟩,
    (cont i).subtype_mk _⟩
  have coord (i : Fin 4) : Continuous (fun u : K => u.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  let read : C(K,ℂ) := G.comp ⟨fun u => coordinateInput u.val,
    ((coord 0).prodMk (coord 1)).prodMk ((coord 2).prodMk (coord 3))⟩
  let f : Fin 2 → C(K,ℝ) := ![⟨fun u => (read u).re, Complex.continuous_re.comp read.continuous⟩,
    ⟨fun u => (read u).im, Complex.continuous_im.comp read.continuous⟩]
  have excluded (x : X) : ∃ i j k, f k (z i x) ≠ f k (z j x) := by
    obtain ⟨i,j,ne⟩ := reject x
    by_cases hr : (G (cell i x)).re = (G (cell j x)).re
    · exact ⟨i,j,1,fun hi => ne (Complex.ext hr hi)⟩
    · exact ⟨i,j,0,hr⟩
  obtain ⟨P,γ,hγ,gap⟩ := exists_two_rational_four_moment_polynomials K hK z f univ
    isCompact_univ (fun x _ => excluded x)
  exact ⟨P,γ,hγ,fun x => gap x (mem_univ x)⟩

/-- Only the geometry near partitions with zero horizontal moments is needed:
on the compact complement the unperturbed planar test has a uniform gap. -/
theorem rational_cube_tests_of_local_stacks {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : ℕ) (hn : ¬ IsPrimePow (r+2)) (cell : Fin (r+2) → C(X,Input))
    (balanced : ∀ x, ∑ i, horizontal (cell i x) = 0)
    (charts : ∀ δ > (0 : ℝ), ∀ x, (∀ i, horizontal (cell i x) = 0) →
      ∀ᶠ y in 𝓝 x, ∃ (A : EqualVolumeStack (r+2)) (σ : Equiv.Perm (Fin (r+2))),
        (∀ j, ‖A.slope j‖ ≤ δ) ∧ ∀ i, cell (σ i) y = A.moments i) :
    ∃ (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (γ : ℝ), 0 < γ ∧
      ∀ x, ∃ i j k, γ < |eval (P k) (fourCoordinates (cell i x)) -
        eval (P k) (fourCoordinates (cell j x))| := by
  classical
  obtain ⟨δ, F, hδ, rigidity, tests⟩ := exists_cube_layer_tests r hn
  let U := {y | ∃ (A : EqualVolumeStack (r+2)) (σ : Equiv.Perm (Fin (r+2))),
    (∀ j, ‖A.slope j‖ ≤ δ) ∧ ∀ i, cell (σ i) y = A.moments i}
  have base (x) (hx : x ∈ (interior U)ᶜ) : ∃ i j, F (cell i x) ≠ F (cell j x) := by
    by_contra! fair
    exact hx (mem_interior_iff_mem_nhds.mpr
      (charts δ hδ x (rigidity _ (balanced x) fair)))
  obtain ⟨ε, hε, stable⟩ := Stability.uniform_rejection cell F (interior U)ᶜ
    isOpen_interior.isClosed_compl.isCompact base
  obtain ⟨G, close, localTest⟩ := tests ε hε
  apply rationalize_cube_test cell G
  intro x
  by_cases hx : x ∈ interior U
  · obtain ⟨A, σ, hs, repr⟩ := interior_subset hx
    obtain ⟨i,j,ne⟩ := localTest A hs
    exact ⟨σ i,σ j,by simpa only [repr] using ne⟩
  · exact stable G close x hx

end NRR.CubeFourMomentReadout
