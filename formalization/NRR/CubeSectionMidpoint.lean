import NRR.CubeSectionRigidity

/-! Actual midpoint sections and the geometric conversion from ordinary
Brunn--Minkowski equality to paired translations about the central section. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.CubeSectionMidpoint
open CubeProductMoments CubeSectionMass CubeSectionTranslation

/-- Minkowski midpoint, as the actual image of a product of sets. -/
def midpoint (A B : Set Active) : Set Active :=
  (fun p : Active × Active => (1/2 : ℝ) • p.1 + (1/2 : ℝ) • p.2) '' (A ×ˢ B)

theorem compact_midpoint {A B : Set Active}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (midpoint A B) :=
  (hA.prod hB).image (by fun_prop)

theorem convex_midpoint {A B : Set Active}
    (hA : Convex ℝ A) (hB : Convex ℝ B) : Convex ℝ (midpoint A B) := by
  exact (hA.prod hB).linear_image
    ((1/2 : ℝ) • LinearMap.fst ℝ Active Active +
      (1/2 : ℝ) • LinearMap.snd ℝ Active Active)

@[simp] theorem translate_zero (B : Set Active) : translate B 0 = B := by
  simp [translate]

theorem translate_translate (B : Set Active) (u v : Active) :
    translate (translate B u) v = translate B (u+v) := by
  simp only [translate, image_image]
  congr 1
  funext x
  exact add_assoc x u v

/-- A convex set and one of its translates have precisely the translated
midpoint set. This is a set identity, not just a volume identity. -/
theorem midpoint_translate_self {A : Set Active} (hA : Convex ℝ A) (v : Active) :
    midpoint A (translate A v) = translate A ((1/2 : ℝ) • v) := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    obtain ⟨c,hc,rfl⟩ := hb
    refine ⟨(1/2 : ℝ) • a + (1/2 : ℝ) • c,
      hA ha hc (by norm_num) (by norm_num) (by norm_num), ?_⟩
    module
  · rintro ⟨a,ha,rfl⟩
    refine ⟨(a,a+v),⟨ha,⟨a,ha,rfl⟩⟩,?_⟩
    dsimp
    module

/-- Convexity of the original body places the actual opposite-fiber
midpoint inside the central fiber. -/
theorem midpoint_fiber_subset {k : ℕ} {C : Set (Active × Passive k)}
    (hv : Convex ℝ C) (u : Passive k) :
    midpoint (fiber C u) (fiber C (-u)) ⊆ fiber C 0 := by
  rintro _ ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  have h := hv hx hy (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have hz : (1/2 : ℝ) • u + (1/2 : ℝ) • (-u) = 0 := by module
  change ((1/2 : ℝ) • x + (1/2 : ℝ) • y,
    (1/2 : ℝ) • u + (1/2 : ℝ) • (-u)) ∈ C at h
  simpa only [hz] using h

/-- In a constant-volume fiber family the Brunn--Minkowski lower bound
forces equality of the entire midpoint with the central convex section. -/
theorem midpoint_fiber_eq_of_volume_lower {k : ℕ}
    {C : Set (Active × Passive k)} (hc : IsCompact C) (hv : Convex ℝ C)
    (full0 : (interior (fiber C 0)).Nonempty) (u : Passive k)
    (equal : mass C u = mass C 0)
    (lower : mass C u ≤ volume.real (midpoint (fiber C u) (fiber C (-u)))) :
    midpoint (fiber C u) (fiber C (-u)) = fiber C 0 := by
  have hm := compact_midpoint (compact_fiber hc u) (compact_fiber hc (-u))
  have h0 := compact_fiber hc (0 : Passive k)
  have sub := midpoint_fiber_subset hv u
  have upper : volume.real (midpoint (fiber C u) (fiber C (-u))) ≤
      volume.real (fiber C 0) :=
    measureReal_mono sub h0.measure_lt_top.ne
  have realEq : volume.real (midpoint (fiber C u) (fiber C (-u))) =
      volume.real (fiber C 0) := le_antisymm upper (by
        change mass C 0 ≤ _
        rw [← equal]
        exact lower)
  have measureEq : volume (midpoint (fiber C u) (fiber C (-u))) =
      volume (fiber C 0) :=
    (ENNReal.toReal_eq_toReal_iff' hm.measure_lt_top.ne h0.measure_lt_top.ne).mp realEq
  exact eq_of_subset_of_measure_eq volume hm.isClosed h0.isClosed (convex_fiber hv 0)
    full0 sub h0.measure_lt_top.ne measureEq

/-- Equal-volume Brunn--Minkowski rigidity initially identifies the two
opposite fibers only up to a translation. Their actual midpoint identity
then normalizes them to opposite translations of the central section. -/
theorem paired_fiber_translations_of_midpoint_eq {k : ℕ}
    {C : Set (Active × Passive k)} (hv : Convex ℝ C) (u : Passive k)
    (mid : midpoint (fiber C u) (fiber C (-u)) = fiber C 0)
    (translation : ∃ w : Active, fiber C (-u) = translate (fiber C u) w) :
    ∃ v : Active, fiber C u = translate (fiber C 0) v ∧
      fiber C (-u) = translate (fiber C 0) (-v) := by
  obtain ⟨w,hw⟩ := translation
  have middle : fiber C 0 = translate (fiber C u) ((1/2 : ℝ) • w) := by
    rw [← mid,hw,midpoint_translate_self (convex_fiber hv u)]
  refine ⟨-((1/2 : ℝ) • w), ?_, ?_⟩
  · rw [middle,translate_translate]
    simp
  · rw [middle,translate_translate,hw]
    congr 1
    module

end NRR.CubeSectionMidpoint
