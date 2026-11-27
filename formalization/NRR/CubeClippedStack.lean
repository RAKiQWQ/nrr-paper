import NRR.LayerWindows
import NRR.CubeLayerExclusion
import NRR.CubeHorizontalRigidity
import NRR.CubePlaneCoordinates

noncomputable section
open Set MeasureTheory TopologicalSpace

namespace NRR.CubeFourMomentReadout
open InterfaceChart

def cubeParameters {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    Fin (r+3) → Parameters d := Fin.cases (0,-1) (Fin.lastCases (0,1) P)

@[simp] theorem cubeParameters_zero {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    cubeParameters P 0 = (0,-1) := rfl

@[simp] theorem cubeParameters_last {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    cubeParameters P (Fin.last (r+2)) = (0,1) := by
  change Fin.lastCases (motive := fun _ : Fin (r+2) => Parameters d)
    (0,1) P (Fin.last (r+1)) = (0,1)
  rw [Fin.lastCases_last]

@[simp] theorem cubeParameters_internal {d r : ℕ} (P : Fin (r+1) → Parameters d)
    (i : Fin (r+1)) : cubeParameters P i.castSucc.succ = P i := by
  simp [cubeParameters]

@[simp] theorem cubeParameters_one {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    cubeParameters P 1 = P 0 := cubeParameters_internal P 0

@[simp] theorem cubeParameters_penultimate {d r : ℕ} (P : Fin (r+1) → Parameters d) :
    cubeParameters P (Fin.last (r+1)).castSucc = P (Fin.last r) :=
  cubeParameters_internal P (Fin.last r)

theorem cell_eq_cube_clippedSlab {d r : ℕ} {K : Set (Space d × ℝ)}
    {S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)} (part : ChainPartition K S)
    (strip : K ⊆ univ ×ˢ Icc (-1 : ℝ) 1) (P : Fin (r+1) → Parameters d)
    (caps : ∀ i,prefixCells S i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
      suffixCells S i.succ = K ∩ {x | height (P i) x.1 ≤ x.2}) :
    ∀ i,(S i : Set (Space d × ℝ)) =
      clippedSlab K (cubeParameters P i.castSucc) (cubeParameters P i.succ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have cap := (caps 0).1
    change prefixCells S 0 = _ at cap
    rw [prefixCells_zero] at cap
    change (S 0 : Set (Space d × ℝ)) = clippedSlab K (cubeParameters P 0) (cubeParameters P 1)
    rw [cubeParameters_zero,cubeParameters_one,cap]
    ext x
    change (x ∈ K ∧ x.2 ≤ height (P 0) x.1) ↔
      x ∈ K ∧ (0 : Space d →L[ℝ] ℝ) x.1+(-1) ≤ x.2 ∧ x.2 ≤ height (P 0) x.1
    constructor
    · rintro ⟨hx,ht⟩
      exact ⟨hx,by simp only [ContinuousLinearMap.zero_apply,zero_add]; linarith [(strip hx).2.1],ht⟩
    · exact fun hx => ⟨hx.1,hx.2.2⟩
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · have cap := (caps (Fin.last r)).2
      change suffixCells S (Fin.last (r+1)) = _ at cap
      rw [suffixCells_last] at cap
      change (S (Fin.last (r+1)) : Set (Space d × ℝ)) =
        clippedSlab K (cubeParameters P (Fin.last (r+1)).castSucc)
          (cubeParameters P (Fin.last (r+2)))
      rw [cubeParameters_penultimate,cubeParameters_last,cap]
      ext x
      change (x ∈ K ∧ height (P (Fin.last r)) x.1 ≤ x.2) ↔
        x ∈ K ∧ height (P (Fin.last r)) x.1 ≤ x.2 ∧ x.2 ≤ (0 : Space d →L[ℝ] ℝ) x.1+1
      constructor
      · rintro ⟨hx,ht⟩
        exact ⟨hx,ht,by simp only [ContinuousLinearMap.zero_apply,zero_add]; linarith [(strip hx).2.2]⟩
      · exact fun hx => ⟨hx.1,hx.2.1⟩
    · change (S k.castSucc.succ : Set (Space d × ℝ)) =
        clippedSlab K (cubeParameters P k.castSucc.castSucc.succ)
          (cubeParameters P k.succ.castSucc.succ)
      rw [cubeParameters_internal,cubeParameters_internal]
      exact cell_eq_clippedSlab_of_graph_caps part P caps k.castSucc k.succ rfl


/-- The cap identities and the closed height band already force all cuts to be ordered. -/
theorem heights_ordered_of_cube_caps {r : ℕ}
    (T : Fin (r+2) → NonemptyCompacts (NRR.Space 2 × ℝ))
    (P : Fin (r+1) → Parameters 2)
    (caps : ∀ i, prefixCells T i.castSucc =
      (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1) ∩
        {x | x.2 ≤ height (P i) x.1})
    (band : ∀ i, ∀ u ∈ CubeHorizontalRigidity.square, height (P i) u ∈ Icc (-1 : ℝ) 1) :
    ∀ i j, i ≤ j → ∀ u ∈ CubeHorizontalRigidity.square,
      height (P i) u ≤ height (P j) u := by
  intro i j hij u hu
  have hp : (u, height (P i) u) ∈ prefixCells T i.castSucc := by
    rw [caps]
    exact ⟨⟨hu, band i u hu⟩, by change height (P i) u ≤ height (P i) u; exact le_rfl⟩
  have hq : (u, height (P i) u) ∈ prefixCells T j.castSucc := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨⟨k.val, k.property.trans (by simpa using hij)⟩, hk⟩
  rw [caps] at hq
  exact hq.2

private theorem cube_square_coordinates (u : NRR.Space 2) :
    u ∈ CubeHorizontalRigidity.square ↔ CubePlaneCoordinates.e u ∈ squareBase := by
  simp only [CubeHorizontalRigidity.square, mem_setOf_eq,
    CubePlaneCoordinates.e_apply, squareBase, mem_prod]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ j
    fin_cases j <;> assumption

/-- True cube caps give a stack of full affine graph layers in coordinate space. -/
theorem exists_stack_of_cube_caps {r : ℕ}
    (T : Fin (r+2) → NonemptyCompacts (NRR.Space 2 × ℝ))
    (chain : ChainPartition (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1) T)
    (P : Fin (r+1) → Parameters 2)
    (caps : ∀ i, prefixCells T i.castSucc =
        (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1) ∩
          {x | x.2 ≤ height (P i) x.1} ∧
      suffixCells T i.succ =
        (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1) ∩
          {x | height (P i) x.1 ≤ x.2})
    (band : ∀ i, ∀ u ∈ CubeHorizontalRigidity.square, height (P i) u ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (small : ∀ i, ‖(P i).1‖ ≤ (3 * (2 / (r+2 : ℕ) : ℝ)) * δ)
    (equal : ∀ i j, volume.real (CubePlaneCoordinates.E '' (T i : Set _)) =
      volume.real (CubePlaneCoordinates.E '' (T j : Set _))) :
    ∃ A : EqualVolumeStack (r+2), (∀ j, ‖A.slope j‖ ≤ δ) ∧
      ∀ i, CubePlaneCoordinates.E '' (T i : Set _) =
        cutLayer (2 / (r+2 : ℕ)) A.intercept A.slope i := by
  let m : ℝ := 2 / (r+2 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hm3 : 3*m ≠ 0 := by positivity
  let Q := cubeParameters P
  let t : Fin (r+3) → ℝ := fun j => (Q j).2
  let p : Fin (r+3) → Plane := fun j => (3*m)⁻¹ • CubePlaneCoordinates.planeSlope (Q j).1
  have height_repr (j : Fin (r+3)) (u : Plane) :
      slabHeight m (t j) (p j) u.1 u.2 = height (Q j) (CubePlaneCoordinates.e.symm u) := by
    simp only [slabHeight, t, p, height, CubePlaneCoordinates.height_eq_planeSlope,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp; ring
  have qband (j : Fin (r+3)) (u : NRR.Space 2) (hu : u ∈ CubeHorizontalRigidity.square) :
      height (Q j) u ∈ Icc (-1 : ℝ) 1 := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [Q, height]
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [Q, height]
      · simpa [Q] using band k u hu
  have qorder (i : Fin (r+2)) (u : NRR.Space 2) (hu : u ∈ CubeHorizontalRigidity.square) :
      height (Q i.castSucc) u ≤ height (Q i.succ) u := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [Q, height] using (band 0 u hu).1
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · simpa [Q, height] using (band (Fin.last r) u hu).2
      · change height (cubeParameters P k.castSucc.castSucc.succ) u ≤
          height (cubeParameters P k.succ.castSucc.succ) u
        rw [cubeParameters_internal, cubeParameters_internal]
        exact heights_ordered_of_cube_caps T P (fun i => (caps i).1) band
          k.castSucc k.succ (by change k.val ≤ k.val + 1; omega) u hu
  have repr (i : Fin (r+2)) : CubePlaneCoordinates.E '' (T i : Set _) = cutLayer m t p i := by
    rw [cell_eq_cube_clippedSlab chain (by intro x hx; exact ⟨mem_univ _, hx.2⟩) P caps]
    ext v
    have hs : CubePlaneCoordinates.e.symm v.1 ∈ CubeHorizontalRigidity.square ↔
        v.1 ∈ squareBase := by
      simpa using cube_square_coordinates (CubePlaneCoordinates.e.symm v.1)
    have himg : v ∈ CubePlaneCoordinates.E ''
        clippedSlab (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1)
          (Q i.castSucc) (Q i.succ) ↔
        (CubePlaneCoordinates.e.symm v.1, v.2) ∈
          clippedSlab (CubeHorizontalRigidity.square ×ˢ Icc (-1 : ℝ) 1)
            (Q i.castSucc) (Q i.succ) := by
      constructor
      · rintro ⟨x, hx, hxe⟩
        have he : x = (CubePlaneCoordinates.e.symm v.1, v.2) := by
          apply CubePlaneCoordinates.E.injective
          simpa [CubePlaneCoordinates.E, ContinuousLinearEquiv.prodCongr] using hxe
        simpa [he] using hx
      · intro hx
        refine ⟨(CubePlaneCoordinates.e.symm v.1, v.2), hx, ?_⟩
        simp [CubePlaneCoordinates.E, ContinuousLinearEquiv.prodCongr]
    rw [himg]
    change (_ ∧ _) ↔ _
    simp only [cutLayer, graphSlab, mem_setOf_eq, mem_Icc, height_repr]
    constructor
    · rintro ⟨⟨hu, hz⟩, hl, hh⟩
      exact ⟨(hs.mp hu).1, (hs.mp hu).2, hl, hh⟩
    · rintro ⟨hx, hy, hl, hh⟩
      have hu := hs.mpr ⟨hx, hy⟩
      exact ⟨⟨hu, (qband _ _ hu).1.trans hl, hh.trans (qband _ _ hu).2⟩, hl, hh⟩
  have psmall (j : Fin (r+3)) : ‖p j‖ ≤ δ := by
    have bound (k : Fin (r+1)) :
        ‖(3*m)⁻¹ • CubePlaneCoordinates.planeSlope (P k).1‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity : 0 < 3*m))]
      have hn : ‖CubePlaneCoordinates.planeSlope (P k).1‖ ≤ ‖(P k).1‖ := by
        rw [Prod.norm_def]
        exact max_le (CubePlaneCoordinates.abs_planeSlope_fst_le _)
          (CubePlaneCoordinates.abs_planeSlope_snd_le _)
      have hb : ‖CubePlaneCoordinates.planeSlope (P k).1‖ ≤ (3*m)*δ := hn.trans (small k)
      calc
        _ ≤ (3*m)⁻¹ * ((3*m)*δ) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = δ := by field_simp
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [p, Q, CubePlaneCoordinates.planeSlope] using hδ
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · change ‖p (Fin.last (r+2))‖ ≤ δ
        simpa [p, Q, CubePlaneCoordinates.planeSlope] using hδ
      · simpa [p, Q] using bound k
  let A : EqualVolumeStack (r+2) := {
    intercept := t
    slope := p
    bottom := by simp [t, Q]
    top := by simp [t, Q]
    lowerFace := by simp [p, Q, CubePlaneCoordinates.planeSlope]
    upperFace := by simp [p, Q, CubePlaneCoordinates.planeSlope]
    ordered := by
      intro i u hu
      rw [height_repr, height_repr]
      apply qorder
      apply (cube_square_coordinates _).mpr
      simpa using hu
    equalVolume := by intro i j; rw [← repr i, ← repr j]; exact equal i j }
  exact ⟨A, psmall, repr⟩

end NRR.CubeFourMomentReadout

