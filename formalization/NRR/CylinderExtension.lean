import NRR.CylinderRigidity

/-! A common open horizontal face determines the separating hyperplane of
two convex pieces, even away from the cylinder where the face was found. -/

noncomputable section
open Set

namespace NRR.Cylinder
variable {d : ℕ}

/-- Two convex pieces with disjoint interiors that share an open horizontal
face are globally separated by that horizontal plane. The two axis points
fix which of the pieces lies below the face. -/
theorem separated_by_common_horizontal_face
    {A B : Set (Space d × ℝ)} (ca : IsClosed A) (cb : IsClosed B)
    (va : Convex ℝ A) (vb : Convex ℝ B)
    (disj : Disjoint (interior A) (interior B))
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
    {a b t : ℝ} (ha : (0,a) ∈ interior A) (hb : (0,b) ∈ interior B)
    (hab : a < b) (face : ∀ u ∈ D, (u,t) ∈ A ∩ B) :
    (∀ p ∈ A, p.2 ≤ t) ∧ (∀ p ∈ B, t ≤ p.2) := by
  obtain ⟨F,c,hA,hB⟩ :=
    geometric_hahn_banach_open va.interior isOpen_interior vb.interior disj
  have A_le (p) (hp : p ∈ A) : F p ≤ c := by
    apply closure_minimal (fun x hx => (hA x hx).le)
      (isClosed_le F.continuous continuous_const)
    rwa [va.closure_interior_eq_closure_of_nonempty_interior ⟨_,ha⟩, ca.closure_eq]
  have B_ge (p) (hp : p ∈ B) : c ≤ F p := by
    apply closure_minimal hB (isClosed_le continuous_const F.continuous)
    rwa [vb.closure_interior_eq_closure_of_nonempty_interior ⟨_,hb⟩, cb.closure_eq]
  let k := F (0,1)
  have eval (u : Space d) (s : ℝ) : F (u,s) = F (u,0) + s*k := by
    have he : (u,s) = (u,0) + s • ((0,1) : Space d × ℝ) := by ext <;> simp
    rw [he, map_add, map_smul]
    rfl
  have positive : 0 < k := by
    have hlt := (hA _ ha).trans_le (hB _ hb)
    rw [eval 0 a, eval 0 b] at hlt
    by_contra! hk
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab.le) hk]
  have face_eq (u : Space d) (hu : u ∈ D) : F (u,t) = c :=
    le_antisymm (A_le _ (face u hu).1) (B_ge _ (face u hu).2)
  have center_eq : t*k = c := by
    have h := face_eq 0 (interior_subset hD)
    rw [eval] at h
    simpa only [show F ((0 : Space d),0) = 0 from F.map_zero, zero_add] using h
  let L : Space d →ₗ[ℝ] ℝ :=
    F.toLinearMap.comp (LinearMap.inl ℝ (Space d) ℝ)
  have subset_kernel : D ⊆ (LinearMap.ker L : Set (Space d)) := by
    intro u hu
    change F (u,0) = 0
    have h := face_eq u hu
    rw [eval] at h
    linarith
  have kernel_top : LinearMap.ker L = ⊤ :=
    (LinearMap.ker L).eq_top_of_nonempty_interior' ⟨0, interior_mono subset_kernel hD⟩
  have horizontal_zero (u : Space d) : F (u,0) = 0 := by
    change u ∈ LinearMap.ker L
    rw [kernel_top]
    trivial
  constructor
  · rintro ⟨u,s⟩ hp
    have h := A_le _ hp
    rw [eval, horizontal_zero, zero_add, ← center_eq] at h
    exact (mul_le_mul_iff_left₀ positive).mp h
  · rintro ⟨u,s⟩ hp
    have h := B_ge _ hp
    rw [eval, horizontal_zero, zero_add, ← center_eq] at h
    exact (mul_le_mul_iff_left₀ positive).mp h

/-- The horizontal separation found on two adjacent positive-thickness
slabs persists for the entire convex pieces containing those slabs. -/
theorem separated_by_adjacent_horizontal_slabs
    {A B : Set (Space d × ℝ)} (ca : IsClosed A) (cb : IsClosed B)
    (va : Convex ℝ A) (vb : Convex ℝ B)
    (disj : Disjoint (interior A) (interior B))
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
    {a t b : ℝ} (hat : a < t) (htb : t < b)
    (lower : D ×ˢ Icc a t ⊆ A) (upper : D ×ˢ Icc t b ⊆ B) :
    (∀ p ∈ A, p.2 ≤ t) ∧ (∀ p ∈ B, t ≤ p.2) := by
  have ha : (0,(a+t)/2) ∈ interior A := by
    apply interior_mono lower
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hD, by constructor <;> linarith⟩
  have hb : (0,(t+b)/2) ∈ interior B := by
    apply interior_mono upper
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hD, by constructor <;> linarith⟩
  apply separated_by_common_horizontal_face ca cb va vb disj hD ha hb
    (by linarith : (a+t)/2 < (t+b)/2)
  intro u hu
  exact ⟨lower ⟨hu, ⟨hat.le, le_rfl⟩⟩, upper ⟨hu, ⟨le_rfl, htb.le⟩⟩⟩

end NRR.Cylinder
