import NRR.Partitions
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.MetricSpace.Thickening

/-! Interfaces of convex partitions whose nonadjacent cells are disjoint. -/

open Set Topology Filter
noncomputable section

namespace NRR.CutChart

variable {d n : ℕ} {K : Body d} {S : Fin n → Body d}

def ChainDisjoint (S : Fin n → Body d) : Prop :=
  ∀ i j, i.val + 1 < j.val → Disjoint (S i).points (S j).points

def prefixCells (S : Fin n → Body d) (k : Fin n) : Set (Space d) :=
  ⋃ j : {j : Fin n // j ≤ k}, (S j.val).points

def suffixCells (S : Fin n → Body d) (k : Fin n) : Set (Space d) :=
  ⋃ j : {j : Fin n // k ≤ j}, (S j.val).points

private theorem isClosed_cell (C : Body d) : IsClosed C.points := C.val.isCompact.isClosed

private theorem cell_subset (p : BodyPartition K S) (i : Fin n) : (S i).points ⊆ K.points := by
  rw [← p.covers]
  exact subset_iUnion (fun j : Fin n => (S j).points) i

private theorem closure_cell_interior (C : Body d) : closure (interior C.points) = C.points :=
  (C.property.1.closure_interior_eq_closure_of_nonempty_interior C.property.2).trans
    (isClosed_cell C).closure_eq

/-- The open half of K containing a point of L cannot also meet R, when
the common points of the two closed pieces all lie on the separating plane. -/
private theorem strict_side_disjoint {L R : Set (Space d)} (f : Space d →L[ℝ] ℝ) (u : ℝ)
    (cover : K.points ⊆ L ∪ R) (hL : IsClosed L) (hR : IsClosed R)
    (plane : ∀ x ∈ L ∩ R, f x = u) (x₀ : Space d) (hK₀ : x₀ ∈ K.points)
    (hL₀ : x₀ ∈ L) (h₀ : f x₀ < u) {x : Space d} (hx : x ∈ K.points) (h : f x < u) :
    x ∉ R := by
  intro hr
  let A := K.points ∩ {z | f z < u}
  have conn : IsPreconnected A :=
    (K.property.1.inter (convex_halfSpace_lt f.toLinearMap.isLinear _)).isPreconnected
  obtain ⟨y, hy, hp⟩ := isPreconnected_closed_iff.mp conn L R hL hR
    (inter_subset_left.trans cover) ⟨x₀, ⟨hK₀,h₀⟩, hL₀⟩ ⟨x, ⟨hx,h⟩, hr⟩
  exact (ne_of_lt hy.2) (plane y hp)

/-- Recover points on the cutting plane by joining them to a strict point
and taking the closure inside the closed member of the cover. -/
private theorem closed_side_subset {L R : Set (Space d)} (f : Space d →L[ℝ] ℝ) (u : ℝ)
    (cover : K.points ⊆ L ∪ R) (hL : IsClosed L) (hR : IsClosed R)
    (plane : ∀ x ∈ L ∩ R, f x = u) (x₀ : Space d) (hK₀ : x₀ ∈ K.points)
    (hL₀ : x₀ ∈ L) (h₀ : f x₀ < u) :
    K.points ∩ {z | f z ≤ u} ⊆ L := by
  rintro x ⟨hx, hle⟩
  have seg : openSegment ℝ x₀ x ⊆ L := by
    rintro _ ⟨a,b,ha,hb,hab,rfl⟩
    have hk := K.property.1 hK₀ hx ha.le hb.le hab
    have hlt : f (a • x₀ + b • x) < u := by
      simp only [map_add, map_smul, smul_eq_mul]
      change f x ≤ u at hle
      calc
        a * f x₀ + b * f x < a * u + b * u :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h₀ ha)
            (mul_le_mul_of_nonneg_left hle hb.le)
        _ = u := by rw [← add_mul, hab, one_mul]
    exact (cover hk).resolve_right (strict_side_disjoint f u cover hL hR plane x₀ hK₀ hL₀ h₀ hk hlt)
  exact hL.closure_subset (closure_mono seg (segment_subset_closure_openSegment (right_mem_segment ..)))

theorem prefix_suffix_cover (p : BodyPartition K S) (i j : Fin n) (hij : j.val = i.val+1) :
    prefixCells S i ∪ suffixCells S j = K.points := by
  apply Subset.antisymm
  · exact union_subset (iUnion_subset fun k => cell_subset p k.val)
      (iUnion_subset fun k => cell_subset p k.val)
  · intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (p.covers.symm ▸ hx)
    by_cases hki : k ≤ i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k,hki⟩,hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,by omega⟩,hk⟩)

theorem prefix_suffix_overlap (chain : ChainDisjoint S) (i j : Fin n) (hij : j.val = i.val+1) :
    prefixCells S i ∩ suffixCells S j = (S i).points ∩ (S j).points := by
  apply Subset.antisymm
  · rintro x ⟨hl,hr⟩
    obtain ⟨⟨k,hk⟩,hxk⟩ := mem_iUnion.mp hl
    obtain ⟨⟨l,hl⟩,hxl⟩ := mem_iUnion.mp hr
    change x ∈ (S k).points at hxk
    change x ∈ (S l).points at hxl
    have hn : ¬ k.val+1 < l.val := fun he => disjoint_left.mp (chain k l he) hxk hxl
    obtain rfl : k = i := Fin.ext (by omega)
    obtain rfl : l = j := Fin.ext (by omega)
    exact ⟨hxk,hxl⟩
  · rintro x ⟨hi,hj⟩
    exact ⟨mem_iUnion.mpr ⟨⟨i,le_rfl⟩,hi⟩,mem_iUnion.mpr ⟨⟨j,le_rfl⟩,hj⟩⟩

/-- Every separator strict on the adjacent interiors splits the entire ordered
partition into two closed hyperplane caps. -/
theorem caps_of_separator (p : BodyPartition K S) (chain : ChainDisjoint S)
    (i j : Fin n) (hij : j.val = i.val + 1) (f : Space d →L[ℝ] ℝ) (v : ℝ)
    (hi : ∀ x ∈ interior (S i).points, f x < v)
    (hj : ∀ x ∈ interior (S j).points, v < f x) :
    prefixCells S i = K.points ∩ {x | f x ≤ v} ∧
      suffixCells S j = K.points ∩ {x | v ≤ f x} := by
  let L := prefixCells S i
  let R := suffixCells S j
  have hL : IsClosed L := isClosed_iUnion_of_finite fun k => isClosed_cell (S k.val)
  have hR : IsClosed R := isClosed_iUnion_of_finite fun k => isClosed_cell (S k.val)
  have eq : L ∪ R = K.points := prefix_suffix_cover p i j hij
  have leq : (S i).points ⊆ {x | f x ≤ v} := by
    rw [← closure_cell_interior (S i)]
    exact closure_minimal (fun x hx => (hi x hx).le) (isClosed_le f.continuous continuous_const)
  have geq : (S j).points ⊆ {x | v ≤ f x} := by
    rw [← closure_cell_interior (S j)]
    exact closure_minimal (fun x hx => (hj x hx).le) (isClosed_le continuous_const f.continuous)
  have plane (x : Space d) (hx : x ∈ L ∩ R) : f x = v := by
    rw [show L ∩ R = _ from prefix_suffix_overlap chain i j hij] at hx
    exact le_antisymm (leq hx.1) (geq hx.2)
  obtain ⟨lo,hlo⟩ := (S i).property.2
  obtain ⟨up,hup⟩ := (S j).property.2
  have hiL : lo ∈ L := mem_iUnion.mpr ⟨⟨i,le_rfl⟩,interior_subset hlo⟩
  have hjR : up ∈ R := mem_iUnion.mpr ⟨⟨j,le_rfl⟩,interior_subset hup⟩
  have hiK := cell_subset p i (interior_subset hlo)
  have hjK := cell_subset p j (interior_subset hup)
  have eq' : R ∪ L = K.points := (union_comm ..).trans eq
  have plane' (x : Space d) (hx : x ∈ R ∩ L) : (-f) x = -v := by
    simp [plane x ⟨hx.2,hx.1⟩]
  have h₀ : (-f) up < -v := neg_lt_neg (hj up hup)
  have left := closed_side_subset f v eq.ge hL hR plane lo hiK hiL (hi lo hlo)
  have right := closed_side_subset (-f) (-v) eq'.ge hR hL plane' up hjK hjR h₀
  refine ⟨Subset.antisymm ?_ left, Subset.antisymm ?_ (by simpa using right)⟩
  · intro x hx
    have hk := eq.le (Or.inl hx)
    refine ⟨hk, show f x ≤ v from le_of_not_gt fun hgt => ?_⟩
    exact strict_side_disjoint (-f) (-v) eq'.ge hR hL plane' up hjK hjR h₀ hk (neg_lt_neg hgt) hx
  · intro x hx
    have hk := eq.le (Or.inr hx)
    refine ⟨hk, show v ≤ f x from le_of_not_gt fun hlt => ?_⟩
    exact strict_side_disjoint f v eq.ge hL hR plane lo hiK hiL (hi lo hlo) hk hlt hx

/-- The required separator exists for every neighboring pair of a chain
partition, by separation of their full-dimensional open interiors. -/
theorem exists_caps (p : BodyPartition K S) (chain : ChainDisjoint S)
    (i j : Fin n) (hij : j.val = i.val + 1) :
    ∃ (f : Space d →L[ℝ] ℝ) (v : ℝ), f ≠ 0 ∧
      prefixCells S i = K.points ∩ {x | f x ≤ v} ∧
      suffixCells S j = K.points ∩ {x | v ≤ f x} := by
  obtain ⟨f,v,hi,hj⟩ := geometric_hahn_banach_open_open (S i).property.1.interior isOpen_interior
    (S j).property.1.interior isOpen_interior (p.disjoint (show i ≠ j by intro h; subst j; omega))
  refine ⟨f,v,?_,caps_of_separator p chain i j hij f v hi hj⟩
  intro hf
  obtain ⟨x,hx⟩ := (S i).property.2
  obtain ⟨y,hy⟩ := (S j).property.2
  have hl := hi x hx
  have hr := hj y hy
  simp [hf] at hl hr
  linarith

/-- Intersecting the adjacent prefix and suffix cuts reconstructs a single
body, including all its boundary points. -/
theorem cell_eq_caps (chain : ChainDisjoint S) (i : Fin n) :
    (S i).points = prefixCells S i ∩ suffixCells S i := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨mem_iUnion.mpr ⟨⟨i,le_rfl⟩,hx⟩,mem_iUnion.mpr ⟨⟨i,le_rfl⟩,hx⟩⟩
  · rintro x ⟨hl,hr⟩
    obtain ⟨⟨k,hk⟩,hxk⟩ := mem_iUnion.mp hl
    obtain ⟨⟨l,hl⟩,hxl⟩ := mem_iUnion.mp hr
    by_cases hki : k = i
    · subst k; exact hxk
    by_cases hli : l = i
    · subst l; exact hxl
    exact False.elim (disjoint_left.mp (chain k l (by omega)) hxk hxl)

end NRR.CutChart

