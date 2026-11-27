import NRR.CutChart
import Mathlib.Topology.MetricSpace.Thickening

/-! Openness and uniqueness facts for the affine interface chart. -/

noncomputable section
open Set Topology Metric TopologicalSpace Filter
set_option maxHeartbeats 800000

namespace NRR.InterfaceChart

/-- Disjoint compact sets remain disjoint under sufficiently small
Hausdorff perturbations of both sets. -/
theorem disjoint_of_near {X : Type*} [MetricSpace X]
    (A B : NonemptyCompacts X) (h : Disjoint (A : Set X) B) :
    ∃ ε > (0 : ℝ), ∀ A' B' : NonemptyCompacts X,
      dist A' A < ε → dist B' B < ε → Disjoint (A' : Set X) B' := by
  obtain ⟨ε,hε,hsep⟩ := h.exists_thickenings A.isCompact B.isCompact.isClosed
  refine ⟨ε,hε,fun A' B' hA hB => hsep.mono ?_ ?_⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hA (edist_ne_top A' A)
    exact mem_thickening_iff.mpr ⟨y,hy,hxy⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hB (edist_ne_top B' B)
    exact mem_thickening_iff.mpr ⟨y,hy,hxy⟩

theorem isOpen_disjoint {X : Type*} [MetricSpace X] :
    IsOpen {p : NonemptyCompacts X × NonemptyCompacts X | Disjoint (p.1 : Set X) p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨A,B⟩ h
  obtain ⟨ε,hε,near⟩ := disjoint_of_near A B h
  let U := {p : NonemptyCompacts X × NonemptyCompacts X |
    dist p.1 A < ε ∧ dist p.2 B < ε}
  have openU : IsOpen U :=
    (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
      (isOpen_lt (continuous_snd.dist continuous_const) continuous_const)
  exact mem_nhds_iff.mpr ⟨U,fun p hp => near p.1 p.2 hp.1 hp.2,openU,by simp [U,hε]⟩

/-- The condition that all nonadjacent cells of an ordered partition are
disjoint is an open condition on the ordered tuple of convex bodies. -/
theorem isOpen_chainDisjoint (d n : ℕ) :
    IsOpen {S : Fin n → Body d | CutChart.ChainDisjoint S} := by
  simp only [CutChart.ChainDisjoint, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i.val+1 < j.val
  · simp only [hij, iInter_true]
    have ci : Continuous (fun S : Fin n → Body d => (S i).val) :=
      continuous_subtype_val.comp (continuous_apply i)
    have cj : Continuous (fun S : Fin n → Body d => (S j).val) :=
      continuous_subtype_val.comp (continuous_apply j)
    exact (isOpen_disjoint (X := Space d)).preimage (ci.prodMk cj)
  · simp [hij]

/-- An affine height graph is encoded by its slope functional and intercept. -/
abbrev Parameters (d : ℕ) := (Space d →L[ℝ] ℝ) × ℝ

def height {d : ℕ} (p : Parameters d) (u : Space d) : ℝ := p.1 u + p.2

theorem parameters_eq_of_height_eq {d : ℕ} {D : Set (Space d)}
    (hD : (0 : Space d) ∈ interior D) {p q : Parameters d}
    (eq : ∀ u ∈ D, height p u = height q u) : p = q := by
  have intercept : p.2 = q.2 := by
    simpa [height] using eq 0 (interior_subset hD)
  let L : Space d →ₗ[ℝ] ℝ := p.1.toLinearMap - q.1.toLinearMap
  have sub : D ⊆ (LinearMap.ker L : Set (Space d)) := by
    intro u hu
    change p.1 u - q.1 u = 0
    have := eq u hu
    dsimp [height] at this
    linarith
  have all : LinearMap.ker L = ⊤ :=
    (LinearMap.ker L).eq_top_of_nonempty_interior' ⟨0,interior_mono sub hD⟩
  have slope : p.1 = q.1 := by
    ext u
    have hu : u ∈ LinearMap.ker L := by rw [all]; trivial
    change p.1 u - q.1 u = 0 at hu
    exact sub_eq_zero.mp hu
  exact Prod.ext slope intercept

/-- A body cut between two affine graphs. -/
def clippedSlab {d : ℕ} (K : Set (Space d × ℝ)) (p q : Parameters d) :
    Set (Space d × ℝ) :=
  {x | x ∈ K ∧ height p x.1 ≤ x.2 ∧ x.2 ≤ height q x.1}

/-- Both active interfaces are uniquely recoverable from a single clipped
slab if an inner cylinder contains their graphs over an open base. -/
theorem parameters_eq_of_clippedSlab_eq {d : ℕ}
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
    {K : Set (Space d × ℝ)} {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K) {p q p' q' : Parameters d}
    (bounds : ∀ u ∈ D, lo ≤ height p u ∧ height p u ≤ height q u ∧ height q u ≤ hi)
    (bounds' : ∀ u ∈ D, lo ≤ height p' u ∧ height p' u ≤ height q' u ∧ height q' u ≤ hi)
    (eq : clippedSlab K p q = clippedSlab K p' q') : p = p' ∧ q = q' := by
  have lower (u : Space d) (hu : u ∈ D) : height p u = height p' u := by
    obtain ⟨hl,ho,hh⟩ := bounds u hu
    obtain ⟨hl',ho',hh'⟩ := bounds' u hu
    have hp : (u,height p u) ∈ clippedSlab K p q :=
      ⟨inner ⟨hu,⟨hl,ho.trans hh⟩⟩,le_rfl,ho⟩
    have hp' : (u,height p' u) ∈ clippedSlab K p' q' :=
      ⟨inner ⟨hu,⟨hl',ho'.trans hh'⟩⟩,le_rfl,ho'⟩
    rw [eq] at hp
    rw [← eq] at hp'
    exact le_antisymm hp'.2.1 hp.2.1
  have upper (u : Space d) (hu : u ∈ D) : height q u = height q' u := by
    obtain ⟨hl,ho,hh⟩ := bounds u hu
    obtain ⟨hl',ho',hh'⟩ := bounds' u hu
    have hq : (u,height q u) ∈ clippedSlab K p q :=
      ⟨inner ⟨hu,⟨hl.trans ho,hh⟩⟩,ho,le_rfl⟩
    have hq' : (u,height q' u) ∈ clippedSlab K p' q' :=
      ⟨inner ⟨hu,⟨hl'.trans ho',hh'⟩⟩,ho',le_rfl⟩
    rw [eq] at hq
    rw [← eq] at hq'
    exact le_antisymm hq.2.2 hq'.2.2
  exact ⟨parameters_eq_of_height_eq hD lower,parameters_eq_of_height_eq hD upper⟩

/-- Hausdorff limits can be tested by approximating any point of the limit
with a convergent sequence of points in the approximating compact sets. -/
theorem approximate_point_of_tendsto {X : Type*} [MetricSpace X]
    {A : ℕ → NonemptyCompacts X} {B : NonemptyCompacts X}
    (h : Tendsto A atTop (𝓝 B)) {x : X} (hx : x ∈ B) :
    ∃ u : ℕ → X, (∀ n, u n ∈ A n) ∧ Tendsto u atTop (𝓝 x) := by
  choose u hu hdist using fun n => (A n).isCompact.exists_infDist_eq_dist (A n).nonempty x
  refine ⟨u,hu,tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have ht := (lipschitz_infDist_set x).continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,infDist_zero_of_mem hx,hdist,dist_comm x] using ht

/-- Weak separation inequalities pass to a Hausdorff limit even when both
the normal functional and the offset vary. -/
theorem separator_le_of_tendsto {d : ℕ}
    {A : ℕ → NonemptyCompacts (Space d × ℝ)} {B : NonemptyCompacts (Space d × ℝ)}
    (hA : Tendsto A atTop (𝓝 B))
    {F : ℕ → (Space d × ℝ) →L[ℝ] ℝ} {G : (Space d × ℝ) →L[ℝ] ℝ}
    (hF : Tendsto F atTop (𝓝 G)) {c : ℕ → ℝ} {b : ℝ}
    (hc : Tendsto c atTop (𝓝 b)) (sep : ∀ n x, x ∈ A n → F n x ≤ c n) :
    ∀ x ∈ B, G x ≤ b := by
  intro x hx
  obtain ⟨u,hu,hux⟩ := approximate_point_of_tendsto hA hx
  have ev : Continuous (fun p : ((Space d × ℝ) →L[ℝ] ℝ) × (Space d × ℝ) => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have near : Tendsto (fun n => F n (u n)) atTop (𝓝 (G x)) :=
    ev.continuousAt.tendsto.comp (hF.prodMk_nhds hux)
  exact le_of_tendsto_of_tendsto near hc (Eventually.of_forall fun n => sep n (u n) (hu n))

/-- A weakly oriented affine separator of an ordered pair of compact sets. -/
def Separates {d : ℕ} (A B : NonemptyCompacts (Space d × ℝ))
    (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ) : Prop :=
  (∀ x ∈ A, F x ≤ c) ∧ ∀ x ∈ B, c ≤ F x

theorem isClosed_separators (d : ℕ) :
    IsClosed {r : (NonemptyCompacts (Space d × ℝ) × NonemptyCompacts (Space d × ℝ)) ×
      (((Space d × ℝ) →L[ℝ] ℝ) × ℝ) | Separates r.1.1 r.1.2 r.2.1 r.2.2} := by
  apply isSeqClosed_iff_isClosed.mp
  intro r s hsep near
  have hA : Tendsto (fun n => (r n).1.1) atTop (𝓝 s.1.1) :=
    ((continuous_fst.comp continuous_fst).tendsto s).comp near
  have hB : Tendsto (fun n => (r n).1.2) atTop (𝓝 s.1.2) :=
    ((continuous_snd.comp continuous_fst).tendsto s).comp near
  have hF : Tendsto (fun n => (r n).2.1) atTop (𝓝 s.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto s).comp near
  have hc : Tendsto (fun n => (r n).2.2) atTop (𝓝 s.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto s).comp near
  refine ⟨separator_le_of_tendsto hA hF hc (fun n => (hsep n).1),?_⟩
  intro x hx
  have h := separator_le_of_tendsto hB hF.neg hc.neg
    (fun n y hy => neg_le_neg ((hsep n).2 y hy)) x hx
  exact neg_le_neg_iff.mp h

/-- Any nonzero weak separator containing an open horizontal face is a
positive vertical functional, as soon as its lower side contains one point
strictly below the face. This identifies limits of normalized separators. -/
theorem separator_eq_vertical {d : ℕ} {D : Set (Space d)}
    (hD : (0 : Space d) ∈ interior D) (F : (Space d × ℝ) →L[ℝ] ℝ)
    (hne : F ≠ 0) {a t c : ℝ} (hat : a < t)
    (lower : F (0,a) ≤ c) (face : ∀ u ∈ D, F (u,t) = c) :
    0 < F (0,1) ∧ c = t * F (0,1) ∧ ∀ x, F x = x.2 * F (0,1) := by
  let k := F (0,1)
  have eval (u : Space d) (s : ℝ) : F (u,s) = F (u,0) + s*k := by
    have he : (u,s) = (u,0) + s • ((0,1) : Space d × ℝ) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  have center : t*k = c := by
    have h := face 0 (interior_subset hD)
    rw [eval] at h
    simpa only [show F ((0 : Space d),0) = 0 from F.map_zero,zero_add] using h
  let L : Space d →ₗ[ℝ] ℝ := F.toLinearMap.comp (LinearMap.inl ℝ (Space d) ℝ)
  have sub : D ⊆ (LinearMap.ker L : Set (Space d)) := by
    intro u hu
    change F (u,0) = 0
    have h := face u hu
    rw [eval] at h
    linarith
  have all : LinearMap.ker L = ⊤ :=
    (LinearMap.ker L).eq_top_of_nonempty_interior' ⟨0,interior_mono sub hD⟩
  have horizontal (u : Space d) : F (u,0) = 0 := by
    change u ∈ LinearMap.ker L
    rw [all]
    trivial
  have vertical (x : Space d × ℝ) : F x = x.2*k := by
    rcases x with ⟨u,s⟩
    rw [eval,horizontal,zero_add]
  have hk : k ≠ 0 := by
    intro he
    apply hne
    apply ContinuousLinearMap.ext
    intro x
    simpa only [he,mul_zero,ContinuousLinearMap.zero_apply] using vertical x
  have hk0 : 0 ≤ k := by
    rw [eval,horizontal,zero_add,← center] at lower
    nlinarith
  exact ⟨lt_of_le_of_ne hk0 (Ne.symm hk),center.symm,vertical⟩

/-- Convert a separator whose vertical coefficient is positive into the
unique height graph with the same lower halfspace. -/
def graphParameters {d : ℕ} (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ) : Parameters d :=
  (-(F (0,1))⁻¹ • F.comp (ContinuousLinearMap.inl ℝ (Space d) ℝ), c / F (0,1))

theorem height_graphParameters {d : ℕ} (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ) (u : Space d) :
    height (graphParameters F c) u = (c-F (u,0)) / F (0,1) := by
  simp only [height,graphParameters,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,smul_eq_mul]
  ring

theorem le_separator_iff_graph {d : ℕ} (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hF : 0 < F (0,1)) (x : Space d × ℝ) :
    F x ≤ c ↔ x.2 ≤ height (graphParameters F c) x.1 := by
  rcases x with ⟨u,s⟩
  have he : F (u,s) = F (u,0) + s*F (0,1) := by
    have he : (u,s) = (u,0) + s • ((0,1) : Space d × ℝ) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  rw [height_graphParameters,le_div_iff₀ hF,he]
  constructor <;> intro h <;> linarith

theorem ge_separator_iff_graph {d : ℕ} (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hF : 0 < F (0,1)) (x : Space d × ℝ) :
    c ≤ F x ↔ height (graphParameters F c) x.1 ≤ x.2 := by
  rcases x with ⟨u,s⟩
  have he : F (u,s) = F (u,0) + s*F (0,1) := by
    have he : (u,s) = (u,0) + s • ((0,1) : Space d × ℝ) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  rw [height_graphParameters,div_le_iff₀ hF,he]
  constructor <;> intro h <;> linarith

/-- A finite convex partition expressed directly in product coordinates. -/
structure ConvexPartition {d n : ℕ} (K : Set (Space d × ℝ))
    (S : Fin n → NonemptyCompacts (Space d × ℝ)) : Prop where
  parentConvex : Convex ℝ K
  cellConvex : ∀ i, Convex ℝ (S i : Set (Space d × ℝ))
  cellInterior : ∀ i, (interior (S i : Set (Space d × ℝ))).Nonempty
  covers : (⋃ i, (S i : Set (Space d × ℝ))) = K
  disjoint : Pairwise fun i j =>
    Disjoint (interior (S i : Set (Space d × ℝ))) (interior (S j : Set (Space d × ℝ)))

/-- The geometric data of an ordered convex chain partition in product
coordinates. Equal-mass partitions supply these data without any change. -/
structure ChainPartition {d n : ℕ} (K : Set (Space d × ℝ))
    (S : Fin n → NonemptyCompacts (Space d × ℝ)) : Prop extends ConvexPartition K S where
  nonadjacent : ∀ i j, i.val+1 < j.val → Disjoint (S i : Set (Space d × ℝ)) (S j)

theorem isOpen_productChainDisjoint (d n : ℕ) :
    IsOpen {S : Fin n → NonemptyCompacts (Space d × ℝ) |
      ∀ i j, i.val+1 < j.val → Disjoint (S i : Set (Space d × ℝ)) (S j)} := by
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i.val+1 < j.val
  · simp only [hij,iInter_true]
    have ci : Continuous (fun S : Fin n → NonemptyCompacts (Space d × ℝ) => S i) := continuous_apply i
    have cj : Continuous (fun S : Fin n → NonemptyCompacts (Space d × ℝ) => S j) := continuous_apply j
    exact (isOpen_disjoint (X := Space d × ℝ)).preimage (ci.prodMk cj)
  · simp [hij]

def prefixCells {d n : ℕ} (S : Fin n → NonemptyCompacts (Space d × ℝ)) (k : Fin n) :
    Set (Space d × ℝ) := ⋃ j : {j : Fin n // j ≤ k}, (S j.val : Set (Space d × ℝ))

def suffixCells {d n : ℕ} (S : Fin n → NonemptyCompacts (Space d × ℝ)) (k : Fin n) :
    Set (Space d × ℝ) := ⋃ j : {j : Fin n // k ≤ j}, (S j.val : Set (Space d × ℝ))

namespace ChainPartition
variable {d n : ℕ} {K : Set (Space d × ℝ)}
  {S : Fin n → NonemptyCompacts (Space d × ℝ)} (p : ChainPartition K S)
include p

theorem cell_subset (i : Fin n) : (S i : Set (Space d × ℝ)) ⊆ K := by
  rw [← p.covers]
  exact subset_iUnion (fun j : Fin n => (S j : Set (Space d × ℝ))) i

theorem closure_cell_interior (i : Fin n) :
    closure (interior (S i : Set (Space d × ℝ))) = (S i : Set (Space d × ℝ)) :=
  ((p.cellConvex i).closure_interior_eq_closure_of_nonempty_interior (p.cellInterior i)).trans
    (S i).isCompact.isClosed.closure_eq

private theorem strict_side_disjoint {L R : Set (Space d × ℝ)} (f : (Space d × ℝ) →L[ℝ] ℝ)
    (u : ℝ) (cover : K ⊆ L ∪ R) (hL : IsClosed L) (hR : IsClosed R)
    (plane : ∀ x ∈ L ∩ R, f x = u) (x₀ : Space d × ℝ) (hK₀ : x₀ ∈ K)
    (hL₀ : x₀ ∈ L) (h₀ : f x₀ < u) {x : Space d × ℝ} (hx : x ∈ K) (h : f x < u) :
    x ∉ R := by
  intro hr
  let A := K ∩ {z | f z < u}
  have conn : IsPreconnected A :=
    (p.parentConvex.inter (convex_halfSpace_lt f.toLinearMap.isLinear _)).isPreconnected
  obtain ⟨y,hy,hp⟩ := isPreconnected_closed_iff.mp conn L R hL hR
    (inter_subset_left.trans cover) ⟨x₀,⟨hK₀,h₀⟩,hL₀⟩ ⟨x,⟨hx,h⟩,hr⟩
  exact (ne_of_lt hy.2) (plane y hp)

private theorem closed_side_subset {L R : Set (Space d × ℝ)}
    (f : (Space d × ℝ) →L[ℝ] ℝ) (u : ℝ)
    (cover : K ⊆ L ∪ R) (hL : IsClosed L) (hR : IsClosed R)
    (plane : ∀ x ∈ L ∩ R, f x = u) (x₀ : Space d × ℝ) (hK₀ : x₀ ∈ K)
    (hL₀ : x₀ ∈ L) (h₀ : f x₀ < u) : K ∩ {z | f z ≤ u} ⊆ L := by
  rintro x ⟨hx,hle⟩
  have seg : openSegment ℝ x₀ x ⊆ L := by
    rintro _ ⟨a,b,ha,hb,hab,rfl⟩
    have hk := p.parentConvex hK₀ hx ha.le hb.le hab
    have hlt : f (a • x₀ + b • x) < u := by
      simp only [map_add,map_smul,smul_eq_mul]
      calc
        a*f x₀ + b*f x < a*u+b*u :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h₀ ha)
            (mul_le_mul_of_nonneg_left hle hb.le)
        _ = u := by rw [← add_mul,hab,one_mul]
    exact (cover hk).resolve_right (p.strict_side_disjoint f u cover hL hR plane x₀ hK₀ hL₀ h₀ hk hlt)
  exact hL.closure_subset (closure_mono seg (segment_subset_closure_openSegment (right_mem_segment ..)))

theorem prefix_suffix_cover (i j : Fin n) (hij : j.val = i.val+1) :
    prefixCells S i ∪ suffixCells S j = K := by
  apply Subset.antisymm
  · exact union_subset (iUnion_subset fun k => p.cell_subset k.val)
      (iUnion_subset fun k => p.cell_subset k.val)
  · intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (p.covers.symm ▸ hx)
    by_cases hki : k ≤ i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k,hki⟩,hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,by omega⟩,hk⟩)

theorem prefix_suffix_overlap (i j : Fin n) (hij : j.val = i.val+1) :
    prefixCells S i ∩ suffixCells S j = (S i : Set (Space d × ℝ)) ∩ S j := by
  apply Subset.antisymm
  · rintro x ⟨hl,hr⟩
    obtain ⟨⟨k,hk⟩,hxk⟩ := mem_iUnion.mp hl
    obtain ⟨⟨l,hl⟩,hxl⟩ := mem_iUnion.mp hr
    change x ∈ S k at hxk
    change x ∈ S l at hxl
    have hn : ¬ k.val+1 < l.val := fun he => disjoint_left.mp (p.nonadjacent k l he) hxk hxl
    obtain rfl : k = i := Fin.ext (by omega)
    obtain rfl : l = j := Fin.ext (by omega)
    exact ⟨hxk,hxl⟩
  · rintro x ⟨hi,hj⟩
    exact ⟨mem_iUnion.mpr ⟨⟨i,le_rfl⟩,hi⟩,mem_iUnion.mpr ⟨⟨j,le_rfl⟩,hj⟩⟩

theorem caps_of_separator (i j : Fin n) (hij : j.val = i.val+1)
    (f : (Space d × ℝ) →L[ℝ] ℝ) (v : ℝ)
    (hi : ∀ x ∈ interior (S i : Set (Space d × ℝ)), f x < v)
    (hj : ∀ x ∈ interior (S j : Set (Space d × ℝ)), v < f x) :
    prefixCells S i = K ∩ {x | f x ≤ v} ∧ suffixCells S j = K ∩ {x | v ≤ f x} := by
  let L := prefixCells S i
  let R := suffixCells S j
  have hL : IsClosed L := isClosed_iUnion_of_finite fun k => (S k.val).isCompact.isClosed
  have hR : IsClosed R := isClosed_iUnion_of_finite fun k => (S k.val).isCompact.isClosed
  have eq : L ∪ R = K := p.prefix_suffix_cover i j hij
  have leq : (S i : Set (Space d × ℝ)) ⊆ {x | f x ≤ v} := by
    rw [← p.closure_cell_interior i]
    exact closure_minimal (fun x hx => (hi x hx).le) (isClosed_le f.continuous continuous_const)
  have geq : (S j : Set (Space d × ℝ)) ⊆ {x | v ≤ f x} := by
    rw [← p.closure_cell_interior j]
    exact closure_minimal (fun x hx => (hj x hx).le) (isClosed_le continuous_const f.continuous)
  have plane (x : Space d × ℝ) (hx : x ∈ L ∩ R) : f x = v := by
    rw [show L ∩ R = _ from p.prefix_suffix_overlap i j hij] at hx
    exact le_antisymm (leq hx.1) (geq hx.2)
  obtain ⟨lo,hlo⟩ := p.cellInterior i
  obtain ⟨up,hup⟩ := p.cellInterior j
  have hiL : lo ∈ L := mem_iUnion.mpr ⟨⟨i,le_rfl⟩,interior_subset hlo⟩
  have hjR : up ∈ R := mem_iUnion.mpr ⟨⟨j,le_rfl⟩,interior_subset hup⟩
  have hiK := p.cell_subset i (interior_subset hlo)
  have hjK := p.cell_subset j (interior_subset hup)
  have eq' : R ∪ L = K := (union_comm ..).trans eq
  have plane' (x : Space d × ℝ) (hx : x ∈ R ∩ L) : (-f) x = -v := by
    simp [plane x ⟨hx.2,hx.1⟩]
  have h₀ : (-f) up < -v := neg_lt_neg (hj up hup)
  have left := p.closed_side_subset f v eq.ge hL hR plane lo hiK hiL (hi lo hlo)
  have right := p.closed_side_subset (-f) (-v) eq'.ge hR hL plane' up hjK hjR h₀
  refine ⟨Subset.antisymm ?_ left,Subset.antisymm ?_ (by simpa using right)⟩
  · intro x hx
    have hk := eq.le (Or.inl hx)
    refine ⟨hk,show f x ≤ v from le_of_not_gt fun hgt => ?_⟩
    exact p.strict_side_disjoint (-f) (-v) eq'.ge hR hL plane' up hjK hjR h₀ hk (neg_lt_neg hgt) hx
  · intro x hx
    have hk := eq.le (Or.inr hx)
    refine ⟨hk,show v ≤ f x from le_of_not_gt fun hlt => ?_⟩
    exact p.strict_side_disjoint f v eq.ge hL hR plane lo hiK hiL (hi lo hlo) hk hlt hx

/-- A chain partition has genuine affine prefix and suffix caps at every
adjacent pair. No parameterization or separator is assumed. -/
theorem exists_caps (i j : Fin n) (hij : j.val = i.val+1) :
    ∃ (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ), F ≠ 0 ∧ Separates (S i) (S j) F c ∧
      prefixCells S i = K ∩ {x | F x ≤ c} ∧ suffixCells S j = K ∩ {x | c ≤ F x} := by
  obtain ⟨F,c,hi,hj⟩ := geometric_hahn_banach_open_open (p.cellConvex i).interior isOpen_interior
    (p.cellConvex j).interior isOpen_interior (p.disjoint (show i ≠ j by intro h; subst j; omega))
  have hne : F ≠ 0 := by
    intro he
    obtain ⟨x,hx⟩ := p.cellInterior i
    obtain ⟨y,hy⟩ := p.cellInterior j
    have hl := hi x hx
    have hr := hj y hy
    simp [he] at hl hr
    linarith
  have cap := p.caps_of_separator i j hij F c hi hj
  have sep : Separates (S i) (S j) F c := by
    constructor
    · intro x hx
      have hp : x ∈ prefixCells S i := mem_iUnion.mpr ⟨⟨i,le_rfl⟩,hx⟩
      exact (cap.1 ▸ hp).2
    · intro x hx
      have hp : x ∈ suffixCells S j := mem_iUnion.mpr ⟨⟨j,le_rfl⟩,hx⟩
      exact (cap.2 ▸ hp).2
  exact ⟨F,c,hne,sep,cap⟩

theorem cell_eq_caps (i : Fin n) :
    (S i : Set (Space d × ℝ)) = prefixCells S i ∩ suffixCells S i := by
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
    exact False.elim (disjoint_left.mp (p.nonadjacent k l (by omega)) hxk hxl)

end ChainPartition

end NRR.InterfaceChart
