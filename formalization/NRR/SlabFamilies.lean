import NRR.CutContinuity
import NRR.ConvexLimits
import NRR.GlobalAssembly

/-! Compact disjoint families of actual affine slabs.  Axis witnesses keep
the different layers distinct even at the extreme ends of the parent. -/

noncomputable section
open Set Topology Metric TopologicalSpace

namespace NRR.InterfaceChart

def cutConvexCompact {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) (r : FeasibleParameters K) :
    ConvexLimits.ConvexCompact (Space d × ℝ) :=
  ⟨cutCompact compact r,convex_clippedSlab convex _ _⟩

theorem continuous_cutConvexCompact {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) :
    Continuous (cutConvexCompact compact convex) :=
  (continuous_cutCompact compact convex).subtype_mk _

theorem compact_admissibleBox_of_axis {d : ℕ} {K : Set (Space d × ℝ)}
    {ε a b c e t : ℝ} (axis : ((0 : Space d),t) ∈ K)
    (lower : b < t) (upper : t < c) :
    IsCompact (admissibleBox K ε a b c e) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have image : Subtype.val '' admissibleBox K ε a b c e =
      parameterBox d ε a b ×ˢ parameterBox d ε c e := by
    ext r
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact hr
    · intro hr
      have feasible : ∃ y ∈ K, height r.1 y.1 < y.2 ∧ y.2 < height r.2 y.1 := by
        refine ⟨(0,t),axis,?_,?_⟩
        · simpa only [height,map_zero,zero_add] using hr.1.2.2.trans_lt lower
        · simpa only [height,map_zero,zero_add] using upper.trans_le hr.2.2.1
      exact ⟨⟨r,feasible⟩,hr,rfl⟩
  rw [image]
  exact (compact_parameterBox d ε a b).prod (compact_parameterBox d ε c e)

/-- Actual single-cell families, rather than parameter sets or their
formal names. The first and last bounding planes may lie outside K. -/
def slabFamily {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) (ε a b c e : ℝ) :
    Set (ConvexLimits.ConvexCompact (Space d × ℝ)) :=
  cutConvexCompact compact convex '' admissibleBox K ε a b c e

theorem compact_slabFamily {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K)
    {ε a b c e t : ℝ} (axis : ((0 : Space d),t) ∈ K)
    (lower : b < t) (upper : t < c) :
    IsCompact (slabFamily compact convex ε a b c e) :=
  (compact_admissibleBox_of_axis axis lower upper).image
    (continuous_cutConvexCompact compact convex)

/-- A fixed point of the vertical axis distinguishes an earlier layer
from every later layer. No uniform positivity of the prescribed density
is involved in this disjointness statement. -/
theorem slabFamily_disjoint {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K)
    {ε a b c e ε' a' b' c' e' t : ℝ}
    (axis : ((0 : Space d),t) ∈ K) (lower : b ≤ t) (upper : t ≤ c)
    (separate : t < a') :
    Disjoint (slabFamily compact convex ε a b c e)
      (slabFamily compact convex ε' a' b' c' e') := by
  apply disjoint_left.mpr
  rintro C ⟨r,hr,he⟩ ⟨s,hs,hsC⟩
  have memR : ((0 : Space d),t) ∈ ConvexLimits.points (cutConvexCompact compact convex r) := by
    refine ⟨axis,?_,?_⟩
    · simpa only [height,map_zero,zero_add] using hr.1.2.2.trans lower
    · simpa only [height,map_zero,zero_add] using upper.trans hr.2.2.1
  have eq : cutConvexCompact compact convex r = cutConvexCompact compact convex s :=
    he.trans hsC.symm
  rw [eq] at memR
  have bad : s.val.1.2 ≤ t := by
    simpa only [height,map_zero,zero_add] using memR.2.1
  linarith [hs.1.2.1]

/-- Consecutive intercept windows produce pairwise disjoint compact
single-cell families, including the two outside cells. -/
theorem compact_disjoint_layerFamilies {d n : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) (ε : ℝ)
    (a b : Fin (n+1) → ℝ) (t : Fin n → ℝ)
    (ordered : Monotone a) (axis : ∀ i, ((0 : Space d),t i) ∈ K)
    (between : ∀ i, b i.castSucc < t i ∧ t i < a i.succ) :
    (∀ i : Fin n, IsCompact
      (slabFamily compact convex ε (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ))) ∧
    Pairwise (fun i j : Fin n => Disjoint
      (slabFamily compact convex ε (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ))
      (slabFamily compact convex ε (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ))) := by
  refine ⟨fun i => compact_slabFamily compact convex (axis i) (between i).1 (between i).2,?_⟩
  intro i j hij
  have forward (i j : Fin n) (h : i < j) : Disjoint
      (slabFamily compact convex ε (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ))
      (slabFamily compact convex ε (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)) := by
    apply slabFamily_disjoint compact convex (axis i) (between i).1.le (between i).2.le
    exact (between i).2.trans_le (ordered (show i.succ ≤ j.castSucc by
      change i.val+1 ≤ j.val
      exact h))
  rcases lt_or_gt_of_ne hij with h | h
  · exact forward i j h
  · exact (forward j i h).symm

/-- Recover both interfaces continuously from a member of an actual
compact convex slab family. -/
def slabInterfaceReadout {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi) :
    C(cutConvexCompact compact convex '' S,Parameters d × Parameters d) := by
  let lift : C(cutConvexCompact compact convex '' S,
      range (fun r : S => cutCompact compact r.val)) :=
    ⟨fun C => ⟨C.val.val,by
      obtain ⟨r,hr,he⟩ := C.property
      exact ⟨⟨r,hr⟩,congrArg Subtype.val he⟩⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  exact (interfaceReadout compact convex hD inner S hS bounds).comp lift

@[simp] theorem slabInterfaceReadout_apply {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi)
    (r : FeasibleParameters K) (hr : r ∈ S) :
    slabInterfaceReadout compact convex hD inner S hS bounds
      ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩ = r.val := by
  change interfaceReadout compact convex hD inner S hS bounds
    ⟨cutCompact compact r,mem_range_self (⟨r,hr⟩ : S)⟩ = r.val
  exact interfaceReadout_apply compact convex hD inner S hS bounds ⟨r,hr⟩

def slabProfileReadout {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi)
    (cap : C(Parameters d,ℂ)) : C(cutConvexCompact compact convex '' S,ℂ × ℂ) :=
  let P := slabInterfaceReadout compact convex hD inner S hS bounds
  ⟨fun C => (cap (P C).1,-cap (P C).2),
    (cap.continuous.comp (continuous_fst.comp P.continuous)).prodMk
      (cap.continuous.comp (continuous_snd.comp P.continuous)).neg⟩

@[simp] theorem slabProfileReadout_apply {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi)
    (cap : C(Parameters d,ℂ)) (r : FeasibleParameters K) (hr : r ∈ S) :
    slabProfileReadout compact convex hD inner S hS bounds cap
      ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩ =
        (cap r.val.1,-cap r.val.2) := by
  change (cap (slabInterfaceReadout compact convex hD inner S hS bounds
    ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩).1,
    -cap (slabInterfaceReadout compact convex hD inner S hS bounds
    ⟨cutConvexCompact compact convex r,mem_image_of_mem _ hr⟩).2) = _
  rw [slabInterfaceReadout_apply compact convex hD inner S hS bounds r hr]

/-- The middle cell is distinguished and the bottom cell is the first
ordinary label. This is the precise labelling needed by the planar model. -/
def specialRelabel (r : ℕ) : Option (Fin (r+1)) ≃ Fin (r+2) :=
  (finSuccEquiv' (1 : Fin (r+2))).symm

@[simp] theorem specialRelabel_none (r : ℕ) : specialRelabel r none = 1 := rfl

@[simp] theorem specialRelabel_some_zero (r : ℕ) : specialRelabel r (some 0) = 0 := by
  exact finSuccEquiv'_symm_some_below (by change (0 : ℕ) < 1; omega)

/-- A finite family of actual convex slabs, with a continuous two-cut
reading on its distinguished member, supplies the global patching chart. -/
def layerChart {d r : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) (ε : ℝ)
    (a b : Fin (r+3) → ℝ) (t : Fin (r+2) → ℝ)
    (ordered : Monotone a) (axis : ∀ i, ((0 : Space d),t i) ∈ K)
    (between : ∀ i, b i.castSucc < t i ∧ t i < a i.succ)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (bounds : ∀ s ∈ admissibleBox K ε (a 1) (b 1) (a 2) (b 2), ∀ u ∈ D,
      lo ≤ height s.val.1 u ∧ height s.val.1 u ≤ height s.val.2 u ∧ height s.val.2 u ≤ hi)
    (cap : C(Parameters d,ℂ)) :
    GlobalAssembly.TwoInterfaceChart (r+1) (ConvexLimits.ConvexCompact (Space d × ℝ)) := by
  have data := compact_disjoint_layerFamilies compact convex ε a b t ordered axis between
  refine ⟨(fun i => slabFamily compact convex ε
      (a (specialRelabel r i).castSucc) (b (specialRelabel r i).castSucc)
      (a (specialRelabel r i).succ) (b (specialRelabel r i).succ)),
    (fun i => data.1 (specialRelabel r i)),
    (fun _ _ hij => data.2 ((specialRelabel r).injective.ne hij)),?_⟩
  have hS : IsCompact (admissibleBox K ε (a 1) (b 1) (a 2) (b 2)) := by
    exact compact_admissibleBox_of_axis (axis 1) (between 1).1 (between 1).2
  exact slabProfileReadout compact convex hD inner _ hS bounds cap

end NRR.InterfaceChart
