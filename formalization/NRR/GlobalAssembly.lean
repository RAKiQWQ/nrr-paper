import NRR.PlanarScaling
import NRR.Stability
import NRR.Descent

/-! Bounded single-block patching and global exclusion from local cut charts. -/

open Set Topology Finset MeasureTheory
noncomputable section
set_option maxHeartbeats 600000

namespace NRR.GlobalAssembly

open LocalModel RootSums

def familyInclusion {ι B : Type*} [TopologicalSpace B] (A : ι → Set B) :
    C((Σ i,A i),B) :=
  ⟨fun p => p.2.val,continuous_sigma (fun _ => continuous_subtype_val)⟩

def familyFunction {ι B : Type*} [TopologicalSpace B] (A : ι → Set B)
    (f : ∀ i,C(A i,ℂ)) : C((Σ i,A i),ℂ) :=
  ⟨fun p => f p.1 p.2,continuous_sigma (fun i => (f i).continuous)⟩

theorem familyFunction_factors {ι B : Type*} [TopologicalSpace B]
    (A : ι → Set B) (disjoint : Pairwise fun i j => Disjoint (A i) (A j))
    (f : ∀ i,C(A i,ℂ)) :
    Function.FactorsThrough (familyFunction A f) (familyInclusion A) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  simp only [familyInclusion,ContinuousMap.coe_mk] at he
  have hij : i = j := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint hne) x.property (he.symm ▸ y.property)
  subst j
  have hxy : x = y := Subtype.ext he
  subst y
  rfl

/-- Finitely many disjoint compact block families permit independent bounded
continuous prescriptions, with the same uniform bound after extension to the
entire block space. -/
theorem extend_disjoint_compacts {ι B : Type*} [Fintype ι]
    [TopologicalSpace B] [T2Space B] [NormalSpace B]
    (A : ι → Set B) (compact : ∀ i, IsCompact (A i))
    (disjoint : Pairwise fun i j => Disjoint (A i) (A j))
    (f : ∀ i, C(A i,ℂ)) {M : ℝ} (hM : 0 < M)
    (bound : ∀ i x, ‖f i x‖ ≤ M) :
    ∃ F : C(B,ℂ), (∀ b, ‖F b‖ ≤ M) ∧ ∀ (i : ι) (x : A i), F x = f i x := by
  classical
  letI (i : ι) : CompactSpace (A i) := (isCompact_iff_compactSpace).mp (compact i)
  let e := familyInclusion A
  let δ := familyFunction A f
  have consistent : Function.FactorsThrough δ e := familyFunction_factors A disjoint f
  have bounded : ∀ p,‖δ p‖ ≤ M := by
    intro p
    simp only [δ,familyFunction,ContinuousMap.coe_mk]
    exact bound p.1 p.2
  have closed : IsClosedMap e := e.continuous.isClosedMap
  obtain ⟨F,hF,hfix⟩ := Descent.extendCorrection (S := Σ i,A i) (X := B) e closed δ
    consistent hM bounded
  exact ⟨F,hF,fun i x => hfix ⟨i,x⟩⟩

/-- Single-block chart data.  The distinguished family stores the two
neighboring interface readings; every family is a compact subset of the same
ambient Hausdorff block space. -/
structure TwoInterfaceChart (m : ℕ) (B : Type*) [TopologicalSpace B] where
  family : Option (Fin m) → Set B
  compact : ∀ i, IsCompact (family i)
  disjoint : Pairwise fun i j => Disjoint (family i) (family j)
  reading : C(family none, ℂ × ℂ)

namespace TwoInterfaceChart

variable {m : ℕ} [NeZero m] {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]

/-- A configuration belongs to the chart if its blocks admit the required
labelling and the distinguished block alone recovers the two interface data. -/
def Models (A : TwoInterfaceChart m B) (cell : Fin (m+1) → C(X,B))
    (w : C(B,ℂ)) (x : X) : Prop :=
  ∃ (e : Option (Fin m) ≃ Fin (m+1))
    (mem : ∀ i, cell (e i) x ∈ A.family i),
      A.reading ⟨cell (e none) x,mem none⟩ =
        (w (cell (e (some 0)) x),
          (∑ i, w (cell (e (some i)) x)) - w (cell (e (some 0)) x))

def patch (A : TwoInterfaceChart m B) (σ : ℝ) (D : C(ℂ × ℂ,ℂ)) :
    ∀ i, C(A.family i,ℂ)
  | none => (scaledCorrection σ D).comp A.reading
  | some i => ContinuousMap.const _ (-((σ:ℂ)^2 * shift i))

def bound (M : ℝ) : ℝ := M + ∑ i : Fin m, ‖shift i‖

omit [NeZero m] in
theorem bound_pos {M : ℝ} (hM : 0 < M) : 0 < bound (m := m) M := by
  exact add_pos_of_pos_of_nonneg hM (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

omit [NeZero m] in
theorem patch_bound (A : TwoInterfaceChart m B) (σ : ℝ) (D : C(ℂ × ℂ,ℂ))
    {M : ℝ} (hD : ∀ y, ‖D y‖ ≤ M) (i : Option (Fin m)) (x : A.family i) :
    ‖A.patch σ D i x‖ ≤ σ^2 * bound (m := m) M := by
  cases i with
  | none =>
    exact (scaledCorrection_bound σ D hD _).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))) (sq_nonneg σ))
  | some i =>
    change ‖-((σ:ℂ)^2 * shift i)‖ ≤ σ^2 * bound (m := m) M
    rw [norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
    have hs : ‖shift i‖ ≤ ∑ j : Fin m, ‖shift j‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have hm : 0 ≤ M := (norm_nonneg (D (0,0))).trans (hD (0,0))
    exact hs.trans (le_add_of_nonneg_left hm)

omit [NeZero m] in
theorem exists_global_patch [T2Space B] [NormalSpace B]
    (A : TwoInterfaceChart m B) {σ : ℝ} (hσ : 0 < σ) (D : C(ℂ × ℂ,ℂ))
    {M : ℝ} (hM : 0 < M) (hD : ∀ y, ‖D y‖ ≤ M) :
    ∃ E : C(B,ℂ), (∀ b, ‖E b‖ ≤ σ^2 * bound (m := m) M) ∧
      ∀ (i : Option (Fin m)) (x : A.family i), E x = A.patch σ D i x := by
  apply extend_disjoint_compacts A.family A.compact A.disjoint (A.patch σ D)
    (mul_pos (sq_pos_of_pos hσ) (bound_pos hM))
  exact A.patch_bound σ D hD

/-- On every configuration described by the chart, the extended single-block
patch retains the exact planar exclusion.  The local labelling need not be
continuous or globally fixed. -/
theorem rejects_model (A : TwoInterfaceChart m B) (cell : Fin (m+1) → C(X,B))
    (w : C(B,ℂ)) (h : ℂ ≃ₜ ℂ)
    (hh : ∀ t : ℝ, 0 < t → ∀ z, h ((t:ℂ)*z) = (t:ℂ)*h z)
    (D : C(ℂ × ℂ,ℂ))
    (avoid : ∀ (z : Fin m → ℂ) (z₂ q : ℂ), (∑ i,z i)+z₂ = 0 →
      (∀ i,squareTest h (z i)-shift i = q) →
      squareTest h z₂+D (z 0,(∑ i,z i)-z 0) ≠ q)
    {σ : ℝ} (hσ : 0 < σ) (E : C(B,ℂ))
    (fix : ∀ (i : Option (Fin m)) (y : A.family i), E y = A.patch σ D i y) (x : X)
    (balanced : ∑ i,w (cell i x) = 0) (model : A.Models cell w x) :
    ∃ i j, squareTest h (w (cell i x))+E (cell i x) ≠
      squareTest h (w (cell j x))+E (cell j x) := by
  classical
  obtain ⟨e,mem,read⟩ := model
  let z (i : Fin m) := w (cell (e (some i)) x)
  let z₂ := w (cell (e none) x)
  have hz : (∑ i,z i)+z₂ = 0 := by
    have he := e.sum_comp (fun i => w (cell i x))
    rw [balanced,Fintype.sum_option] at he
    simpa [z,z₂,add_comm] using he
  have e_other (i : Fin m) : E (cell (e (some i)) x) = -((σ:ℂ)^2 * shift i) :=
    fix (some i) ⟨cell (e (some i)) x,mem (some i)⟩
  have e_special : E (cell (e none) x) = scaledCorrection σ D (z 0,(∑ i,z i)-z 0) := by
    have he := fix none ⟨cell (e none) x,mem none⟩
    change E (cell (e none) x) = scaledCorrection σ D (A.reading _) at he
    rw [read] at he
    exact he
  by_contra! fair
  let q := squareTest h z₂+scaledCorrection σ D (z 0,(∑ i,z i)-z 0)
  have hf (i : Fin m) : squareTest h (z i)-(σ:ℂ)^2*shift i = q := by
    have he := fair (e (some i)) (e none)
    rw [e_other i,e_special] at he
    exact he
  exact (scaled_planar_avoid h hh D avoid hσ z z₂ q hz hf) rfl

end TwoInterfaceChart

/-- A quadratic perturbation bound can be made smaller than any prescribed
positive uniform stability radius. -/
theorem exists_small_quadratic {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ σ^2*M ≤ ε := by
  let σ := min 1 (ε/(M+1))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hscale : σ*(M+1) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < M+1)).mp (min_le_right _ _)
  have hsquare : σ^2 ≤ σ := by nlinarith [mul_nonneg hσ.le (sub_nonneg.mpr hσ1)]
  refine ⟨σ,hσ,?_⟩
  calc
    σ^2*M ≤ σ*M := mul_le_mul_of_nonneg_right hsquare hM.le
    _ ≤ σ*(M+1) := by nlinarith
    _ ≤ ε := hscale

def perturbFirst {B V : Type*} [TopologicalSpace B] [TopologicalSpace V]
    (f : C(B,ℂ × V)) (E : C(B,ℂ)) : C(B,ℂ × V) :=
  ⟨fun b => ((f b).1+E b,(f b).2), by fun_prop⟩

theorem perturbFirst_dist {B V : Type*} [TopologicalSpace B] [MetricSpace V]
    (f : C(B,ℂ × V)) (E : C(B,ℂ)) (b : B) :
    dist (f b) (perturbFirst f E b) = ‖E b‖ := by
  change max (dist (f b).1 ((f b).1+E b)) (dist (f b).2 (f b).2) = _
  rw [dist_self,dist_eq_norm,show (f b).1-((f b).1+E b) = -E b by abel,norm_neg]
  exact max_eq_left (norm_nonneg _)

/-- A bounded planar correction on separated compact block families extends
to one global characteristic.  Local exclusion handles the chart and the
compact-complement stability margin handles every remaining configuration. -/
theorem exists_global_perturbation {r : ℕ} {B X V : Type*}
    [TopologicalSpace B] [T2Space B] [NormalSpace B]
    [TopologicalSpace X] [MetricSpace V]
    (cell : Fin (r+2) → C(X,B)) (w : C(B,ℂ))
    (h : ℂ ≃ₜ ℂ)
    (hh : ∀ t : ℝ, 0 < t → ∀ z, h ((t:ℂ)*z) = (t:ℂ)*h z)
    (D : C(ℂ × ℂ,ℂ)) {M : ℝ} (hM : 0 < M) (hD : ∀ y,‖D y‖ ≤ M)
    (avoid : ∀ (z : Fin (r+1) → ℂ) (z₂ q : ℂ), (∑ i,z i)+z₂ = 0 →
      (∀ i,squareTest h (z i)-shift i = q) →
      squareTest h z₂+D (z 0,(∑ i,z i)-z 0) ≠ q)
    (f : C(B,ℂ × V)) (first : ∀ b,(f b).1 = squareTest h (w b))
    (s U : Set X) (hc : IsCompact (s \ U))
    (outside : ∀ x ∈ s \ U, ∃ i j,f (cell i x) ≠ f (cell j x))
    (balanced : ∀ x ∈ s,∑ i,w (cell i x) = 0)
    (A : TwoInterfaceChart (r+1) B)
    (models : ∀ x ∈ s,x ∈ U → A.Models cell w x) :
    ∃ G : C(B,ℂ × V), ∀ x ∈ s,∃ i j,G (cell i x) ≠ G (cell j x) := by
  obtain ⟨ε,hε,reject⟩ := Stability.uniform_rejection cell f (s \ U) hc outside
  obtain ⟨σ,hσ,hsmall⟩ := exists_small_quadratic
    (TwoInterfaceChart.bound_pos (m := r+1) hM) hε
  obtain ⟨E,hE,fix⟩ := A.exists_global_patch hσ D hM hD
  let G := perturbFirst f E
  refine ⟨G,fun x hx => ?_⟩
  by_cases hin : x ∈ U
  · obtain ⟨i,j,hij⟩ := A.rejects_model cell w h hh D avoid hσ E fix x
      (balanced x hx) (models x hx hin)
    refine ⟨i,j,fun he => hij ?_⟩
    have hf := congrArg Prod.fst he
    change (f (cell i x)).1+E (cell i x) = (f (cell j x)).1+E (cell j x) at hf
    simpa only [first] using hf
  · apply reject G (fun b => ?_) x ⟨hx,hin⟩
    rw [perturbFirst_dist]
    exact (hE b).trans hsmall

def baseTest {B V : Type*} [TopologicalSpace B] [TopologicalSpace V]
    (h : ℂ ≃ₜ ℂ) (w : C(B,ℂ)) (v : C(B,V)) : C(B,ℂ × V) :=
  ⟨fun b => (squareTest h (w b),v b), by fun_prop⟩

/-- Fairness of the nonlinear complex test and the remaining additive
coordinates forces every original moment to vanish. -/
theorem fair_base_forces_zero {n : ℕ} [NeZero n] {B V : Type*}
    [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : ℂ ≃ₜ ℂ) (hzero : h 0 = 0)
    (avoid : ∀ z ≠ 0,∀ j ≤ n,branchSum h n j z ≠ 0)
    (w : C(B,ℂ)) (v : C(B,V)) (b : Fin n → B)
    (hw : ∑ i,w (b i) = 0) (hv : ∑ i,v (b i) = 0)
    (fair : ∀ i j,baseTest h w v (b i) = baseTest h w v (b j)) :
    ∀ i,w (b i) = 0 ∧ v (b i) = 0 := by
  have hz := balanced_square_rigidity h.toEquiv hzero avoid
    (fun i => w (b i)) hw (fun i j => congrArg Prod.fst (fair i j))
  have each (i : Fin n) : v (b i) = v (b 0) := congrArg Prod.snd (fair i 0)
  have hsum : (∑ i,v (b i)) = n • v (b 0) := by
    calc
      _ = ∑ _i : Fin n,v (b 0) := Finset.sum_congr rfl (fun i _ => each i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [hsum] at hv
  have hvreal : (n:ℝ) • v (b 0) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hv
  have hzeroV : v (b 0) = 0 := (smul_eq_zero.mp hvreal).resolve_left
    (Nat.cast_ne_zero.mpr (NeZero.ne n))
  exact fun i => ⟨hz i,(each i).trans hzeroV⟩

/-- The complete analytic assembly step.  The geometric inputs consist only
of balanced continuous moments, localization of their common zero set, and
compact separated block families carrying the two-interface readings.  All
nonlinear and correction functions are constructed from the block count. -/
theorem counterexample_of_chart {r : ℕ} (hn : ¬ IsPrimePow (r+2))
    {B X V : Type*} [TopologicalSpace B] [T2Space B] [NormalSpace B]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (cell : Fin (r+2) → C(X,B)) (w : C(B,ℂ)) (v : C(B,V))
    (s U : Set X) (hc : IsCompact (s \ U))
    (balancedW : ∀ x ∈ s,∑ i,w (cell i x) = 0)
    (balancedV : ∀ x ∈ s,∑ i,v (cell i x) = 0)
    (localized : ∀ x ∈ s,(∀ i,w (cell i x) = 0 ∧ v (cell i x) = 0) → x ∈ U)
    (A : TwoInterfaceChart (r+1) B)
    (models : ∀ x ∈ s,x ∈ U → A.Models cell w x) :
    ∃ G : C(B,ℂ × V),∀ x ∈ s,∃ i j,G (cell i x) ≠ G (cell j x) := by
  obtain ⟨h,hzero,_,hh,avoid,M,D,hM,hD,havoid⟩ := exists_planar_correction r hn
  let f := baseTest h w v
  have outside : ∀ x ∈ s \ U,∃ i j,f (cell i x) ≠ f (cell j x) := by
    intro x hx
    by_contra! fair
    exact hx.2 (localized x hx.1 (fair_base_forces_zero h hzero avoid w v
      (fun i => cell i x) (balancedW x hx.1) (balancedV x hx.1) fair))
  exact exists_global_perturbation cell w h hh D hM hD havoid f (fun _ => rfl)
    s U hc outside balancedW A models

/-- Split the complex coordinate into two real characteristics and retain
each of the remaining Euclidean coordinates. -/
def realCoordinates {q : ℕ} {B : Type*} [TopologicalSpace B]
    (G : C(B,ℂ × Space q)) : Fin (q+2) → C(B,ℝ) :=
  Fin.cases ⟨fun b => (G b).1.re,by fun_prop⟩
    (Fin.cases ⟨fun b => (G b).1.im,by fun_prop⟩
      (fun k => ⟨fun b => (G b).2 k,
        (EuclideanSpace.proj k).continuous.comp (continuous_snd.comp G.continuous)⟩))

theorem realCoordinates_separates {q : ℕ} {B : Type*} [TopologicalSpace B]
    (G : C(B,ℂ × Space q)) {b c : B} (hne : G b ≠ G c) :
    ∃ k,realCoordinates G k b ≠ realCoordinates G k c := by
  by_contra! equal
  apply hne
  apply Prod.ext
  · apply Complex.ext
    · exact equal 0
    · exact equal (Fin.succ 0)
  · ext k
    exact equal k.succ.succ

/-- A vector-valued rejection supplies exactly the corresponding number of
real-valued continuous single-block characteristics. -/
theorem real_characteristics_of_rejection {q : ℕ} {B X : Type*}
    [TopologicalSpace B] [TopologicalSpace X] {n : ℕ}
    (cell : Fin n → C(X,B)) (s : Set X) (G : C(B,ℂ × Space q))
    (reject : ∀ x ∈ s,∃ i j,G (cell i x) ≠ G (cell j x)) :
    ∃ φ : Fin (q+2) → C(B,ℝ),∀ x ∈ s,∃ k i j,φ k (cell i x) ≠ φ k (cell j x) := by
  refine ⟨realCoordinates G,fun x hx => ?_⟩
  obtain ⟨i,j,hij⟩ := reject x hx
  obtain ⟨k,hk⟩ := realCoordinates_separates G hij
  exact ⟨k,i,j,hk⟩

/-- The geometric chart and localization data produce the required number
of real characteristics directly.  Openness of the chart neighborhood and
compactness of the configuration space supply the stability hypothesis. -/
theorem real_counterexample_of_chart {r q : ℕ} (hn : ¬ IsPrimePow (r+2))
    {B X : Type*} [TopologicalSpace B] [T2Space B] [NormalSpace B]
    [TopologicalSpace X]
    (cell : Fin (r+2) → C(X,B)) (w : C(B,ℂ)) (v : C(B,Space q))
    (s U : Set X) (hs : IsCompact s) (hU : IsOpen U)
    (balancedW : ∀ x ∈ s,∑ i,w (cell i x) = 0)
    (balancedV : ∀ x ∈ s,∑ i,v (cell i x) = 0)
    (localized : ∀ x ∈ s,(∀ i,w (cell i x) = 0 ∧ v (cell i x) = 0) → x ∈ U)
    (A : TwoInterfaceChart (r+1) B)
    (models : ∀ x ∈ s,x ∈ U → A.Models cell w x) :
    ∃ φ : Fin (q+2) → C(B,ℝ),∀ x ∈ s,∃ k i j,
      φ k (cell i x) ≠ φ k (cell j x) := by
  obtain ⟨G,reject⟩ := counterexample_of_chart hn cell w v s U (hs.diff hU)
    balancedW balancedV localized A models
  exact real_characteristics_of_rejection cell s G reject

/-- Evaluation of a body configuration as a compact-convex single block. -/
def partitionCell {d n : ℕ} (i : Fin n) : C((Fin n → Body d),CompactConvex d) :=
  ⟨fun S => (S i).toCompactConvex,
    (continuous_subtype_val.comp (continuous_apply i)).subtype_mk _⟩

/-- The analytic construction in the precise body-partition formulation.
Only the balanced moments and the geometric localization/chart remain as
inputs; compactness, extension, nonlinear exclusion and the dimension count
are all discharged here. -/
theorem body_counterexample_of_chart {d r q : ℕ} (hn : ¬ IsPrimePow (r+2))
    (hdim : d-1 = q+2) (K : Body d) (μ : MeasureTheory.Measure (Space d))
    [MeasureTheory.IsFiniteMeasure μ] (hμ : μ ≪ MeasureTheory.volume)
    (hK : 0 < μ K.points)
    (w : C(CompactConvex d,ℂ)) (v : C(CompactConvex d,Space q))
    (U : Set (Fin (r+2) → Body d)) (hU : IsOpen U)
    (balancedW : ∀ S : Fin (r+2) → Body d,BodyPartition K S → EqualMass μ S →
      ∑ i,w ((S i).toCompactConvex) = 0)
    (balancedV : ∀ S : Fin (r+2) → Body d,BodyPartition K S → EqualMass μ S →
      ∑ i,v ((S i).toCompactConvex) = 0)
    (localized : ∀ S : Fin (r+2) → Body d,BodyPartition K S → EqualMass μ S →
      (∀ i,w ((S i).toCompactConvex) = 0 ∧ v ((S i).toCompactConvex) = 0) → S ∈ U)
    (A : TwoInterfaceChart (r+1) (CompactConvex d))
    (models : ∀ S : Fin (r+2) → Body d,BodyPartition K S → EqualMass μ S → S ∈ U →
      A.Models partitionCell w S) :
    ∃ φ : Fin (d-1) → C(CompactConvex d,ℝ),
      ∀ S : Fin (r+2) → Body d,BodyPartition K S → EqualMass μ S →
        ∃ k i j,φ k (S i).toCompactConvex ≠ φ k (S j).toCompactConvex := by
  let s := {S : Fin (r+2) → Body d | BodyPartition K S ∧ EqualMass μ S}
  obtain ⟨ψ,reject⟩ := real_counterexample_of_chart hn partitionCell w v s U
    (compact_equalMassPartitions K μ hμ hK) hU
    (fun S hS => balancedW S hS.1 hS.2) (fun S hS => balancedV S hS.1 hS.2)
    (fun S hS => localized S hS.1 hS.2) A (fun S hS => models S hS.1 hS.2)
  refine ⟨fun k => ψ (Fin.cast hdim k),fun S hS hm => ?_⟩
  obtain ⟨k,i,j,hij⟩ := reject S ⟨hS,hm⟩
  refine ⟨Fin.cast hdim.symm k,i,j,?_⟩
  simpa only [Fin.cast_cast,Fin.cast_eq_self] using hij

end NRR.GlobalAssembly
