import NRR.Coordinates
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Geometric normalization of a prescribed full-dimensional convex body.
The construction starts with an actual inner ball touching its boundary. -/

noncomputable section
open Set Topology TopologicalSpace Metric
open scoped RealInnerProductSpace

namespace NRR.BodyNormalization

open Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The largest ball about a prescribed interior point has positive radius
and touches the boundary.  No smoothness of the body is assumed. -/
theorem exists_inner_ball_touch (K : ConvexBody E) {c : E}
    (hc : c ∈ interior (bodyPoints K)) :
    ∃ r : ℝ,0 < r ∧ ∃ y : E,y ∈ frontier (bodyPoints K) ∧
      closedBall c r ⊆ bodyPoints K ∧ dist y c = r := by
  let S := bodyPoints K
  let A := (interior S)ᶜ
  have hA : IsClosed A := isOpen_interior.isClosed_compl
  have hne : A.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    apply K.val.isCompact.ne_univ
    exact eq_univ_of_univ_subset (h ▸ interior_subset)
  let r := infDist c A
  have hr : 0 < r := (infDist_pos_iff_notMem_closure hne).mp (by
    rwa [hA.closure_eq,mem_compl_iff,not_not])
  obtain ⟨y,hy,heq⟩ := hA.exists_infDist_eq_dist hne c
  have hball : ball c r ⊆ interior S := ball_infDist_compl_subset
  have hclosed : closedBall c r ⊆ S := by
    rw [← closure_ball c hr.ne']
    exact closure_minimal (hball.trans interior_subset) K.val.isCompact.isClosed
  have hyr : dist y c = r := (dist_comm y c).trans heq.symm
  have hyS : y ∈ S := hclosed (mem_closedBall.mpr hyr.le)
  exact ⟨r,hr,y,⟨subset_closure hyS,hy⟩,hclosed,hyr⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Every boundary point of a full-dimensional closed convex body has a
nonzero supporting functional. -/
theorem exists_support_at_frontier (K : ConvexBody E) {y : E}
    (hy : y ∈ frontier (bodyPoints K)) :
    ∃ f : E →L[ℝ] ℝ,f ≠ 0 ∧ ∀ x ∈ bodyPoints K,f x ≤ f y := by
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point K.property.1.interior isOpen_interior hy.2
  have hn : f ≠ 0 := by
    intro he
    obtain ⟨c,hc⟩ := K.property.2
    simpa only [he,ContinuousLinearMap.zero_apply,lt_self_iff_false] using hf c hc
  refine ⟨f,hn,fun x hx => ?_⟩
  apply closure_minimal (fun z hz => (hf z hz).le) (isClosed_le f.continuous continuous_const)
  rwa [K.property.1.closure_interior_eq_closure_of_nonempty_interior K.property.2,
    K.val.isCompact.isClosed.closure_eq]

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A supporting functional of a Euclidean ball at a point is a positive
multiple of the radial inner product.  Consequently a body containing that
ball has a unique supporting hyperplane at a shared boundary point. -/
theorem support_ball_radial {c y : V} {r : ℝ} (hr : 0 < r) (hyr : dist y c = r)
    (f : V →L[ℝ] ℝ) (hf : f ≠ 0)
    (support : ∀ x ∈ closedBall c r,f x ≤ f y) :
    ∃ a : ℝ,0 < a ∧ ∀ x,f x = a * inner ℝ (y-c) x := by
  let v : V := (InnerProductSpace.toDual ℝ V).symm f
  have hv (x : V) : inner ℝ v x = f x := InnerProductSpace.toDual_symm_apply
  have hvne : v ≠ 0 := by
    intro he
    apply hf
    ext x
    rw [← hv x,he,inner_zero_left]
    rfl
  have hvpos := norm_pos_iff.mpr hvne
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hvne
  have huv : inner ℝ v u = ‖v‖ := by
    simp only [u,real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  have hz : c+r • u ∈ closedBall c r := by
    simp only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,hu,
      Real.norm_eq_abs,abs_of_pos hr,mul_one,le_refl]
  have hsup := support (c+r • u) hz
  rw [map_add,map_smul,← hv u,huv,smul_eq_mul] at hsup
  have hyrnorm : ‖y-c‖ = r := by simpa only [dist_eq_norm] using hyr
  have heq : inner ℝ v (y-c) = ‖v‖ * ‖y-c‖ := by
    apply le_antisymm (real_inner_le_norm _ _)
    rw [inner_sub_right,hv y,hv c,hyrnorm]
    linarith
  have hrad := inner_eq_norm_mul_iff_real.mp heq
  rw [hyrnorm] at hrad
  refine ⟨‖v‖/r,div_pos hvpos hr,fun x => ?_⟩
  have he := congrArg (fun z : V => inner ℝ z x) hrad
  simp only [real_inner_smul_left,hv x] at he
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  change f x * r = ‖v‖ * inner ℝ (y-c) x
  nlinarith

/-- At a ball-contact point, every chord pointing strictly into the tangent
half-space lies in the interior except for its endpoints. -/
theorem openSegment_interior_of_ball_touch (K : ConvexBody V) {c y x : V} {r : ℝ}
    (hr : 0 < r) (hyr : dist y c = r) (hball : closedBall c r ⊆ bodyPoints K)
    (hx : x ∈ bodyPoints K) (inward : inner ℝ (y-c) (x-y) < 0) :
    openSegment ℝ x y ⊆ interior (bodyPoints K) := by
  rintro z ⟨a,b,ha,hb,hab,heq⟩
  have hy : y ∈ bodyPoints K := hball (mem_closedBall.mpr hyr.le)
  have hz : z ∈ bodyPoints K := heq ▸ K.property.1 hx hy ha.le hb.le hab
  by_contra hi
  obtain ⟨g,hgn,hg⟩ := exists_support_at_frontier K ⟨subset_closure hz,hi⟩
  have hgx := hg x hx
  have hgy := hg y hy
  have hsum : a*g x+b*g y = g z := by
    simpa only [map_add,map_smul,smul_eq_mul] using congrArg g heq
  have hbalance : a*(g z-g x)+b*(g z-g y) = 0 := by
    calc
      _ = (a+b)*g z-(a*g x+b*g y) := by ring
      _ = 0 := by rw [hab,hsum]; ring
  have hzeroX : g x = g z := by
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hgy)]
  have hzeroY : g y = g z := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hgx)]
  obtain ⟨t,ht,hgt⟩ := support_ball_radial hr hyr g hgn
    (fun u hu => (hg u (hball hu)).trans_eq hzeroY.symm)
  have hstrict : g x < g y := by
    rw [hgt x,hgt y]
    exact mul_lt_mul_of_pos_left (sub_neg.mp (by simpa only [inner_sub_right] using inward)) ht
  exact hstrict.ne (hzeroX.trans hzeroY.symm)

/-- A prescribed full-dimensional compact convex body has two opposite
parallel supporting hyperplanes joined by an interior open chord. -/
theorem exists_parallel_supporting_chord [Nontrivial V] (K : ConvexBody V) :
    ∃ (ym yp : V) (f : V →L[ℝ] ℝ),ym ∈ bodyPoints K ∧ yp ∈ bodyPoints K ∧
      f ≠ 0 ∧ f ym < f yp ∧
      (∀ x ∈ bodyPoints K,f ym ≤ f x ∧ f x ≤ f yp) ∧
      openSegment ℝ ym yp ⊆ interior (bodyPoints K) := by
  obtain ⟨c,hc⟩ := K.property.2
  obtain ⟨r,hr,yp,hyfront,hball,hyr⟩ := exists_inner_ball_touch K hc
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point K.property.1.interior
    isOpen_interior hyfront.2
  have hfn : f ≠ 0 := by
    intro he
    simpa only [he,ContinuousLinearMap.zero_apply,lt_self_iff_false] using hf c hc
  have support (x : V) (hx : x ∈ bodyPoints K) : f x ≤ f yp := by
    apply closure_minimal (fun z hz => (hf z hz).le) (isClosed_le f.continuous continuous_const)
    rwa [K.property.1.closure_interior_eq_closure_of_nonempty_interior K.property.2,
      K.val.isCompact.isClosed.closure_eq]
  obtain ⟨ym,hymin,hmin⟩ := K.val.isCompact.exists_isMinOn K.val.nonempty f.continuous.continuousOn
  have hgap : f ym < f yp := (hmin (interior_subset hc)).trans_lt (hf c hc)
  obtain ⟨t,ht,hft⟩ := support_ball_radial hr hyr f hfn (fun x hx => support x (hball hx))
  have inward : inner ℝ (yp-c) (ym-yp) < 0 := by
    rw [inner_sub_right]
    rw [hft ym,hft yp] at hgap
    exact sub_neg.mpr ((mul_lt_mul_iff_of_pos_left ht).mp hgap)
  exact ⟨ym,yp,f,hymin,hball (mem_closedBall.mpr hyr.le),hfn,hgap,
    fun x hx => ⟨hmin hx,support x hx⟩,
    openSegment_interior_of_ball_touch K hr hyr hball hymin inward⟩

end Inner

section Frame

/-- Splitting a nonzero linear height functional using a prescribed vector
of height one.  That vector, rather than an orthogonal normal, becomes the
vertical direction, so an arbitrary interior chord can be made vertical. -/
def splitKer {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : W →L[ℝ] ℝ) (v : W) (hv : f v = 1) : W ≃ₗ[ℝ] (LinearMap.ker f.toLinearMap) × ℝ where
  toFun x := (⟨x-f x • v,by simp [map_sub,map_smul,hv]⟩,f x)
  invFun p := p.1.val+p.2 • v
  left_inv x := by change x-f x • v+f x • v = x; abel
  right_inv p := by
    rcases p with ⟨u,t⟩
    have hu : f u.val = 0 := u.property
    have he : f (u.val+t • v) = t := by simp [hu,hv]
    apply Prod.ext
    · apply Subtype.ext
      change u.val+t • v-f (u.val+t • v) • v = u.val
      rw [he]
      abel
    · exact he
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x+y-f (x+y) • v = (x-f x • v)+(y-f y • v)
      rw [map_add,add_smul]
      abel
    · exact map_add f x y
  map_smul' t x := by
    apply Prod.ext
    · apply Subtype.ext
      change t • x-f (t • x) • v = t • (x-f x • v)
      rw [map_smul,smul_eq_mul,smul_sub,smul_smul]
    · exact map_smul f t x

theorem finrank_ker_height {d : ℕ} (f : Space (d+1) →L[ℝ] ℝ) (v : Space (d+1))
    (hv : f v = 1) : Module.finrank ℝ (LinearMap.ker f.toLinearMap) = d := by
  have he := (splitKer f v hv).finrank_eq
  have hd : d+1 = Module.finrank ℝ (LinearMap.ker f.toLinearMap)+1 := by
    simpa only [finrank_euclideanSpace_fin,Module.finrank_prod,Module.finrank_self] using he
  omega

def kernelCoordinates {d : ℕ} (f : Space (d+1) →L[ℝ] ℝ) (v : Space (d+1))
    (hv : f v = 1) : (LinearMap.ker f.toLinearMap) ≃L[ℝ] Space d :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_ker_height f v hv,finrank_euclideanSpace_fin])

/-- The explicit affine frame centered at `c`, with `f` as height and `v`
as its vertical vector. -/
def normalizingFrame {d : ℕ} (f : Space (d+1) →L[ℝ] ℝ) (v c : Space (d+1))
    (hv : f v = 1) : Space (d+1) ≃ᴬ[ℝ] Space d × ℝ :=
  ((ContinuousAffineEquiv.constVAdd ℝ (Space (d+1)) (-c)).trans
    (splitKer f v hv).toContinuousLinearEquiv.toContinuousAffineEquiv).trans
    (((kernelCoordinates f v hv).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousAffineEquiv)

theorem normalizingFrame_snd {d : ℕ} (f : Space (d+1) →L[ℝ] ℝ) (v c x : Space (d+1))
    (hv : f v = 1) : (normalizingFrame f v c hv x).2 = f (x-c) := by
  change f (-c+x) = f (x-c)
  congr 1
  abel

theorem normalizingFrame_axis {d : ℕ} (f : Space (d+1) →L[ℝ] ℝ) (v c : Space (d+1))
    (hv : f v = 1) (t : ℝ) : normalizingFrame f v c hv (c+t • v) = (0,t) := by
  apply Prod.ext
  · change kernelCoordinates f v hv
      ⟨(-c+(c+t • v))-f (-c+(c+t • v)) • v,_⟩ = 0
    have he : -c+(c+t • v) = t • v := by abel
    simp only [he,map_smul,hv,smul_eq_mul,mul_one,sub_self]
    exact map_zero _
  · rw [normalizingFrame_snd]
    have he : c+t • v-c = t • v := by abel
    simp only [he,map_smul,hv,smul_eq_mul,mul_one]

end Frame

/-- Every full-dimensional Euclidean compact convex body admits affine
horizontal-height coordinates in which the body has height in `[-1,1]`
and the whole open vertical unit chord belongs to its interior. -/
theorem exists_normalized_coordinates {d : ℕ} (K : Body (d+1)) :
    ∃ e : Space (d+1) ≃ᴬ[ℝ] Space d × ℝ,
      (∀ q ∈ bodyPoints (Coordinates.Affine.bodiesHomeomorph e K),|q.2| ≤ 1) ∧
      ∀ t : ℝ,-1 < t → t < 1 →
        ((0,t) : Space d × ℝ) ∈ interior (bodyPoints (Coordinates.Affine.bodiesHomeomorph e K)) := by
  obtain ⟨ym,yp,f,hym,hyp,_,hgap,bounds,chord⟩ := exists_parallel_supporting_chord K
  let g : Space (d+1) →L[ℝ] ℝ := (2/(f yp-f ym)) • f
  let v : Space (d+1) := (1/2 : ℝ) • (yp-ym)
  let c : Space (d+1) := (1/2 : ℝ) • (yp+ym)
  have hden : f yp-f ym ≠ 0 := sub_ne_zero.mpr hgap.ne'
  have hgv : g v = 1 := by
    simp only [g,v,ContinuousLinearMap.smul_apply,map_smul,map_sub,smul_eq_mul]
    field_simp
  let e := normalizingFrame g v c hgv
  have height (x : Space (d+1)) :
      (f yp-f ym)*(e x).2 = 2*f x-f yp-f ym := by
    rw [normalizingFrame_snd]
    simp only [g,c,ContinuousLinearMap.smul_apply,map_sub,map_smul,map_add,smul_eq_mul]
    field_simp
    ring
  refine ⟨e,?_,?_⟩
  · rintro q ⟨x,hx,rfl⟩
    obtain ⟨hlo,hhi⟩ := bounds x hx
    have he := height x
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  · intro t htlo hthi
    have hseg : c+t • v ∈ openSegment ℝ ym yp := by
      refine ⟨(1-t)/2,(1+t)/2,by linarith,by linarith,by ring,?_⟩
      dsimp [c,v]
      module
    rw [Coordinates.Affine.bodyPoints_bodiesHomeomorph,← Coordinates.Affine.interior_image]
    exact ⟨c+t • v,chord hseg,normalizingFrame_axis g v c hgv t⟩

end NRR.BodyNormalization
