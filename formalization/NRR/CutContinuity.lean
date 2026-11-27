import NRR.InterfaceChart
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Hausdorff continuity of convex bodies clipped between affine graphs. -/

noncomputable section
open Set Topology Metric TopologicalSpace Filter
set_option maxHeartbeats 800000

namespace NRR.InterfaceChart

theorem height_dist_le {d : ℕ} (p q : Parameters d) (u : Space d) :
    |height p u - height q u| ≤ (‖u‖+1) * dist p q := by
  have hs : ‖(p.1-q.1) u‖ ≤ ‖p.1-q.1‖ * ‖u‖ := (p.1-q.1).le_opNorm u
  have hp : ‖p.1-q.1‖ ≤ dist p q := by
    simpa only [dist_eq_norm] using (le_max_left (dist p.1 q.1) (dist p.2 q.2))
  have hb : |p.2-q.2| ≤ dist p q := by
    simpa only [Real.dist_eq] using (le_max_right (dist p.1 q.1) (dist p.2 q.2))
  have he : height p u - height q u = ((p.1-q.1) u) + (p.2-q.2) := by
    simp only [height,ContinuousLinearMap.sub_apply]
    ring
  rw [he]
  have H := abs_add_le ((p.1-q.1) u) (p.2-q.2)
  rw [← Real.norm_eq_abs] at H
  calc
    _ ≤ ‖(p.1-q.1) u‖ + |p.2-q.2| := H
    _ ≤ ‖p.1-q.1‖*‖u‖ + dist p q := add_le_add hs hb
    _ ≤ dist p q * ‖u‖ + dist p q := by gcongr
    _ = _ := by ring

private theorem height_combo {d : ℕ} (p : Parameters d)
    (x y : Space d × ℝ) (t : ℝ) :
    height p (((1-t) • x + t • y).1) =
      (1-t) * height p x.1 + t * height p y.1 := by
  change p.1 ((1-t) • x.1 + t • y.1) + p.2 = _
  simp only [height,map_add,map_smul,smul_eq_mul]
  ring

/-- Moving slightly toward one strict feasible point repairs a uniformly
small perturbation of both affine inequalities. -/
theorem blend_mem_clippedSlab {d : ℕ} {K : Set (Space d × ℝ)} (convex : Convex ℝ K)
    {p q p' q' : Parameters d} {x y : Space d × ℝ} {t ρ e : ℝ}
    (hx : x ∈ clippedSlab K p q) (hy : y ∈ K)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (he : 0 ≤ e) (hsmall : e ≤ t*ρ)
    (errLower : ∀ z ∈ K, |height p z.1-height p' z.1| ≤ e)
    (errUpper : ∀ z ∈ K, |height q z.1-height q' z.1| ≤ e)
    (lower : height p' y.1 + ρ ≤ y.2) (upper : y.2 + ρ ≤ height q' y.1) :
    ((1-t) • x + t • y) ∈ clippedSlab K p' q' := by
  have hlow := (abs_le.mp (errLower x hx.1)).1
  have hupp := (abs_le.mp (errUpper x hx.1)).2
  refine ⟨convex hx.1 hy (by linarith) ht (by ring),?_,?_⟩
  · rw [height_combo]
    change (1-t)*height p' x.1 + t*height p' y.1 ≤ (1-t)*x.2 + t*y.2
    have h1 := mul_le_mul_of_nonneg_left (show height p' x.1 ≤ x.2+e by linarith [hx.2.1])
      (show 0 ≤ 1-t by linarith)
    have h2 := mul_le_mul_of_nonneg_left lower ht
    nlinarith [mul_nonneg ht he]
  · rw [height_combo]
    change (1-t)*x.2 + t*y.2 ≤ (1-t)*height q' x.1 + t*height q' y.1
    have h1 := mul_le_mul_of_nonneg_left (show x.2-e ≤ height q' x.1 by linarith [hx.2.2])
      (show 0 ≤ 1-t by linarith)
    have h2 := mul_le_mul_of_nonneg_left upper ht
    nlinarith [mul_nonneg ht he]

/-- Strict feasibility is precisely the nondegeneracy needed for continuity:
the clipping planes may move and rotate, while the parent convex compact
set stays fixed. No regularity of its boundary is assumed. -/
theorem continuous_clippedSlab {d : ℕ} {X : Type*} [TopologicalSpace X]
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    (p q : X → Parameters d) (hp : Continuous p) (hq : Continuous q)
    (C : X → NonemptyCompacts (Space d × ℝ))
    (repr : ∀ s, (C s : Set (Space d × ℝ)) = clippedSlab K (p s) (q s))
    (strict : ∀ s, ∃ y ∈ K, height (p s) y.1 < y.2 ∧ y.2 < height (q s) y.1) :
    Continuous C := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y,hy,hyl,hyu⟩ := strict s
  obtain ⟨R,hR,bound⟩ := (compact.image continuous_fst).isBounded.exists_pos_norm_le
  let ρ := min (y.2-height (p s) y.1) (height (q s) y.1-y.2) / 2
  have hρ : 0 < ρ := half_pos (lt_min (sub_pos.mpr hyl) (sub_pos.mpr hyu))
  have slackLower : height (p s) y.1 + 2*ρ ≤ y.2 := by
    have := min_le_left (y.2-height (p s) y.1) (height (q s) y.1-y.2)
    dsimp [ρ]
    linarith
  have slackUpper : y.2 + 2*ρ ≤ height (q s) y.1 := by
    have := min_le_right (y.2-height (p s) y.1) (height (q s) y.1-y.2)
    dsimp [ρ]
    linarith
  let t := min (1/2 : ℝ) (ε / (2*(diam K+1)))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htε : t * diam K < ε := by
    have ht' : t ≤ ε/(2*(diam K+1)) := min_le_right _ _
    have mul : t*(2*(diam K+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp ht'
    nlinarith [diam_nonneg (s := K)]
  let e := t*ρ/2
  have he : 0 < e := by dsimp [e]; positivity
  have heρ : e ≤ ρ := by dsimp [e]; nlinarith
  have hesmall : e ≤ t*ρ := by dsimp [e]; nlinarith [mul_pos ht hρ]
  let δ := e/(R+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have nearp : ∀ᶠ v in 𝓝 s, dist (p v) (p s) < δ :=
    (hp.tendsto s).eventually (Metric.ball_mem_nhds _ hδ)
  have nearq : ∀ᶠ v in 𝓝 s, dist (q v) (q s) < δ :=
    (hq.tendsto s).eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [nearp,nearq] with v hvp hvq
  have err (a b : Parameters d) (near : dist a b < δ) (x : Space d × ℝ) (hx : x ∈ K) :
      |height a x.1-height b x.1| ≤ e := by
    have bx : ‖x.1‖ ≤ R := bound x.1 (mem_image_of_mem Prod.fst hx)
    have mul : (R+1)*dist a b < e := by
      rw [mul_comm]
      exact (lt_div_iff₀ (by linarith)).mp near
    exact (height_dist_le a b x.1).trans
      ((mul_le_mul_of_nonneg_right (by linarith : ‖x.1‖+1 ≤ R+1) dist_nonneg).trans mul.le)
  have errp (x) (hx : x ∈ K) := err (p v) (p s) hvp x hx
  have errq (x) (hx : x ∈ K) := err (q v) (q s) hvq x hx
  have errp' (x) (hx : x ∈ K) : |height (p s) x.1-height (p v) x.1| ≤ e := by
    rw [abs_sub_comm]
    exact errp x hx
  have errq' (x) (hx : x ∈ K) : |height (q s) x.1-height (q v) x.1| ≤ e := by
    rw [abs_sub_comm]
    exact errq x hx
  have strictvLower : height (p v) y.1+ρ ≤ y.2 := by
    have := (abs_le.mp (errp y hy)).2
    linarith
  have strictvUpper : y.2+ρ ≤ height (q v) y.1 := by
    have := (abs_le.mp (errq y hy)).1
    linarith
  have close (x : Space d × ℝ) (hx : x ∈ K) :
      dist x ((1-t) • x + t • y) ≤ t*diam K := by
    have hdist : dist x (AffineMap.lineMap x y t) = t * dist x y := by
      simpa only [Real.norm_eq_abs, abs_of_pos ht] using dist_left_lineMap x y t
    rw [← AffineMap.lineMap_apply_module] 
    rw [hdist]
    exact mul_le_mul_of_nonneg_left (dist_le_diam_of_mem compact.isBounded hx hy) ht.le
  have hd : dist (C v) (C s) ≤ t*diam K := by
    apply hausdorffDist_le_of_mem_dist (by positivity)
    · intro x hx
      rw [repr] at hx
      refine ⟨(1-t) • x + t • y,?_,close x hx.1⟩
      rw [repr]
      exact blend_mem_clippedSlab convex hx hy ht.le ht1 he.le hesmall errp errq
        (by linarith [slackLower]) (by linarith [slackUpper])
    · intro x hx
      rw [repr] at hx
      refine ⟨(1-t) • x + t • y,?_,close x hx.1⟩
      rw [repr]
      exact blend_mem_clippedSlab convex hx hy ht.le ht1 he.le hesmall errp' errq'
        strictvLower strictvUpper
  exact hd.trans_lt htε

/-- Pairs of affine planes with a strictly positive gap at some point of
the parent set. This is an open parameter domain. -/
abbrev FeasibleParameters {d : ℕ} (K : Set (Space d × ℝ)) :=
  {r : Parameters d × Parameters d //
    ∃ y ∈ K, height r.1 y.1 < y.2 ∧ y.2 < height r.2 y.1}

theorem continuous_height_parameters {d : ℕ} (u : Space d) :
    Continuous (fun p : Parameters d => height p u) := by
  dsimp [height]
  fun_prop

theorem isOpen_feasibleParameters {d : ℕ} (K : Set (Space d × ℝ)) :
    IsOpen {r : Parameters d × Parameters d |
      ∃ y ∈ K, height r.1 y.1 < y.2 ∧ y.2 < height r.2 y.1} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro r ⟨y,hy,hl,hu⟩
  let U := {r : Parameters d × Parameters d |
    height r.1 y.1 < y.2 ∧ y.2 < height r.2 y.1}
  have hU : IsOpen U :=
    (isOpen_lt ((continuous_height_parameters y.1).comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_const ((continuous_height_parameters y.1).comp continuous_snd))
  exact mem_nhds_iff.mpr ⟨U,fun s hs => ⟨y,hy,hs⟩,hU,⟨hl,hu⟩⟩

/-- The actual nonempty compact body cut out by a feasible pair of planes. -/
def cutCompact {d : ℕ} {K : Set (Space d × ℝ)} (compact : IsCompact K)
    (r : FeasibleParameters K) : NonemptyCompacts (Space d × ℝ) := by
  have low : Continuous (fun x : Space d × ℝ => height r.val.1 x.1) := by
    dsimp [height]
    fun_prop
  have high : Continuous (fun x : Space d × ℝ => height r.val.2 x.1) := by
    dsimp [height]
    fun_prop
  refine ⟨⟨clippedSlab K r.val.1 r.val.2,compact.inter_right
    ((isClosed_le low continuous_snd).inter (isClosed_le continuous_snd high))⟩,?_⟩
  obtain ⟨y,hy,hl,hu⟩ := r.property
  exact ⟨y,hy,hl.le,hu.le⟩

@[simp] theorem coe_cutCompact {d : ℕ} {K : Set (Space d × ℝ)} (compact : IsCompact K)
    (r : FeasibleParameters K) :
    (cutCompact compact r : Set (Space d × ℝ)) = clippedSlab K r.val.1 r.val.2 := rfl

theorem continuous_cutCompact {d : ℕ} {K : Set (Space d × ℝ)}
    (compact : IsCompact K) (convex : Convex ℝ K) : Continuous (cutCompact compact) :=
  continuous_clippedSlab compact convex (fun r => r.val.1) (fun r => r.val.2)
    (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
    (cutCompact compact) (fun _ => rfl) (fun r => r.property)

/-- On a compact parameter family whose interfaces remain inside the inner
cylinder, the single-body parameterization is a closed embedding. Thus its
inverse reads both affine interfaces continuously from the body itself. -/
theorem compact_parameter_isClosedEmbedding {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi) :
    IsClosedEmbedding (fun r : S => cutCompact compact r.val) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  apply ((continuous_cutCompact compact convex).comp continuous_subtype_val).isClosedEmbedding
  intro r s he
  have he' : clippedSlab K r.val.val.1 r.val.val.2 =
      clippedSlab K s.val.val.1 s.val.val.2 :=
    congrArg (fun C : NonemptyCompacts (Space d × ℝ) => (C : Set (Space d × ℝ))) he
  obtain ⟨hl,hu⟩ := parameters_eq_of_clippedSlab_eq hD inner
    (bounds r.val r.property) (bounds s.val s.property) he'
  exact Subtype.ext (Subtype.ext (Prod.ext hl hu))

/-- A native homeomorphism onto the image of the compact single-body
chart; its inverse is the required continuous interface readout. -/
def compact_parameter_homeomorph {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi) :
    S ≃ₜ range (fun r : S => cutCompact compact r.val) :=
  (compact_parameter_isClosedEmbedding compact convex hD inner S hS bounds).isEmbedding.toHomeomorph

/-- Away from vertical coefficient zero, converting a separating functional
to its affine height graph is continuous in both the functional and offset. -/
theorem continuousAt_graphParameters {d : ℕ}
    (r : ((Space d × ℝ) →L[ℝ] ℝ) × ℝ) (hne : r.1 (0,1) ≠ 0) :
    ContinuousAt (fun s : ((Space d × ℝ) →L[ℝ] ℝ) × ℝ => graphParameters s.1 s.2) r := by
  have coef : Continuous (fun s : ((Space d × ℝ) →L[ℝ] ℝ) × ℝ => s.1 (0,1)) :=
    continuous_fst.clm_apply continuous_const
  have restriction : Continuous (fun s : ((Space d × ℝ) →L[ℝ] ℝ) × ℝ =>
      s.1.comp (ContinuousLinearMap.inl ℝ (Space d) ℝ)) :=
    continuous_fst.clm_comp_const _
  exact ((coef.continuousAt.inv₀ hne).neg.smul restriction.continuousAt).prodMk
    (continuous_snd.continuousAt.div coef.continuousAt hne)

theorem graphParameters_of_vertical {d : ℕ} (F : (Space d × ℝ) →L[ℝ] ℝ)
    {c t : ℝ} (hne : F (0,1) ≠ 0) (offset : c = t * F (0,1))
    (vertical : ∀ x, F x = x.2 * F (0,1)) : graphParameters F c = (0,t) := by
  have horizontal : F.comp (ContinuousLinearMap.inl ℝ (Space d) ℝ) = 0 := by
    ext u
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.zero_apply,zero_mul] using vertical (u,0)
  simp only [graphParameters,horizontal,smul_zero,offset,mul_div_cancel_right₀ _ hne]

/-- A convergent sequence of nonzero separators of a horizontal face has
affine graph parameters converging to that horizontal plane. In particular,
the slopes tend to zero; the height is fixed by the common open face. -/
theorem tendsto_graphParameters_of_horizontal_face {d : ℕ}
    {F : ℕ → (Space d × ℝ) →L[ℝ] ℝ} {G : (Space d × ℝ) →L[ℝ] ℝ}
    (hF : Tendsto F atTop (𝓝 G)) {c : ℕ → ℝ} {b : ℝ} (hc : Tendsto c atTop (𝓝 b))
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) (hne : G ≠ 0)
    {a t : ℝ} (hat : a < t) (lower : G (0,a) ≤ b)
    (face : ∀ u ∈ D, G (u,t) = b) :
    (∀ᶠ n in atTop, 0 < F n (0,1)) ∧
      Tendsto (fun n => graphParameters (F n) (c n)) atTop (𝓝 (0,t)) := by
  obtain ⟨positive,offset,vertical⟩ := separator_eq_vertical hD G hne hat lower face
  have coef : Continuous (fun H : (Space d × ℝ) →L[ℝ] ℝ => H (0,1)) :=
    continuous_id.clm_apply continuous_const
  refine ⟨(coef.continuousAt.tendsto.comp hF).eventually (lt_mem_nhds positive),?_⟩
  have h := (continuousAt_graphParameters (G,b) positive.ne').tendsto.comp (hF.prodMk_nhds hc)
  simpa only [graphParameters_of_vertical G positive.ne' offset vertical] using h

/-- Positive vertical coefficient and closeness of graph parameters form
an open condition on the affine separator. -/
theorem isOpen_good_graphParameters {d : ℕ} (t η : ℝ) :
    IsOpen {r : ((Space d × ℝ) →L[ℝ] ℝ) × ℝ |
      0 < r.1 (0,1) ∧ dist (graphParameters r.1 r.2) (0,t) < η} := by
  apply isOpen_iff_mem_nhds.mpr
  intro r hr
  have coef : Continuous (fun s : ((Space d × ℝ) →L[ℝ] ℝ) × ℝ => s.1 (0,1)) :=
    continuous_fst.clm_apply continuous_const
  have hpos := coef.continuousAt.eventually (lt_mem_nhds hr.1)
  have hclose := ((continuousAt_graphParameters r hr.1.ne').dist continuousAt_const).eventually
    (gt_mem_nhds hr.2)
  filter_upwards [hpos,hclose] with s hs ht
  exact ⟨hs,ht⟩

/-- Uniform local graph-chart theorem for two horizontal neighbors. For
every prescribed slope/height tolerance there is a Hausdorff neighborhood
in which every normalized weak separator has a positive vertical
coefficient and affine graph parameters within that tolerance. -/
theorem exists_graph_neighborhood {d : ℕ}
    (A B : NonemptyCompacts (Space d × ℝ))
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
    {a t : ℝ} (hat : a < t) (ha : (0,a) ∈ A)
    (faceA : ∀ u ∈ D, (u,t) ∈ A) (faceB : ∀ u ∈ D, (u,t) ∈ B)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : Set (NonemptyCompacts (Space d × ℝ) × NonemptyCompacts (Space d × ℝ)),
      IsOpen U ∧ (A,B) ∈ U ∧
      ∀ q ∈ U, ∀ (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ), ‖(F,c)‖ = 1 →
        Separates q.1 q.2 F c →
          0 < F (0,1) ∧ dist (graphParameters F c) (0,t) < η := by
  let P := ((Space d × ℝ) →L[ℝ] ℝ) × ℝ
  let Q := NonemptyCompacts (Space d × ℝ) × NonemptyCompacts (Space d × ℝ)
  let good : Set P := {r | 0 < r.1 (0,1) ∧ dist (graphParameters r.1 r.2) (0,t) < η}
  let bad : Set P := sphere 0 1 ∩ goodᶜ
  have hbad : IsCompact bad :=
    (isCompact_sphere (0 : P) 1).inter_right (isOpen_good_graphParameters t η).isClosed_compl
  letI : CompactSpace bad := isCompact_iff_compactSpace.mp hbad
  let R : Set (Q × bad) := {q | Separates q.1.1 q.1.2 q.2.val.1 q.2.val.2}
  have hR : IsClosed R :=
    (isClosed_separators d).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have closedBad : IsClosed (Prod.fst '' R) := isClosedMap_fst_of_compactSpace _ hR
  let U := (Prod.fst '' R)ᶜ
  have inU : (A,B) ∈ U := by
    rintro ⟨⟨q,r⟩,hsep,hq⟩
    change q = (A,B) at hq
    subst q
    have normr : ‖r.val‖ = 1 := by
      simpa only [mem_sphere,dist_zero_right] using r.property.1
    have nonzero : r.val.1 ≠ 0 := by
      intro he
      obtain ⟨x,hx⟩ := A.nonempty
      obtain ⟨y,hy⟩ := B.nonempty
      have hl := hsep.1 x hx
      have hu := hsep.2 y hy
      simp only [he,ContinuousLinearMap.zero_apply] at hl hu
      have hz : r.val.2 = 0 := le_antisymm hu hl
      have hr : r.val = 0 := Prod.ext he hz
      rw [hr,norm_zero] at normr
      norm_num at normr
    have onface (u : Space d) (hu : u ∈ D) : r.val.1 (u,t) = r.val.2 :=
      le_antisymm (hsep.1 _ (faceA u hu)) (hsep.2 _ (faceB u hu))
    obtain ⟨positive,offset,vertical⟩ :=
      separator_eq_vertical hD r.val.1 nonzero hat (hsep.1 _ ha) onface
    have ingood : r.val ∈ good := by
      refine ⟨positive,?_⟩
      rw [graphParameters_of_vertical r.val.1 positive.ne' offset vertical]
      simpa using hη
    exact r.property.2 ingood
  refine ⟨U,closedBad.isOpen_compl,inU,?_⟩
  intro q hq F c hn hs
  by_contra hnot
  have memBad : (F,c) ∈ bad :=
    ⟨by simpa only [mem_sphere,dist_zero_right] using hn,hnot⟩
  exact hq ⟨(q,⟨(F,c),memBad⟩),hs,rfl⟩

theorem graphParameters_pos_smul {d : ℕ} (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ)
    {a : ℝ} (ha : 0 < a) : graphParameters (a • F) (a*c) = graphParameters F c := by
  apply parameters_eq_of_height_eq (D := univ) (by simp)
  intro u _
  rw [height_graphParameters,height_graphParameters]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [← mul_sub]
  exact mul_div_mul_left _ _ ha.ne'

/-- The local graph-chart theorem applies to arbitrary nonzero separators;
normalization is performed inside the proof and does not affect the plane. -/
theorem exists_graph_neighborhood_of_nonzero {d : ℕ}
    (A B : NonemptyCompacts (Space d × ℝ))
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
    {a t : ℝ} (hat : a < t) (ha : (0,a) ∈ A)
    (faceA : ∀ u ∈ D, (u,t) ∈ A) (faceB : ∀ u ∈ D, (u,t) ∈ B)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : Set (NonemptyCompacts (Space d × ℝ) × NonemptyCompacts (Space d × ℝ)),
      IsOpen U ∧ (A,B) ∈ U ∧
      ∀ q ∈ U, ∀ (F : (Space d × ℝ) →L[ℝ] ℝ) (c : ℝ), F ≠ 0 →
        Separates q.1 q.2 F c →
          0 < F (0,1) ∧ dist (graphParameters F c) (0,t) < η := by
  obtain ⟨U,hU,memU,chart⟩ := exists_graph_neighborhood A B hD hat ha faceA faceB hη
  refine ⟨U,hU,memU,?_⟩
  intro q hq F c hne hs
  have pairne : (F,c) ≠ 0 := fun he => hne (congrArg Prod.fst he)
  have hn : 0 < ‖(F,c)‖ := norm_pos_iff.mpr pairne
  let α := ‖(F,c)‖⁻¹
  have hα : 0 < α := inv_pos.mpr hn
  have normalized : ‖(α • F,α*c)‖ = 1 :=
    norm_smul_inv_norm (𝕜 := ℝ) pairne
  have sep : Separates q.1 q.2 (α • F) (α*c) := by
    constructor
    · intro x hx
      exact mul_le_mul_of_nonneg_left (hs.1 x hx) hα.le
    · intro x hx
      exact mul_le_mul_of_nonneg_left (hs.2 x hx) hα.le
  obtain ⟨positive,close⟩ := chart q hq (α • F) (α*c) normalized sep
  have positive' : 0 < F (0,1) := by
    by_contra! h
    exact (not_le_of_gt positive) (mul_nonpos_of_nonneg_of_nonpos hα.le h)
  exact ⟨positive',by simpa only [graphParameters_pos_smul F c hα] using close⟩

/-- Intersecting a convex parent with two affine halfspaces preserves
convexity, including at degenerate parameter values. -/
theorem convex_clippedSlab {d : ℕ} {K : Set (Space d × ℝ)}
    (convex : Convex ℝ K) (p q : Parameters d) : Convex ℝ (clippedSlab K p q) := by
  let low := p.1.comp (ContinuousLinearMap.fst ℝ (Space d) ℝ) -
    ContinuousLinearMap.snd ℝ (Space d) ℝ
  let high := ContinuousLinearMap.snd ℝ (Space d) ℝ -
    q.1.comp (ContinuousLinearMap.fst ℝ (Space d) ℝ)
  have lower : Convex ℝ {x : Space d × ℝ | height p x.1 ≤ x.2} := by
    convert convex_halfSpace_le low.toLinearMap.isLinear (-p.2) using 1
    ext x
    change p.1 x.1+p.2 ≤ x.2 ↔ p.1 x.1-x.2 ≤ -p.2
    constructor <;> intro h <;> linarith
  have upper : Convex ℝ {x : Space d × ℝ | x.2 ≤ height q x.1} := by
    convert convex_halfSpace_le high.toLinearMap.isLinear q.2 using 1
    ext x
    change x.2 ≤ q.1 x.1+q.2 ↔ x.2-q.1 x.1 ≤ q.2
    constructor <;> intro h <;> linarith
  exact convex.inter (lower.inter upper)

theorem mem_interior_clippedSlab {d : ℕ} {K : Set (Space d × ℝ)}
    (p q : Parameters d) {y : Space d × ℝ} (hy : y ∈ interior K)
    (hl : height p y.1 < y.2) (hu : y.2 < height q y.1) :
    y ∈ interior (clippedSlab K p q) := by
  have low : Continuous (fun x : Space d × ℝ => height p x.1) := by dsimp [height]; fun_prop
  have high : Continuous (fun x : Space d × ℝ => height q x.1) := by dsimp [height]; fun_prop
  let U := interior K ∩ ({x : Space d × ℝ | height p x.1 < x.2} ∩
    {x : Space d × ℝ | x.2 < height q x.1})
  have hU : IsOpen U := isOpen_interior.inter
    ((isOpen_lt low continuous_snd).inter (isOpen_lt continuous_snd high))
  have sub : U ⊆ clippedSlab K p q :=
    fun x hx => ⟨interior_subset hx.1,hx.2.1.le,hx.2.2.le⟩
  exact interior_maximal sub hU ⟨hy,hl,hu⟩

/-- A whole finite horizontal chain has one common neighborhood in which
every convex partition is described by small affine prefix/suffix cuts.
The nonadjacent-disjoint condition is obtained from openness, rather than
being imposed on the neighboring partitions as an extra hypothesis. -/
theorem exists_chain_graph_neighborhood {d r : ℕ}
    (H : Fin (r+2) → NonemptyCompacts (Space d × ℝ))
    (nonadjacent : ∀ i j, i.val+1 < j.val → Disjoint (H i : Set (Space d × ℝ)) (H j))
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D)
    (a t : Fin (r+1) → ℝ) (hat : ∀ i, a i < t i)
    (below : ∀ i, (0,a i) ∈ H i.castSucc)
    (faceLower : ∀ i u, u ∈ D → (u,t i) ∈ H i.castSucc)
    (faceUpper : ∀ i u, u ∈ D → (u,t i) ∈ H i.succ)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : Set (Fin (r+2) → NonemptyCompacts (Space d × ℝ)),
      IsOpen U ∧ H ∈ U ∧
      ∀ S ∈ U, ∀ K, ConvexPartition K S →
        ∃ P : Fin (r+1) → Parameters d, ChainPartition K S ∧
          (∀ i, dist (P i) (0,t i) < η) ∧
          ∀ i, prefixCells S i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
            suffixCells S i.succ = K ∩ {x | height (P i) x.1 ≤ x.2} := by
  classical
  choose V hV memV charts using fun i => exists_graph_neighborhood_of_nonzero
    (H i.castSucc) (H i.succ) hD (hat i) (below i) (faceLower i) (faceUpper i) hη
  let W : Set (Fin (r+2) → NonemptyCompacts (Space d × ℝ)) :=
    ⋂ i : Fin (r+1), (fun S => (S i.castSucc,S i.succ)) ⁻¹' V i
  have openW : IsOpen W := isOpen_iInter_of_finite fun i =>
    (hV i).preimage ((continuous_apply i.castSucc).prodMk (continuous_apply i.succ))
  let U := W ∩ {S : Fin (r+2) → NonemptyCompacts (Space d × ℝ) |
    ∀ i j, i.val+1 < j.val → Disjoint (S i : Set (Space d × ℝ)) (S j)}
  have openU : IsOpen U := openW.inter (isOpen_productChainDisjoint d (r+2))
  have memU : H ∈ U := ⟨mem_iInter.mpr (fun i => memV i),nonadjacent⟩
  refine ⟨U,openU,memU,?_⟩
  intro S hS K part
  have chain : ChainPartition K S := ⟨part,hS.2⟩
  choose F c hne sep capLower capUpper using fun i : Fin (r+1) =>
    chain.exists_caps i.castSucc i.succ rfl
  have good (i : Fin (r+1)) := charts i (S i.castSucc,S i.succ)
    (mem_iInter.mp hS.1 i) (F i) (c i) (hne i) (sep i)
  let P : Fin (r+1) → Parameters d := fun i => graphParameters (F i) (c i)
  refine ⟨P,chain,fun i => (good i).2,?_⟩
  intro i
  constructor
  · rw [capLower i]
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,le_separator_iff_graph (F i) (c i) (good i).1]
    rfl
  · rw [capUpper i]
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,ge_separator_iff_graph (F i) (c i) (good i).1]
    rfl

/-- The two neighboring graph cuts recover an interior cell exactly, so
the compact-chart inverse applies to the actual body of that cell. -/
theorem cell_eq_clippedSlab_of_graph_caps {d r : ℕ}
    {K : Set (Space d × ℝ)} {S : Fin (r+2) → NonemptyCompacts (Space d × ℝ)}
    (part : ChainPartition K S) (P : Fin (r+1) → Parameters d)
    (caps : ∀ i, prefixCells S i.castSucc = K ∩ {x | x.2 ≤ height (P i) x.1} ∧
      suffixCells S i.succ = K ∩ {x | height (P i) x.1 ≤ x.2})
    (i j : Fin (r+1)) (adjacent : i.succ = j.castSucc) :
    (S i.succ : Set (Space d × ℝ)) = clippedSlab K (P i) (P j) := by
  calc
    (S i.succ : Set (Space d × ℝ)) = prefixCells S j.castSucc ∩ suffixCells S i.succ := by
      simpa only [adjacent] using part.cell_eq_caps i.succ
    _ = (K ∩ {x | x.2 ≤ height (P j) x.1}) ∩
        (K ∩ {x | height (P i) x.1 ≤ x.2}) := by rw [(caps j).1,(caps i).2]
    _ = clippedSlab K (P i) (P j) := by
      ext x
      simp only [clippedSlab,mem_inter_iff,mem_setOf_eq]
      tauto

/-- The interface readout is defined on the family of single bodies and
takes values in the original ambient slope/intercept parameter space. -/
def interfaceReadout {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi) :
    C(range (fun r : S => cutCompact compact r.val),Parameters d × Parameters d) := by
  let e := compact_parameter_homeomorph compact convex hD inner S hS bounds
  exact ⟨fun C => (e.symm C).val.val,
    continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous)⟩

@[simp] theorem interfaceReadout_apply {d : ℕ}
    {K : Set (Space d × ℝ)} (compact : IsCompact K) (convex : Convex ℝ K)
    {D : Set (Space d)} (hD : (0 : Space d) ∈ interior D) {lo hi : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K)
    (S : Set (FeasibleParameters K)) (hS : IsCompact S)
    (bounds : ∀ r ∈ S, ∀ u ∈ D,
      lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi)
    (r : S) : interfaceReadout compact convex hD inner S hS bounds
      ⟨cutCompact compact r.val,mem_range_self r⟩ = r.val.val := by
  let e := compact_parameter_homeomorph compact convex hD inner S hS bounds
  change (e.symm (e r)).val.val = r.val.val
  rw [e.symm_apply_apply]

/-- A closed ball of slopes and a closed interval of intercepts. -/
def parameterBox (d : ℕ) (ε lo hi : ℝ) : Set (Parameters d) :=
  closedBall 0 ε ×ˢ Icc lo hi

theorem compact_parameterBox (d : ℕ) (ε lo hi : ℝ) : IsCompact (parameterBox d ε lo hi) :=
  (isCompact_closedBall 0 ε).prod isCompact_Icc

theorem height_bounds_of_parameterBox {d : ℕ} {ε a b R : ℝ} (hε : 0 ≤ ε)
    {p : Parameters d} (hp : p ∈ parameterBox d ε a b) {u : Space d} (hu : ‖u‖ ≤ R) :
    a-ε*R ≤ height p u ∧ height p u ≤ b+ε*R := by
  have slope : ‖p.1‖ ≤ ε := by
    simpa only [mem_closedBall,dist_zero_right] using hp.1
  have valBound : |p.1 u| ≤ ε*R := by
    rw [← Real.norm_eq_abs]
    exact (p.1.le_opNorm u).trans (mul_le_mul slope hu (norm_nonneg _) hε)
  obtain ⟨vl,vu⟩ := abs_le.mp valBound
  obtain ⟨hl,hh⟩ := hp.2
  constructor <;> dsimp [height] <;> linarith

def admissibleBox {d : ℕ} (K : Set (Space d × ℝ)) (ε a b c e : ℝ) :
    Set (FeasibleParameters K) :=
  {r | r.val.1 ∈ parameterBox d ε a b ∧ r.val.2 ∈ parameterBox d ε c e}

private theorem feasible_of_parameter_boxes {d : ℕ} {K : Set (Space d × ℝ)}
    {D : Set (Space d)} (hD : (0 : Space d) ∈ D) {lo hi ε a b c e : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K) (hl : lo ≤ a) (gap : b < c) (hh : e ≤ hi)
    (r : Parameters d × Parameters d)
    (hr : r ∈ parameterBox d ε a b ×ˢ parameterBox d ε c e) :
    ∃ y ∈ K, height r.1 y.1 < y.2 ∧ y.2 < height r.2 y.1 := by
  have hp := hr.1.2
  have hq := hr.2.2
  have order : r.1.2 < r.2.2 := lt_of_le_of_lt hp.2 (gap.trans_le hq.1)
  refine ⟨(0,(r.1.2+r.2.2)/2),inner ⟨hD,⟨by dsimp; linarith [hp.1],
    by dsimp; linarith [hq.2]⟩⟩,?_,?_⟩
  · simpa only [height,map_zero,zero_add] using (show r.1.2 < (r.1.2+r.2.2)/2 by linarith)
  · simpa only [height,map_zero,zero_add] using (show (r.1.2+r.2.2)/2 < r.2.2 by linarith)

/-- Closed bounded parameter boxes strictly separated in intercept are a
genuinely compact family in the feasible parameter domain, despite that
domain itself being open. -/
theorem compact_admissibleBox {d : ℕ} {K : Set (Space d × ℝ)}
    {D : Set (Space d)} (hD : (0 : Space d) ∈ D) {lo hi ε a b c e : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K) (hl : lo ≤ a) (gap : b < c) (hh : e ≤ hi) :
    IsCompact (admissibleBox K ε a b c e) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have image : Subtype.val '' admissibleBox K ε a b c e =
      parameterBox d ε a b ×ˢ parameterBox d ε c e := by
    ext r
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact hr
    · intro hr
      exact ⟨⟨r,feasible_of_parameter_boxes hD inner hl gap hh r hr⟩,hr,rfl⟩
  rw [image]
  exact (compact_parameterBox d ε a b).prod (compact_parameterBox d ε c e)

/-- Explicit numerical margins give both compactness and every graph bound
needed by `interfaceReadout` for the whole closed parameter box. -/
theorem compact_admissibleBox_with_bounds {d : ℕ} {K : Set (Space d × ℝ)}
    {D : Set (Space d)} (hD : (0 : Space d) ∈ D) {lo hi ε a b c e R : ℝ}
    (inner : D ×ˢ Icc lo hi ⊆ K) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (bound : ∀ u ∈ D, ‖u‖ ≤ R) (gap : b < c)
    (lower : lo ≤ a-ε*R) (middle : b+ε*R ≤ c-ε*R) (upper : e+ε*R ≤ hi) :
    IsCompact (admissibleBox K ε a b c e) ∧
      ∀ r ∈ admissibleBox K ε a b c e, ∀ u ∈ D,
        lo ≤ height r.val.1 u ∧ height r.val.1 u ≤ height r.val.2 u ∧ height r.val.2 u ≤ hi := by
  have nonneg : 0 ≤ ε*R := mul_nonneg hε hR
  refine ⟨compact_admissibleBox hD inner (by linarith) gap (by linarith),?_⟩
  intro r hr u hu
  have hl := height_bounds_of_parameterBox hε hr.1 (bound u hu)
  have hh := height_bounds_of_parameterBox hε hr.2 (bound u hu)
  exact ⟨lower.trans hl.1,hl.2.trans (middle.trans hh.1),hh.2.trans upper⟩

end NRR.InterfaceChart
