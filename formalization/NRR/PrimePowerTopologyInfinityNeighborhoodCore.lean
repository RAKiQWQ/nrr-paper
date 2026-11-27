import NRR.PrimePowerTopologyGeneralCellAttachment

/-! Explicit pointed good neighborhoods and their propagation through the
radial collars of finite disk attachments. -/

noncomputable section
set_option maxHeartbeats 1600000
open Set Topology Metric
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- The precise local input for an ordinary suspension comparison: an open
neighborhood contracts to its marked point through maps fixing that point. -/
structure PointGoodNeighborhood (X : Type) [TopologicalSpace X] (p : X) where
  neighborhood : Set X
  isOpen : IsOpen neighborhood
  mem : p ∈ neighborhood
  contraction : (ContinuousMap.const neighborhood (⟨p, mem⟩ : neighborhood)).Homotopy
    (ContinuousMap.id neighborhood)
  fixed : ∀ t : unitInterval, contraction (t, ⟨p, mem⟩) = ⟨p, mem⟩

namespace PointGoodNeighborhood

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {p : X} (G : PointGoodNeighborhood X p)

def deformation : NeighborhoodDeformation ({p} : Set X) G.neighborhood where
  subset := by intro x hx; simpa only [mem_singleton_iff.mp hx] using G.mem
  retract := ContinuousMap.const _ ⟨p, mem_singleton p⟩
  retraction a := Subtype.ext (mem_singleton_iff.mp a.property).symm
  homotopy := G.contraction
  preserve t a := by
    have ha : a.val = p := mem_singleton_iff.mp a.property
    have he : (⟨a.val,by simpa only [ha] using G.mem⟩ : G.neighborhood) = ⟨p,G.mem⟩ :=
      Subtype.ext ha
    rw [he]
    exact congrArg Subtype.val (G.fixed t)

/-- Push a good neighborhood through an open embedding. -/
def map (f : C(X,Y)) (hf : IsOpenEmbedding f) : PointGoodNeighborhood Y (f p) := by
  let U : Set Y := f '' G.neighborhood
  let e : G.neighborhood ≃ₜ U :=
    ((hf.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph (f := fun x : G.neighborhood => f x.val)).trans
      (Homeomorph.setCongr (by
        ext y
        change (∃ x : G.neighborhood, f x.val = y) ↔ ∃ x, x ∈ G.neighborhood ∧ f x = y
        constructor
        · rintro ⟨x,rfl⟩; exact ⟨x.val,x.property,rfl⟩
        · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩))
  have he (x : G.neighborhood) : (e x).val = f x.val := rfl
  have hm : f p ∈ U := ⟨p,G.mem,rfl⟩
  have hp : e ⟨p,G.mem⟩ = ⟨f p,hm⟩ := Subtype.ext rfl
  refine {
    neighborhood := U
    isOpen := hf.isOpenMap _ G.isOpen
    mem := hm
    contraction := {
      toFun := fun z => e (G.contraction (z.1,e.symm z.2))
      continuous_toFun := e.continuous.comp (G.contraction.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      map_zero_left := by
        intro x
        change e (G.contraction (0,e.symm x)) = ⟨f p,hm⟩
        exact (congrArg e (G.contraction.apply_zero (e.symm x))).trans hp
      map_one_left := by intro x; simp }
    fixed := ?_ }
  intro t
  change e (G.contraction (t,e.symm ⟨f p,hm⟩)) = ⟨f p,hm⟩
  rw [← hp, e.symm_apply_apply, G.fixed]

def homeomorph (e : X ≃ₜ Y) : PointGoodNeighborhood Y (e p) :=
  G.map ⟨e,e.continuous⟩ e.isOpenEmbedding

/-- Pull a pointed contraction back through a collar retraction. The
retraction is constant along the collar motion, so its inverse image of
the smaller neighborhood remains invariant throughout the homotopy. -/
def pullback {p : Y} (G : PointGoodNeighborhood Y p)
    (i : C(Y,X)) (r : C(X,Y)) (hr : ∀ y, r (i y) = y)
    (H : (i.comp r).Homotopy (ContinuousMap.id X))
    (hH : ∀ t x, r (H (t,x)) = r x)
    (hfixed : ∀ t y, H (t,i y) = i y) : PointGoodNeighborhood X (i p) := by
  let U : Set X := r ⁻¹' G.neighborhood
  have hm : i p ∈ U := by change r (i p) ∈ G.neighborhood; rw [hr]; exact G.mem
  let j : C(G.neighborhood,U) := ⟨fun y => ⟨i y.val,by
    change r (i y.val) ∈ G.neighborhood; rw [hr]; exact y.property⟩,
    by apply Continuous.subtype_mk; exact i.continuous.comp continuous_subtype_val⟩
  let s : C(U,G.neighborhood) := ⟨fun x => ⟨r x.val,x.property⟩,
    (r.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let v : C(U,U) := j.comp s
  let K : (ContinuousMap.const U (⟨i p,hm⟩ : U)).Homotopy v := {
    toFun := fun z => j (G.contraction (z.1,s z.2))
    continuous_toFun := j.continuous.comp (G.contraction.continuous.comp
      (continuous_fst.prodMk (s.continuous.comp continuous_snd)))
    map_zero_left := by intro x; apply Subtype.ext; simp [j]
    map_one_left := by intro x; simp [v] }
  let L : v.Homotopy (ContinuousMap.id U) := {
    toFun := fun z => ⟨H (z.1,z.2.val),by
      change r (H (z.1,z.2.val)) ∈ G.neighborhood; rw [hH]; exact z.2.property⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact H.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    map_zero_left := by intro x; apply Subtype.ext; exact H.map_zero_left x.val
    map_one_left := by intro x; apply Subtype.ext; exact H.map_one_left x.val }
  refine ⟨U,G.isOpen.preimage r.continuous,hm,K.trans L,?_⟩
  intro t
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · apply Subtype.ext
    change i (G.contraction (_,s ⟨i p,hm⟩)).val = i p
    have hs : s ⟨i p,hm⟩ = ⟨p,G.mem⟩ := Subtype.ext (hr p)
    rw [hs,G.fixed]
  · apply Subtype.ext
    exact hfixed _ p

end PointGoodNeighborhood

namespace InfinityCollar

variable {ι V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
  [Finite ι] {A : Set X} [CompactSpace A]
  (P : FiniteCellAttachment ι V X A)

theorem annularRadial_zero_after (t : unitInterval) (q : CellAnnulus V) :
    annularRadial (0,annularRadial (t,q)) = annularRadial (0,q) := by
  apply Subtype.ext
  apply Subtype.ext
  have hq : 0 < ‖q.val.val‖ := lt_trans (by norm_num) q.property
  have ht : 0 ≤ (1-(t : ℝ))/‖q.val.val‖+(t : ℝ) :=
    add_nonneg (div_nonneg (sub_nonneg.mpr t.property.2) hq.le) t.property.1
  have hn : 0 < ‖annularRadialValue t q‖ :=
    lt_trans (by norm_num) (annularRadial (t,q)).property
  change annularRadialValue 0 (annularRadial (t,q)) = annularRadialValue 0 q
  simp only [annularRadialValue, Set.Icc.coe_zero, sub_zero, zero_add,
    annularRadial, ContinuousMap.coe_mk, smul_smul]
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  have hc : (1-(t : ℝ))/‖q.val.val‖+(t : ℝ) ≠ 0 := by
    intro hc
    apply ne_of_gt hn
    simp only [annularRadialValue,hc,zero_smul,norm_zero]
  have hn' : 1-(t : ℝ)+(t : ℝ)*‖q.val.val‖ ≠ 0 := by
    rw [norm_annularRadialValue] at hn
    exact hn.ne'
  field_simp [hn']
  <;> ring

theorem homotopy_fixed (t : unitInterval) (a : A) :
    P.neighborhoodHomotopy (t,P.neighborhoodProjection (Sum.inl a)) =
      P.neighborhoodProjection (Sum.inl a) := by
  rw [P.neighborhoodHomotopy_lift]
  rfl

theorem homotopy_zero_after (t : unitInterval) (x : P.neighborhood) :
    P.neighborhoodHomotopy (0,P.neighborhoodHomotopy (t,x)) =
      P.neighborhoodHomotopy (0,x) := by
  obtain ⟨a,rfl⟩ := P.quotient_neighborhoodProjection.surjective x
  rw [P.neighborhoodHomotopy_lift]
  rcases a with a | ⟨i,q⟩
  · rfl
  · change P.neighborhoodHomotopy
      (0,P.neighborhoodProjection (Sum.inr ⟨i,annularRadial (t,q)⟩)) = _
    rw [P.neighborhoodHomotopy_lift,P.neighborhoodHomotopy_lift]
    apply Subtype.ext
    change P.characteristic i (annularRadial (0,annularRadial (t,q))).val =
      P.characteristic i (annularRadial (0,q)).val
    rw [annularRadial_zero_after]

/-- A good neighborhood in the lower member extends through an actual
finite disk attachment by composing its contraction with the radial collar. -/
def extend {p : A} (G : PointGoodNeighborhood A p) : PointGoodNeighborhood X p.val := by
  let H := P.neighborhoodDeformation
  let G' : PointGoodNeighborhood P.neighborhood (H.inclusion p) :=
    G.pullback H.inclusion H.retract H.retraction H.homotopy
      (by
        intro t x
        apply Subtype.ext
        change (P.neighborhoodHomotopy (0,P.neighborhoodHomotopy (t,x))).val =
          (P.neighborhoodHomotopy (0,x)).val
        exact congrArg Subtype.val (homotopy_zero_after P t x))
      (by intro t a; exact homotopy_fixed P t a)
  exact G'.map ⟨Subtype.val,continuous_subtype_val⟩ P.isOpen_neighborhood.isOpenEmbedding_subtypeVal

end InfinityCollar
end NRR.PrimePowerTopology
