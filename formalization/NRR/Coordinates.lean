import NRR.ConvexLimits
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-! Transport between Euclidean and horizontal-height coordinates, including
the Hausdorff topology on single blocks and convex body partitions. -/

noncomputable section
open Set Topology TopologicalSpace Metric MeasureTheory
open scoped NNReal

namespace NRR.Coordinates

/-- Evaluation identifies the one-dimensional Euclidean space with the reals. -/
def spaceOne : Space 1 ≃L[ℝ] ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ _).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- The horizontal coordinates and final height coordinate.  The product
norm need not be Euclidean: only a continuous linear equivalence is used. -/
def horizontalHeight (d : ℕ) : Space (d+1) ≃L[ℝ] Space d × ℝ :=
  EuclideanSpace.finAddEquivProd.trans
    ((ContinuousLinearEquiv.refl ℝ (Space d)).prodCongr spaceOne)

section Compacts

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- Continuous image of a nonempty compact set. -/
def compactImage (f : E → F) (hf : Continuous f) (C : NonemptyCompacts E) :
    NonemptyCompacts F :=
  { carrier := f '' (C : Set E)
    isCompact' := C.isCompact.image hf
    nonempty' := C.nonempty.image f }

@[simp] theorem coe_compactImage (f : E → F) (hf : Continuous f)
    (C : NonemptyCompacts E) : (compactImage f hf C : Set F) = f '' (C : Set E) := rfl

/-- A Lipschitz map acts with the same Lipschitz bound on the Hausdorff
spaces of nonempty compact sets. -/
theorem compactImage_lipschitz {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (compactImage f hf.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro S T
  have pointNear (A B : NonemptyCompacts E) (x : E) (hx : x ∈ A) :
      ∃ y ∈ (B : Set E),dist (f x) (f y) ≤ (K:ℝ)*dist A B := by
    obtain ⟨y,hy,hxy⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty x
    refine ⟨y,hy,(hf.dist_le_mul x y).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [← hxy]
    exact infDist_le_hausdorffDist_of_mem hx (edist_ne_top A B)
  change hausdorffDist (f '' (S : Set E)) (f '' (T : Set E)) ≤ _
  apply hausdorffDist_le_of_mem_dist (mul_nonneg K.coe_nonneg dist_nonneg)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := pointNear S T x hx
    exact ⟨f y,mem_image_of_mem f hy,hxy⟩
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨x,hx,hyx⟩ := pointNear T S y hy
    exact ⟨f x,mem_image_of_mem f hx,by simpa only [dist_comm T S] using hyx⟩

end Compacts

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Linear coordinate changes induce homeomorphisms for the Hausdorff
topology on nonempty compact sets. -/
def compactsHomeomorph (e : E ≃L[ℝ] F) : NonemptyCompacts E ≃ₜ NonemptyCompacts F where
  toFun := compactImage e e.continuous
  invFun := compactImage e.symm e.symm.continuous
  left_inv C := by
    apply NonemptyCompacts.ext
    change e.symm '' (e '' (C : Set E)) = (C : Set E)
    simp only [image_image,e.symm_apply_apply,image_id']
  right_inv C := by
    apply NonemptyCompacts.ext
    change e '' (e.symm '' (C : Set F)) = (C : Set F)
    simp only [image_image,e.apply_symm_apply,image_id']
  continuous_toFun := (compactImage_lipschitz e.lipschitz).continuous
  continuous_invFun := (compactImage_lipschitz e.symm.lipschitz).continuous

theorem convex_image_iff (e : E ≃L[ℝ] F) (C : Set E) :
    Convex ℝ C ↔ Convex ℝ (e '' C) := by
  refine ⟨fun h => h.linear_image e.toLinearMap,fun h => ?_⟩
  have hi := h.linear_image e.symm.toLinearMap
  simpa only [LinearEquiv.coe_coe,ContinuousLinearEquiv.coe_toLinearEquiv,
    image_image,Function.comp_def,e.symm_apply_apply,image_id'] using hi

/-- The same coordinate change on all nonempty compact convex sets, including
lower-dimensional ones. -/
def convexCompactsHomeomorph (e : E ≃L[ℝ] F) :
    ConvexLimits.ConvexCompact E ≃ₜ ConvexLimits.ConvexCompact F :=
  (compactsHomeomorph e).subtype (fun C => convex_image_iff e (C : Set E))

@[simp] theorem points_convexCompactsHomeomorph (e : E ≃L[ℝ] F)
    (C : ConvexLimits.ConvexCompact E) :
    ConvexLimits.points (convexCompactsHomeomorph e C) = e '' ConvexLimits.points C := rfl

/-- Full-dimensional compact convex bodies in an arbitrary real normed
space.  For `E = Space d` this is definitionally the original `NRR.Body d`. -/
abbrev ConvexBody (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {C : NonemptyCompacts E // Convex ℝ (C : Set E) ∧ (interior (C : Set E)).Nonempty}

abbrev bodyPoints (C : ConvexBody E) : Set E := C.val

theorem interior_image_nonempty_iff (e : E ≃L[ℝ] F) (C : Set E) :
    (interior C).Nonempty ↔ (interior (e '' C)).Nonempty := by
  have hi : e '' interior C = interior (e '' C) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using e.toHomeomorph.image_interior C
  rw [← hi]
  exact image_nonempty.symm

/-- Full dimensionality, like convexity, is preserved by linear coordinate
changes.  This transports the actual bodies, not just their carriers. -/
def bodiesHomeomorph (e : E ≃L[ℝ] F) : ConvexBody E ≃ₜ ConvexBody F :=
  (compactsHomeomorph e).subtype (fun C =>
    (convex_image_iff e (C : Set E)).and (interior_image_nonempty_iff e (C : Set E)))

@[simp] theorem bodyPoints_bodiesHomeomorph (e : E ≃L[ℝ] F) (C : ConvexBody E) :
    bodyPoints (bodiesHomeomorph e C) = e '' bodyPoints C := rfl

@[simp] theorem bodiesHomeomorph_symm (e : E ≃L[ℝ] F) :
    bodiesHomeomorph e.symm = (bodiesHomeomorph e).symm := rfl

@[simp] theorem convexCompactsHomeomorph_symm (e : E ≃L[ℝ] F) :
    convexCompactsHomeomorph e.symm = (convexCompactsHomeomorph e).symm := rfl

/-- View a full-dimensional body as a possibly degenerate compact convex set. -/
def bodyToConvexCompact (C : ConvexBody E) : ConvexLimits.ConvexCompact E := ⟨C.val,C.property.1⟩

@[simp] theorem bodyToConvexCompact_map (e : E ≃L[ℝ] F) (C : ConvexBody E) :
    bodyToConvexCompact (bodiesHomeomorph e C) =
      convexCompactsHomeomorph e (bodyToConvexCompact C) := rfl

/-- The body-partition structure in coordinates that need not carry an inner
product.  It specializes exactly to the two original partition conditions. -/
structure Partition {ι : Type*} (K : ConvexBody E) (S : ι → ConvexBody E) : Prop where
  covers : (⋃ i,bodyPoints (S i)) = bodyPoints K
  disjoint : Pairwise fun i j => Disjoint (interior (bodyPoints (S i)))
    (interior (bodyPoints (S j)))

theorem Partition.map {ι : Type*} {K : ConvexBody E} {S : ι → ConvexBody E}
    (hp : Partition K S) (e : E ≃L[ℝ] F) :
    Partition (bodiesHomeomorph e K) (fun i => bodiesHomeomorph e (S i)) := by
  constructor
  · simp only [bodyPoints_bodiesHomeomorph,← image_iUnion,hp.covers]
  · intro i j hij
    have hi (C : Set E) : interior (e '' C) = e '' interior C := by
      simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
        (e.toHomeomorph.image_interior C).symm
    rw [bodyPoints_bodiesHomeomorph,bodyPoints_bodiesHomeomorph,hi,hi]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    have hxy : y = x := e.injective heq
    subst y
    exact Set.disjoint_left.mp (hp.disjoint hij) hx hy

theorem partition_map_iff {ι : Type*} (e : E ≃L[ℝ] F) (K : ConvexBody E)
    (S : ι → ConvexBody E) :
    Partition (bodiesHomeomorph e K) (fun i => bodiesHomeomorph e (S i)) ↔ Partition K S := by
  refine ⟨fun hp => ?_,fun hp => hp.map e⟩
  simpa only [bodiesHomeomorph_symm,Homeomorph.symm_apply_apply] using hp.map e.symm

end Linear

theorem bodyPartition_iff_partition {d n : ℕ} (K : Body d) (S : Fin n → Body d) :
    BodyPartition K S ↔ Partition K S :=
  ⟨fun hp => ⟨hp.covers,hp.disjoint⟩,fun hp => ⟨hp.covers,hp.disjoint⟩⟩

section Measure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Coordinate pushforward retains the mass of every compact convex body. -/
theorem map_body_mass (e : E ≃L[ℝ] F) (μ : Measure E) (C : ConvexBody E) :
    (μ.map e) (bodyPoints (bodiesHomeomorph e C)) = μ (bodyPoints C) := by
  rw [bodyPoints_bodiesHomeomorph,
    Measure.map_apply e.continuous.measurable
      (C.val.isCompact.image e.continuous).isClosed.measurableSet,
    e.injective.preimage_image]

theorem equalMass_map_iff {ι : Type*} (e : E ≃L[ℝ] F) (μ : Measure E)
    (S : ι → ConvexBody E) :
    (∀ i j,(μ.map e) (bodyPoints (bodiesHomeomorph e (S i))) =
      (μ.map e) (bodyPoints (bodiesHomeomorph e (S j)))) ↔
      (∀ i j,μ (bodyPoints (S i)) = μ (bodyPoints (S j))) := by
  simp only [map_body_mass]

/-- Probability normalization is retained without any determinant factor. -/
theorem map_isProbabilityMeasure (e : E ≃L[ℝ] F) (μ : Measure E)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.map e) :=
  Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable

/-- Absolute continuity is invariant under linear coordinate changes.  The
source and target reference measures may be any additive Haar measures,
which covers both Euclidean volume and product volume. -/
theorem map_absolutelyContinuous_haar [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F) (μ ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (κ : Measure F) [Measure.IsAddHaarMeasure κ] (hμ : μ ≪ ν) : μ.map e ≪ κ := by
  have hm : μ.map e ≪ ν.map e := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
      e.toHomeomorph.measurableEmbedding.absolutelyContinuous_map hμ
  exact hm.trans (Measure.absolutelyContinuous_isAddHaarMeasure (ν.map e) κ)

/-- Pull a continuous single-block characteristic back through the actual
Hausdorff homeomorphism of all compact convex sets. -/
def pullCharacteristic (e : E ≃L[ℝ] F)
    (φ : C(ConvexLimits.ConvexCompact F,ℝ)) : C(ConvexLimits.ConvexCompact E,ℝ) :=
  φ.comp ⟨convexCompactsHomeomorph e,(convexCompactsHomeomorph e).continuous⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
@[simp] theorem pullCharacteristic_apply (e : E ≃L[ℝ] F)
    (φ : C(ConvexLimits.ConvexCompact F,ℝ)) (C : ConvexBody E) :
    pullCharacteristic e φ (bodyToConvexCompact C) =
      φ (bodyToConvexCompact (bodiesHomeomorph e C)) := rfl

/-- A counterexample in product coordinates transports back to the original
body-partition statement, including the prescribed measure and its order of
quantification. -/
theorem body_counterexample_pullback {d n q : ℕ}
    (e : Space d ≃L[ℝ] F) (K : Body d) (μ : Measure (Space d))
    (φ : Fin q → C(ConvexLimits.ConvexCompact F,ℝ))
    (reject : ∀ S : Fin n → ConvexBody F,Partition (bodiesHomeomorph e K) S →
      (∀ i j,(μ.map e) (bodyPoints (S i)) = (μ.map e) (bodyPoints (S j))) →
      ∃ k i j,φ k (bodyToConvexCompact (S i)) ≠ φ k (bodyToConvexCompact (S j))) :
    ∃ ψ : Fin q → C(CompactConvex d,ℝ),∀ S : Fin n → Body d,
      BodyPartition K S → EqualMass μ S →
      ∃ k i j,ψ k (S i).toCompactConvex ≠ ψ k (S j).toCompactConvex := by
  refine ⟨fun k => pullCharacteristic e (φ k),fun S hp hm => ?_⟩
  have hp' := ((bodyPartition_iff_partition K S).mp hp).map e
  have hm' := (equalMass_map_iff e μ S).mpr hm
  obtain ⟨k,i,j,hij⟩ := reject (fun i => bodiesHomeomorph e (S i)) hp' hm'
  exact ⟨k,i,j,hij⟩

end Measure

namespace Affine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous linear part of an affine coordinate equivalence. -/
def linearPart (e : E ≃ᴬ[ℝ] F) : E ≃L[ℝ] F where
  toLinearEquiv := e.toAffineEquiv.linear
  continuous_toFun := e.toContinuousAffineMap.contLinear.continuous
  continuous_invFun := e.symm.toContinuousAffineMap.contLinear.continuous

theorem decomp (e : E ≃ᴬ[ℝ] F) (x : E) : e x = linearPart e x + e 0 := by
  simpa only [vadd_eq_add,add_zero] using e.toAffineEquiv.map_vadd (0 : E) x

theorem lipschitz (e : E ≃ᴬ[ℝ] F) :
    LipschitzWith ‖(linearPart e : E →L[ℝ] F)‖₊ e := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [decomp e x,decomp e y,dist_add_right]
  exact (linearPart e).lipschitz.dist_le_mul x y

/-- Affine coordinate changes act continuously on the Hausdorff space of
compact sets, with no assumption of an isometric product norm. -/
def compactsHomeomorph (e : E ≃ᴬ[ℝ] F) : NonemptyCompacts E ≃ₜ NonemptyCompacts F where
  toFun := compactImage e e.continuous
  invFun := compactImage e.symm e.symm.continuous
  left_inv C := by
    apply NonemptyCompacts.ext
    change e.symm '' (e '' (C : Set E)) = (C : Set E)
    simp only [image_image,e.symm_apply_apply,image_id']
  right_inv C := by
    apply NonemptyCompacts.ext
    change e '' (e.symm '' (C : Set F)) = (C : Set F)
    simp only [image_image,e.apply_symm_apply,image_id']
  continuous_toFun := (compactImage_lipschitz (lipschitz e)).continuous
  continuous_invFun := (compactImage_lipschitz (lipschitz e.symm)).continuous

theorem convex_image_iff (e : E ≃ᴬ[ℝ] F) (C : Set E) :
    Convex ℝ C ↔ Convex ℝ (e '' C) := by
  refine ⟨fun h => h.affine_image e.toAffineEquiv.toAffineMap,fun h => ?_⟩
  have hi := h.affine_image e.symm.toAffineEquiv.toAffineMap
  simpa only [AffineEquiv.coe_toAffineMap,ContinuousAffineEquiv.coe_coe,
    image_image,e.symm_apply_apply,image_id'] using hi

def convexCompactsHomeomorph (e : E ≃ᴬ[ℝ] F) :
    ConvexLimits.ConvexCompact E ≃ₜ ConvexLimits.ConvexCompact F :=
  (compactsHomeomorph e).subtype (fun C => convex_image_iff e (C : Set E))

@[simp] theorem points_convexCompactsHomeomorph (e : E ≃ᴬ[ℝ] F)
    (C : ConvexLimits.ConvexCompact E) :
    ConvexLimits.points (convexCompactsHomeomorph e C) = e '' ConvexLimits.points C := rfl

theorem interior_image (e : E ≃ᴬ[ℝ] F) (C : Set E) :
    e '' interior C = interior (e '' C) := e.toHomeomorph.image_interior C

def bodiesHomeomorph (e : E ≃ᴬ[ℝ] F) : ConvexBody E ≃ₜ ConvexBody F :=
  (compactsHomeomorph e).subtype (fun C =>
    (convex_image_iff e (C : Set E)).and (by
      change (interior (C : Set E)).Nonempty ↔ (interior (e '' (C : Set E))).Nonempty
      rw [← interior_image e]
      exact image_nonempty.symm))

@[simp] theorem bodyPoints_bodiesHomeomorph (e : E ≃ᴬ[ℝ] F) (C : ConvexBody E) :
    bodyPoints (bodiesHomeomorph e C) = e '' bodyPoints C := rfl

@[simp] theorem bodiesHomeomorph_symm (e : E ≃ᴬ[ℝ] F) :
    bodiesHomeomorph e.symm = (bodiesHomeomorph e).symm := rfl

@[simp] theorem convexCompactsHomeomorph_symm (e : E ≃ᴬ[ℝ] F) :
    convexCompactsHomeomorph e.symm = (convexCompactsHomeomorph e).symm := rfl

@[simp] theorem bodyToConvexCompact_map (e : E ≃ᴬ[ℝ] F) (C : ConvexBody E) :
    bodyToConvexCompact (bodiesHomeomorph e C) =
      convexCompactsHomeomorph e (bodyToConvexCompact C) := rfl

theorem partition_map {ι : Type*} {K : ConvexBody E} {S : ι → ConvexBody E}
    (hp : Partition K S) (e : E ≃ᴬ[ℝ] F) :
    Partition (bodiesHomeomorph e K) (fun i => bodiesHomeomorph e (S i)) := by
  constructor
  · simp only [bodyPoints_bodiesHomeomorph,← image_iUnion,hp.covers]
  · intro i j hij
    rw [bodyPoints_bodiesHomeomorph,bodyPoints_bodiesHomeomorph,
      ← interior_image,← interior_image]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    have hxy : y = x := e.injective heq
    subst y
    exact Set.disjoint_left.mp (hp.disjoint hij) hx hy

theorem partition_map_iff {ι : Type*} (e : E ≃ᴬ[ℝ] F) (K : ConvexBody E)
    (S : ι → ConvexBody E) :
    Partition (bodiesHomeomorph e K) (fun i => bodiesHomeomorph e (S i)) ↔ Partition K S := by
  refine ⟨fun hp => ?_,fun hp => partition_map hp e⟩
  simpa only [bodiesHomeomorph_symm,Homeomorph.symm_apply_apply] using partition_map hp e.symm

section Measure

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

theorem map_body_mass (e : E ≃ᴬ[ℝ] F) (μ : Measure E) (C : ConvexBody E) :
    (μ.map e) (bodyPoints (bodiesHomeomorph e C)) = μ (bodyPoints C) := by
  rw [bodyPoints_bodiesHomeomorph,
    Measure.map_apply e.continuous.measurable
      (C.val.isCompact.image e.continuous).isClosed.measurableSet,
    e.injective.preimage_image]

theorem equalMass_map_iff {ι : Type*} (e : E ≃ᴬ[ℝ] F) (μ : Measure E)
    (S : ι → ConvexBody E) :
    (∀ i j,(μ.map e) (bodyPoints (bodiesHomeomorph e (S i))) =
      (μ.map e) (bodyPoints (bodiesHomeomorph e (S j)))) ↔
      (∀ i j,μ (bodyPoints (S i)) = μ (bodyPoints (S j))) := by
  simp only [map_body_mass]

theorem map_isProbabilityMeasure (e : E ≃ᴬ[ℝ] F) (μ : Measure E)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.map e) :=
  Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable

/-- Translating the image of a Haar measure introduces no further factor;
the affine pushforward is the same Haar measure as the linear pushforward. -/
theorem map_haar_eq_linearPart (e : E ≃ᴬ[ℝ] F) (ν : Measure E)
    [Measure.IsAddHaarMeasure ν] : ν.map e = ν.map (linearPart e) := by
  have he : (e : E → F) = (fun y => y+e 0) ∘ linearPart e := funext (decomp e)
  have ht : Measurable (fun y : F => y+e 0) := (continuous_id.add continuous_const).measurable
  rw [he,← Measure.map_map ht
    (linearPart e).continuous.measurable,map_add_right_eq_self]

theorem map_absolutelyContinuous_haar [FiniteDimensional ℝ F]
    (e : E ≃ᴬ[ℝ] F) (μ ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (κ : Measure F) [Measure.IsAddHaarMeasure κ] (hμ : μ ≪ ν) : μ.map e ≪ κ := by
  have hm : μ.map e ≪ ν.map e := e.toHomeomorph.measurableEmbedding.absolutelyContinuous_map hμ
  rw [map_haar_eq_linearPart e ν] at hm
  exact hm.trans (Measure.absolutelyContinuous_isAddHaarMeasure (ν.map (linearPart e)) κ)

end Measure

def pullCharacteristic (e : E ≃ᴬ[ℝ] F)
    (φ : C(ConvexLimits.ConvexCompact F,ℝ)) : C(ConvexLimits.ConvexCompact E,ℝ) :=
  φ.comp ⟨convexCompactsHomeomorph e,(convexCompactsHomeomorph e).continuous⟩

@[simp] theorem pullCharacteristic_apply (e : E ≃ᴬ[ℝ] F)
    (φ : C(ConvexLimits.ConvexCompact F,ℝ)) (C : ConvexBody E) :
    pullCharacteristic e φ (bodyToConvexCompact C) =
      φ (bodyToConvexCompact (bodiesHomeomorph e C)) := rfl

theorem body_counterexample_pullback {d n q : ℕ} [MeasurableSpace F] [BorelSpace F]
    (e : Space d ≃ᴬ[ℝ] F) (K : Body d) (μ : Measure (Space d))
    (φ : Fin q → C(ConvexLimits.ConvexCompact F,ℝ))
    (reject : ∀ S : Fin n → ConvexBody F,Partition (bodiesHomeomorph e K) S →
      (∀ i j,(μ.map e) (bodyPoints (S i)) = (μ.map e) (bodyPoints (S j))) →
      ∃ k i j,φ k (bodyToConvexCompact (S i)) ≠ φ k (bodyToConvexCompact (S j))) :
    ∃ ψ : Fin q → C(CompactConvex d,ℝ),∀ S : Fin n → Body d,
      BodyPartition K S → EqualMass μ S →
      ∃ k i j,ψ k (S i).toCompactConvex ≠ ψ k (S j).toCompactConvex := by
  refine ⟨fun k => pullCharacteristic e (φ k),fun S hp hm => ?_⟩
  have hp' := partition_map ((bodyPartition_iff_partition K S).mp hp) e
  have hm' := (equalMass_map_iff e μ S).mpr hm
  obtain ⟨k,i,j,hij⟩ := reject (fun i => bodiesHomeomorph e (S i)) hp' hm'
  exact ⟨k,i,j,hij⟩

end Affine

end NRR.Coordinates
