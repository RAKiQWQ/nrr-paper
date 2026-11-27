import NRR.PrimePowerTopologyAssociatedEuler
import NRR.PrimePowerTopologyLocalDegree
import NRR.TopologyPort.RelativeSingularPrism

/-!
Actual local graph/fiber comparison for the associated configuration bundle.
The normal disk graph can be deformed through maps of pairs to the fixed
fiber disk, by contracting only its configuration coordinate.  All relative
maps are genuine singular-homology morphisms.  No global Thom isomorphism
or persistence of a local class after quotienting is asserted here.
-/

noncomputable section
open Set Topology Metric CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

instance mono_associatedPuncturedIncl (d n : ℕ) : Mono (associatedPuncturedIncl d n) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

/-- Projection of the ordered cover to its representation coordinate. -/
def associatedCoverVectorProjection (d n : ℕ) :
    TopCat.of (AssociatedCover d n) ⟶ TopCat.of (ReducedValues d n) :=
  TopCat.ofHom ⟨Prod.snd,continuous_snd⟩

def associatedPuncturedVectorProjection (d n : ℕ) :
    TopCat.of (AssociatedPuncturedCover d n) ⟶ TopCat.of {v : ReducedValues d n // v ≠ 0} :=
  TopCat.ofHom ⟨fun p => ⟨p.val.2,p.property⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

theorem associatedCoverVectorProjection_pair_comm (d n : ℕ) :
    associatedPuncturedIncl d n ≫ associatedCoverVectorProjection d n =
      associatedPuncturedVectorProjection d n ≫
        subIncl (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0} := rfl

def associatedCoverVectorProjectionRelative (R : Type) [Ring R] (k d n : ℕ) :
    Hrel R k (associatedPuncturedIncl d n) ⟶
      HrelSet R k (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0} :=
  HrelMap R k _ _ (associatedCoverVectorProjection_pair_comm d n)

def associatedCoverFiberMap {d n : ℕ} (x : Configuration d n) :
    TopCat.of (ReducedValues d n) ⟶ TopCat.of (AssociatedCover d n) :=
  TopCat.ofHom ⟨fun v => (x,v),continuous_const.prodMk continuous_id⟩

def associatedPuncturedFiberMap {d n : ℕ} (x : Configuration d n) :
    TopCat.of {v : ReducedValues d n // v ≠ 0} ⟶ TopCat.of (AssociatedPuncturedCover d n) :=
  TopCat.ofHom ⟨fun v => ⟨(x,v.val),v.property⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

theorem associatedCoverFiber_pair_comm {d n : ℕ} (x : Configuration d n) :
    subIncl (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0} ≫ associatedCoverFiberMap x =
      associatedPuncturedFiberMap x ≫ associatedPuncturedIncl d n := rfl

def associatedCoverFiberRelative {d n : ℕ} (R : Type) [Ring R] (k : ℕ)
    (x : Configuration d n) :
    HrelSet R k (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0} ⟶
      Hrel R k (associatedPuncturedIncl d n) :=
  HrelMap R k _ _ (associatedCoverFiber_pair_comm x)

/-- The ordinary-cover fiber map has a genuine left inverse on relative
homology.  Any loss after group quotienting is therefore a global issue. -/
theorem associatedCoverFiberRelative_projection {d n : ℕ}
    (R : Type) [Ring R] (k : ℕ) (x : Configuration d n) :
    associatedCoverFiberRelative R k x ≫ associatedCoverVectorProjectionRelative R k d n = 𝟙 _ := by
  unfold associatedCoverFiberRelative associatedCoverVectorProjectionRelative
  rw [HrelMap_comp]
  exact HrelMap_id R k (subIncl (Y := TopCat.of (ReducedValues d n)) {v | v ≠ 0})

def associatedPuncturedQuotient {d n : ℕ} :
    TopCat.of (AssociatedPuncturedCover d n) ⟶
      TopCat.of {z : ConfigurationAssociated d n // z ∉ associatedZeroLocus d n} :=
  TopCat.ofHom ⟨fun p => ⟨associatedQuotient p.val,fun h =>
    p.property ((associatedQuotient_mem_zeroLocus_iff p.val.1 p.val.2).mp h)⟩,
    (associatedQuotient.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem associatedQuotient_pair_comm (d n : ℕ) :
    associatedPuncturedIncl d n ≫ TopCat.ofHom associatedQuotient =
      associatedPuncturedQuotient ≫
        subIncl (Y := TopCat.of (ConfigurationAssociated d n)) (associatedZeroLocus d n)ᶜ := rfl

def associatedQuotientRelative (R : Type) [Ring R] (k d n : ℕ) :
    Hrel R k (associatedPuncturedIncl d n) ⟶
      HrelSet R k (Y := TopCat.of (ConfigurationAssociated d n)) (associatedZeroLocus d n)ᶜ :=
  HrelMap R k _ _ (associatedQuotient_pair_comm d n)

theorem associatedCoverFiberRelative_quotient {d n : ℕ}
    (R : Type) [Ring R] (k : ℕ) (x : Configuration d n) :
    associatedCoverFiberRelative R k x ≫ associatedQuotientRelative R k d n =
      associatedFiberRelative R k x := by
  unfold associatedCoverFiberRelative associatedQuotientRelative associatedFiberRelative
  rw [HrelMap_comp]

section NormalDisk
variable {d n : ℕ} {r : ℝ}

/-- The center as a point of the actual normal disk. -/
def associatedNormalDiskZero (hr : 0 < r) : closedBall (0 : ReducedValues d n) r :=
  ⟨0,by simpa using hr.le⟩

/-- A radial contraction of the actual closed normal disk. -/
def associatedNormalDiskContraction (hr : 0 < r) :
    ContinuousMap.Homotopy (ContinuousMap.id (closedBall (0 : ReducedValues d n) r))
      (ContinuousMap.const _ (associatedNormalDiskZero (d := d) (n := n) hr)) where
  toFun p := ⟨(p.1 : ℝ) • (0 : ReducedValues d n) + (1-(p.1 : ℝ)) • p.2.val,
    ((convex_closedBall (0 : ReducedValues d n) r).starConvex
      (associatedNormalDiskZero (d := d) (n := n) hr).property)
      p.2.property p.1.property.1 (sub_nonneg.mpr p.1.property.2) (add_sub_cancel _ _)⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left v := by apply Subtype.ext; simp
  map_one_left v := by apply Subtype.ext; simp [associatedNormalDiskZero]
/-- The graph of any continuously chosen configuration on a normal disk. -/
def associatedNormalDiskGraph
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    TopCat.of (closedBall (0 : ReducedValues d n) r) ⟶ TopCat.of (AssociatedCover d n) :=
  TopCat.ofHom ⟨fun v => (a v,v.val),a.continuous.prodMk continuous_subtype_val⟩

theorem associatedNormalSphere_ne_zero (hr : 0 < r)
    (v : sphere (0 : ReducedValues d n) r) : v.val ≠ 0 := by
  intro hv
  have hnorm := mem_sphere_zero_iff_norm.mp v.property
  rw [hv,norm_zero] at hnorm
  exact hr.ne' hnorm.symm

def associatedNormalSphereGraph (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    TopCat.of (sphere (0 : ReducedValues d n) r) ⟶ TopCat.of (AssociatedPuncturedCover d n) :=
  TopCat.ofHom ⟨fun v : sphere (0 : ReducedValues d n) r =>
    ⟨(a ⟨v.val,sphere_subset_closedBall v.property⟩,v.val),associatedNormalSphere_ne_zero hr v⟩,
    ((a.continuous.comp (continuous_subtype_val.subtype_mk _)).prodMk
      continuous_subtype_val).subtype_mk _⟩
def associatedNormalBoundaryIncl (d n : ℕ) (r : ℝ) :
    TopCat.of (sphere (0 : ReducedValues d n) r) ⟶
      TopCat.of (closedBall (0 : ReducedValues d n) r) :=
  TopCat.ofHom ⟨fun v => ⟨v.val,sphere_subset_closedBall v.property⟩,
    continuous_subtype_val.subtype_mk _⟩

instance mono_associatedNormalBoundaryIncl : Mono (associatedNormalBoundaryIncl d n r) := by
  rw [TopCat.mono_iff_injective]
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : closedBall (0 : ReducedValues d n) r => z.val) h

theorem associatedNormalGraph_pair_comm (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    associatedNormalBoundaryIncl d n r ≫ associatedNormalDiskGraph a =
      associatedNormalSphereGraph hr a ≫ associatedPuncturedIncl d n := rfl

def associatedNormalGraphRelative (hr : 0 < r) (R : Type) [Ring R] (k : ℕ)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    Hrel R k (associatedNormalBoundaryIncl d n r) ⟶ Hrel R k (associatedPuncturedIncl d n) :=
  HrelMap R k _ _ (associatedNormalGraph_pair_comm hr a)

/-- Contracting only the configuration coordinate preserves every nonzero
normal vector and hence gives a homotopy of the genuine relative pairs. -/
def associatedNormalGraphHomotopy (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    (associatedNormalDiskGraph a).hom.Homotopy
      (associatedNormalDiskGraph
        (ContinuousMap.const _ (a (associatedNormalDiskZero (d := d) (n := n) hr)))).hom where
  toFun p := (a (associatedNormalDiskContraction hr (p.1,p.2)),p.2.val)
  continuous_toFun := (a.continuous.comp (associatedNormalDiskContraction hr).continuous).prodMk
    (continuous_subtype_val.comp continuous_snd)
  map_zero_left v := by simp [associatedNormalDiskGraph]
  map_one_left v := by simp [associatedNormalDiskGraph]

def associatedNormalGraphBoundaryHomotopy (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    (associatedNormalSphereGraph hr a).hom.Homotopy
      (associatedNormalSphereGraph hr
        (ContinuousMap.const _ (a (associatedNormalDiskZero (d := d) (n := n) hr)))).hom where
  toFun p := ⟨associatedNormalGraphHomotopy hr a
    (p.1,⟨p.2.val,sphere_subset_closedBall p.2.property⟩),
      associatedNormalSphere_ne_zero hr p.2⟩
  continuous_toFun :=
    ((associatedNormalGraphHomotopy hr a).continuous.comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).subtype_mk _
  map_zero_left v := by
    apply Subtype.ext
    exact (associatedNormalGraphHomotopy hr a).map_zero_left
      ⟨v.val,sphere_subset_closedBall v.property⟩
  map_one_left v := by
    apply Subtype.ext
    exact (associatedNormalGraphHomotopy hr a).map_one_left
      ⟨v.val,sphere_subset_closedBall v.property⟩

def associatedNormalGraphPairHomotopy (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    ContinuousPairHomotopy (associatedNormalBoundaryIncl d n r) (associatedPuncturedIncl d n)
      (associatedNormalGraph_pair_comm hr a)
      (associatedNormalGraph_pair_comm hr
        (ContinuousMap.const _ (a (associatedNormalDiskZero (d := d) (n := n) hr)))) where
  amb := associatedNormalGraphHomotopy hr a
  sub := associatedNormalGraphBoundaryHomotopy hr a
  compat := by intro t v; rfl
/-- The actual normal graph and its fixed-fiber disk have identical
relative homology maps, with arbitrary coefficients. -/
theorem associatedNormalGraphRelative_eq_fixedFiber (hr : 0 < r)
    (R : Type) [Ring R] (k : ℕ)
    (a : C(closedBall (0 : ReducedValues d n) r,Configuration d n)) :
    associatedNormalGraphRelative hr R k a =
      associatedNormalGraphRelative hr R k
        (ContinuousMap.const _ (a ⟨0,by simpa using hr.le⟩)) :=
  HrelMap_eq_of_continuousPairHomotopy R _ _ _ _ (associatedNormalGraphPairHomotopy hr a) k

end NormalDisk

/-- The disk-graph comparison is the standard normal disk followed by the
actual inclusion of one ordered fiber. -/
theorem associatedNormalGraphRelative_eq_standardFiber
    (R : Type) [Ring R] (k : ℕ) {d n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues (d+1) n) r,Configuration (d+1) n)) :
    associatedNormalGraphRelative hr R k a =
      standardNormalDiskRelative (d := d) (n := n) R k hr ≫
        associatedCoverFiberRelative R k (a (associatedNormalDiskZero hr)) := by
  rw [associatedNormalGraphRelative_eq_fixedFiber hr R k a]
  unfold associatedNormalGraphRelative standardNormalDiskRelative associatedCoverFiberRelative reducedNonzeroSet
  rw [HrelMap_comp]
  rfl

/-- The same equality after passing to the genuine associated quotient. -/
theorem associatedNormalGraphRelative_quotient_eq_standardFiber
    (R : Type) [Ring R] (k : ℕ) {d n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r)
    (a : C(closedBall (0 : ReducedValues (d+1) n) r,Configuration (d+1) n)) :
    associatedNormalGraphRelative hr R k a ≫ associatedQuotientRelative R k (d+1) n =
      standardNormalDiskRelative (d := d) (n := n) R k hr ≫
        associatedFiberRelative R k (a (associatedNormalDiskZero hr)) := by
  rw [associatedNormalGraphRelative_eq_standardFiber R k hr a,Category.assoc,
    associatedCoverFiberRelative_quotient]

/-- On the actual canonical normal disk the graph vector is exactly v.
This connects the local pair comparison to the canonical zero set. -/
theorem canonicalNormalDisk_comp_coverGraph {d n : ℕ} [NeZero n]
    (u : CanonicalKernel d n) (r : ℝ)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    TopCat.ofHom (normalDiskConfiguration u r small) ≫ associatedCoverGraph (canonicalSection d n) =
      associatedNormalDiskGraph (normalDiskConfiguration u r small) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  apply Prod.ext
  · rfl
  · exact canonicalLinear_normalSlice u v.val

/-- The local canonical section in the associated quotient is the graph
map just compared with a genuine standard fiber disk. -/
theorem canonicalNormalDisk_comp_associatedSection {d n : ℕ} [NeZero n]
    (u : CanonicalKernel d n) (r : ℝ)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    TopCat.ofHom (normalDiskConfiguration u r small) ≫ TopCat.ofHom configurationQuotient ≫
        TopCat.ofHom (associatedSection (canonicalSection d n) canonicalSection_equivariant) =
      associatedNormalDiskGraph (normalDiskConfiguration u r small) ≫ TopCat.ofHom associatedQuotient := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  change associatedQuotient (normalDiskConfiguration u r small v,
    canonicalSection d n (normalDiskConfiguration u r small v)) =
      associatedQuotient (normalDiskConfiguration u r small v,v.val)
  rw [show canonicalSection d n (normalDiskConfiguration u r small v) = v.val from
    canonicalLinear_normalSlice u v.val]
end NRR.PrimePowerTopology
