import NRR.PrimePowerTopologyNormalSlice
import NRR.SingularHomologyPair
import Mathlib.Analysis.Convex.Contractible

/-! The real canonical transverse section acts as the identity on normal
sphere homology, with arbitrary ring coefficients. This is the local
normalization input; no global Euler-class survival theorem is asserted. -/

noncomputable section
open Set Topology Metric CategoryTheory
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

def normalDiskConfiguration (u : CanonicalKernel d n) (r : ℝ)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    C(closedBall (0 : ReducedValues (d+1) n) r,Configuration (d+1) n) :=
  (normalFiberConfiguration u).comp
    ⟨fun v => ⟨v.val,small v.property⟩,continuous_subtype_val.subtype_mk _⟩

def normalSphereConfiguration (u : CanonicalKernel d n) (r : ℝ)
    (small : sphere (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    C(sphere (0 : ReducedValues (d+1) n) r,Configuration (d+1) n) :=
  (normalFiberConfiguration u).comp
    ⟨fun v => ⟨v.val,small v.property⟩,continuous_subtype_val.subtype_mk _⟩

@[simp] theorem canonicalSection_normalSphereConfiguration (u : CanonicalKernel d n)
    (r : ℝ) (small : sphere (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (v : sphere (0 : ReducedValues (d+1) n) r) :
    canonicalSection d n (normalSphereConfiguration u r small v) = v.val :=
  canonicalLinear_normalSlice u v.val

/-- There is a positive normal sphere lying entirely in the genuine
configuration space on which the canonical section is exactly the usual
inclusion of that sphere into the reduced representation. -/
theorem exists_actual_normalSphere (u : CanonicalKernel d n)
    (distinct : Function.Injective u.val) :
    ∃ r : ℝ,0 < r ∧ ∃ f : C(sphere (0 : ReducedValues (d+1) n) r,Configuration (d+1) n),
      ∀ v,canonicalSection d n (f v) = v.val := by
  obtain ⟨r,hr,small⟩ := exists_normalFiber_closedBall u distinct
  let boundary : sphere (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u :=
    sphere_subset_closedBall.trans small
  exact ⟨r,hr,normalSphereConfiguration u r boundary,
    canonicalSection_normalSphereConfiguration u r boundary⟩

/-- The normal-sphere inclusion really bounds its normal disk inside the
configuration space. Composing it with a globally defined sphere-valued
section therefore yields an actual nullhomotopy. -/
theorem normalSphereConfiguration_nullhomotopic (u : CanonicalKernel d n)
    (r : ℝ) (hr : 0 ≤ r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u) :
    (normalSphereConfiguration u r (sphere_subset_closedBall.trans small)).Nullhomotopic := by
  let D := closedBall (0 : ReducedValues (d+1) n) r
  letI : ContractibleSpace D := (convex_closedBall (0 : ReducedValues (d+1) n) r).contractibleSpace
    ⟨0,mem_closedBall_self hr⟩
  let inc : C(sphere (0 : ReducedValues (d+1) n) r,D) :=
    ⟨fun v => ⟨v.val,sphere_subset_closedBall v.property⟩,continuous_subtype_val.subtype_mk _⟩
  have null : (normalDiskConfiguration u r small).Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      (id_nullhomotopic D).comp_right (normalDiskConfiguration u r small)
  exact null.comp_left inc

theorem globally_defined_test_normalSphere_nullhomotopic {Y : Type*} [TopologicalSpace Y]
    (u : CanonicalKernel d n) (r : ℝ) (hr : 0 ≤ r)
    (small : closedBall (0 : ReducedValues (d+1) n) r ⊆ canonicalNormalFiberDomain u)
    (g : C(Configuration (d+1) n,Y)) :
    (g.comp (normalSphereConfiguration u r (sphere_subset_closedBall.trans small))).Nullhomotopic :=
  (normalSphereConfiguration_nullhomotopic u r hr small).comp_right g

/-- The actual normal-sphere self-map has identity action on homology
over any ring, including the prime coefficient fields used for transfer. -/
theorem normalSphereSection_HabsMap_id (R : Type) [Ring R]
    (u : CanonicalKernel d n) (r : ℝ) (k : ℕ) :
    HabsMap R k (TopCat.ofHom (normalSphereSection u r)) =
      𝟙 (Habs R k (TopCat.of (sphere (0 : ReducedValues (d+1) n) r))) := by
  rw [normalSphereSection_eq_id]
  change HabsMap R k (𝟙 _) = _
  exact HabsMap_id R k _

theorem normalSphereSection_preserves_class (R : Type) [Ring R]
    (u : CanonicalKernel d n) (r : ℝ) (k : ℕ)
    (c : Habs R k (TopCat.of (sphere (0 : ReducedValues (d+1) n) r))) :
    HabsMap R k (TopCat.ofHom (normalSphereSection u r)) c = c := by
  rw [normalSphereSection_HabsMap_id]
  rfl

end NRR.PrimePowerTopology
