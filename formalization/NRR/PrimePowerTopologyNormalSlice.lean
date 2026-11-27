import NRR.PrimePowerTopologyCanonicalNormal
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Determinant

/-! Actual transverse slices of the canonical section. On each slice the
section is literally the identity, including on every small normal sphere.
This supplies the local normalization for the later homology calculation;
this file does not assume or assert an Euler obstruction theorem. -/

noncomputable section
open Set Topology Metric
open NRR.PrimePower

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

@[simp] theorem canonicalLinear_normalSlice (u : CanonicalKernel d n)
    (v : ReducedValues (d+1) n) :
    canonicalLinear d n (u.val+canonicalLift d n v) = v := by
  rw [map_add,show canonicalLinear d n u.val = 0 from u.property,
    canonicalLinear_lift,zero_add]

def canonicalNormalFiberDomain (u : CanonicalKernel d n) :
    Set (ReducedValues (d+1) n) :=
  {v | Function.Injective (u.val+canonicalLift d n v)}

theorem isOpen_canonicalNormalFiberDomain (u : CanonicalKernel d n) :
    IsOpen (canonicalNormalFiberDomain u) :=
  (isOpen_distinctSites d n).preimage
    (continuous_const.add (canonicalLift d n).continuous)

theorem zero_mem_canonicalNormalFiberDomain (u : CanonicalKernel d n)
    (distinct : Function.Injective u.val) :
    (0 : ReducedValues (d+1) n) ∈ canonicalNormalFiberDomain u := by
  simpa only [canonicalNormalFiberDomain,mem_setOf_eq,map_zero,add_zero] using distinct

/-- A small closed normal disk is an actual disk of distinct-site
configurations, not just a formal ambient vector-space disk. -/
theorem exists_normalFiber_closedBall (u : CanonicalKernel d n)
    (distinct : Function.Injective u.val) :
    ∃ ε : ℝ,0 < ε ∧ closedBall (0 : ReducedValues (d+1) n) ε ⊆
      canonicalNormalFiberDomain u := by
  obtain ⟨ε,hε,sub⟩ := Metric.isOpen_iff.mp (isOpen_canonicalNormalFiberDomain u)
    0 (zero_mem_canonicalNormalFiberDomain u distinct)
  exact ⟨ε/2,half_pos hε,(closedBall_subset_ball (half_lt_self hε)).trans sub⟩

def normalFiberConfiguration (u : CanonicalKernel d n) :
    C(canonicalNormalFiberDomain u,Configuration (d+1) n) :=
  ⟨fun v => ⟨u.val+canonicalLift d n v.val,v.property⟩,
    (continuous_const.add ((canonicalLift d n).continuous.comp continuous_subtype_val)).subtype_mk _⟩

@[simp] theorem canonicalSection_normalFiberConfiguration (u : CanonicalKernel d n)
    (v : canonicalNormalFiberDomain u) :
    canonicalSection d n (normalFiberConfiguration u v) = v.val :=
  canonicalLinear_normalSlice u v.val

/-- The derivative of the actual transverse section is the identity at
every normal coordinate. In particular its determinant is positive one. -/
theorem hasFDerivAt_canonicalNormalSlice (u : CanonicalKernel d n)
    (v : ReducedValues (d+1) n) :
    HasFDerivAt (fun w => canonicalLinear d n (u.val+canonicalLift d n w))
      (ContinuousLinearMap.id ℝ (ReducedValues (d+1) n)) v := by
  simpa only [canonicalLinear_normalSlice] using hasFDerivAt_id v

theorem det_normalSlice_derivative :
    LinearMap.det (ContinuousLinearMap.id ℝ (ReducedValues (d+1) n)).toLinearMap = 1 := by
  exact LinearMap.det_id

/-- The sphere-valued map read from the transverse section, before any
choice of a sphere homology generator. Its formula uses the actual section. -/
def normalSphereSection (u : CanonicalKernel d n) (r : ℝ) :
    C(sphere (0 : ReducedValues (d+1) n) r,sphere (0 : ReducedValues (d+1) n) r) := by
  let F : sphere (0 : ReducedValues (d+1) n) r → sphere (0 : ReducedValues (d+1) n) r :=
    fun v => ⟨canonicalLinear d n (u.val+canonicalLift d n v.val),by
      simpa only [canonicalLinear_normalSlice] using v.property⟩
  have eq : F = id := by
    funext v
    apply Subtype.ext
    exact canonicalLinear_normalSlice u v.val
  exact ⟨F,by rw [eq]; exact continuous_id⟩

theorem normalSphereSection_eq_id (u : CanonicalKernel d n) (r : ℝ) :
    normalSphereSection u r = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  exact canonicalLinear_normalSlice u v.val

end NRR.PrimePowerTopology
