import NRR.PrimePowerTopologyCanonical

/-! An explicit global linear normal form for the canonical section.
Its restriction to the open distinct-site locus is a genuine local normal
model near every point of the vertical zero stratum. -/

noncomputable section
open Set Topology
open NRR.PrimePower

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

abbrev CanonicalKernel (d n : ℕ) [NeZero n] :=
  LinearMap.ker (canonicalLinear d n).toLinearMap

def canonicalNormalLinearEquiv (d n : ℕ) [NeZero n] :
    (Fin n → Space (d+1)) ≃ₗ[ℝ] CanonicalKernel d n × ReducedValues (d+1) n where
  toFun x := (⟨x-canonicalLift d n (canonicalLinear d n x),by
    change canonicalLinear d n (x-canonicalLift d n (canonicalLinear d n x)) = 0
    rw [map_sub,canonicalLinear_lift,sub_self]⟩,canonicalLinear d n x)
  invFun p := p.1.val+canonicalLift d n p.2
  left_inv x := by
    change x-canonicalLift d n (canonicalLinear d n x)+
      canonicalLift d n (canonicalLinear d n x) = x
    abel
  right_inv p := by
    rcases p with ⟨u,v⟩
    have hu : canonicalLinear d n u.val = 0 := u.property
    have hv : canonicalLinear d n (u.val+canonicalLift d n v) = v := by
      rw [map_add,hu,canonicalLinear_lift,zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change u.val+canonicalLift d n v-
        canonicalLift d n (canonicalLinear d n (u.val+canonicalLift d n v)) = u.val
      rw [hv]
      abel
    · exact hv
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x+y-canonicalLift d n (canonicalLinear d n (x+y)) =
        (x-canonicalLift d n (canonicalLinear d n x))+
          (y-canonicalLift d n (canonicalLinear d n y))
      rw [map_add,map_add]
      abel
    · exact map_add (canonicalLinear d n) x y
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      change a • x-canonicalLift d n (canonicalLinear d n (a • x)) =
        a • (x-canonicalLift d n (canonicalLinear d n x))
      rw [map_smul,map_smul,smul_sub]
    · exact map_smul (canonicalLinear d n) a x

/-- These are continuous linear coordinates, not merely a bijective
parameterization of the zero stratum. -/
def canonicalNormalCoordinates (d n : ℕ) [NeZero n] :
    (Fin n → Space (d+1)) ≃L[ℝ] CanonicalKernel d n × ReducedValues (d+1) n :=
  (canonicalNormalLinearEquiv d n).toContinuousLinearEquiv

@[simp] theorem canonicalNormalCoordinates_snd (x : Fin n → Space (d+1)) :
    (canonicalNormalCoordinates d n x).2 = canonicalLinear d n x := rfl

@[simp] theorem canonicalNormalCoordinates_symm (p : CanonicalKernel d n × ReducedValues (d+1) n) :
    (canonicalNormalCoordinates d n).symm p = p.1.val+canonicalLift d n p.2 := rfl

theorem isOpen_distinctSites (d n : ℕ) :
    IsOpen {x : Fin n → Space (d+1) | Function.Injective x} := by
  have eq : {x : Fin n → Space (d+1) | Function.Injective x} =
      ⋂ i : Fin n,⋂ j : Fin n,{x | i ≠ j → x i ≠ x j} := by
    ext x
    simp only [mem_setOf_eq,mem_iInter,Function.Injective]
    constructor
    · intro h i j hij he
      exact hij (h he)
    · intro h i j he
      by_contra hij
      exact h i j hij he
  rw [eq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp only [hij,ne_eq,not_true_eq_false,false_implies,setOf_true,isOpen_univ]
  · simpa only [hij,ne_eq,not_false_eq_true,true_implies] using
      (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl

/-- In normal coordinates the real configuration space is an open set.
The canonical section is exactly the second linear coordinate there. -/
def canonicalNormalDomain (d n : ℕ) [NeZero n] :
    Set (CanonicalKernel d n × ReducedValues (d+1) n) :=
  (canonicalNormalCoordinates d n).symm ⁻¹'
    {x : Fin n → Space (d+1) | Function.Injective x}

theorem isOpen_canonicalNormalDomain (d n : ℕ) [NeZero n] :
    IsOpen (canonicalNormalDomain d n) :=
  (isOpen_distinctSites d n).preimage (canonicalNormalCoordinates d n).symm.continuous

def configurationNormalCoordinates (d n : ℕ) [NeZero n] :
    Configuration (d+1) n ≃ₜ canonicalNormalDomain d n :=
  (canonicalNormalCoordinates d n).toHomeomorph.subtype (fun x => by
    change Function.Injective x ↔ Function.Injective
      ((canonicalNormalCoordinates d n).symm (canonicalNormalCoordinates d n x))
    rw [ContinuousLinearEquiv.symm_apply_apply])

@[simp] theorem canonicalSection_normalCoordinates (x : Configuration (d+1) n) :
    (configurationNormalCoordinates d n x).val.2 = canonicalSection d n x := rfl

/-- The zero stratum has the expected dimension: one common horizontal
translation and one independent height per site. The normal dimension is
exactly `d * (n-1)`, the rank of the reduced permutation target. -/
theorem finrank_canonicalKernel : Module.finrank ℝ (CanonicalKernel d n) = d+n := by
  obtain ⟨m,hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  subst n
  have dim := (canonicalNormalLinearEquiv d (m+1)).finrank_eq
  simp only [Module.finrank_pi_fintype,Module.finrank_prod,
    finrank_reducedValues,finrank_euclideanSpace_fin,Nat.add_sub_cancel,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at dim
  nlinarith

end NRR.PrimePowerTopology
