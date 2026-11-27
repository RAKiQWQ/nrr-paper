import NRR.PrimePowerTopologyVertical

/-! The genuine canonical section of the reduced permutation bundle.
Its zero locus is the actual vertical Fuks stratum. We also construct a
continuous linear right inverse in ambient configuration coordinates. -/

noncomputable section
open Set Topology
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

variable {d n : ℕ} [NeZero n]

/-- Subtract the common horizontal mean from every labelled site. -/
def canonicalLinear (d n : ℕ) [NeZero n] :
    (Fin n → Space (d+1)) →L[ℝ] ReducedValues (d+1) n where
  toFun x := ⟨fun k => centered (fun i => (horizontalHeight d (x i)).1 k),
    fun k => sum_centered (Nat.pos_of_ne_zero (NeZero.ne n)) _⟩
  map_add' x y := by
    apply Subtype.ext
    funext k i
    change centered (fun j => (horizontalHeight d ((x+y) j)).1 k) i =
      centered (fun j => (horizontalHeight d (x j)).1 k) i +
      centered (fun j => (horizontalHeight d (y j)).1 k) i
    simp only [centered,rowMean,Pi.add_apply,map_add,Prod.fst_add,PiLp.add_apply,
      Finset.sum_add_distrib,add_div]
    ring
  map_smul' a x := by
    apply Subtype.ext
    funext k i
    change centered (fun j => (horizontalHeight d ((a • x) j)).1 k) i =
      a * centered (fun j => (horizontalHeight d (x j)).1 k) i
    simp only [centered,rowMean,Pi.smul_apply,map_smul,Prod.smul_fst,PiLp.smul_apply,
      smul_eq_mul,← Finset.mul_sum]
    ring
  cont := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    apply continuous_pi
    intro i
    let v (j : Fin n) : (Fin n → Space (d+1)) → ℝ :=
      fun x => (horizontalHeight d (x j)).1 k
    have cv (j : Fin n) : Continuous (v j) :=
      (EuclideanSpace.proj k).continuous.comp
        (continuous_fst.comp ((horizontalHeight d).continuous.comp (continuous_apply j)))
    exact (cv i).sub ((continuous_finset_sum _ (fun j _ => cv j)).div_const _)

def canonicalSection (d n : ℕ) [NeZero n] :
    C(Configuration (d+1) n,ReducedValues (d+1) n) :=
  ⟨fun x => canonicalLinear d n x.val,(canonicalLinear d n).continuous.comp continuous_subtype_val⟩

@[simp] theorem canonicalSection_apply (x : Configuration (d+1) n)
    (k : Fin d) (i : Fin n) :
    (canonicalSection d n x).val k i =
      (horizontalHeight d (x.val i)).1 k -
        rowMean (fun j => (horizontalHeight d (x.val j)).1 k) := rfl

theorem canonicalSection_equivariant (σ : Equiv.Perm (Fin n))
    (x : Configuration (d+1) n) :
    canonicalSection d n (σ • x) = σ • canonicalSection d n x := by
  apply Subtype.ext
  funext k
  exact centered_reindex σ.symm (fun i => (horizontalHeight d (x.val i)).1 k)

/-- The canonical section vanishes exactly when all horizontal coordinates
coincide, with no condition on their common position or the distinct heights. -/
theorem canonicalSection_zero_iff (x : Configuration (d+1) n) :
    canonicalSection d n x = 0 ↔ x ∈ verticalSet d n := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  constructor
  · intro zero i j
    ext k
    have hz := congrArg Subtype.val zero
    have row := congrFun hz k
    exact (centered_eq_zero_iff hn _).mp row i j
  · intro vertical
    apply Subtype.ext
    funext k
    apply (centered_eq_zero_iff hn _).mpr
    intro i j
    exact congrArg (fun u : Space d => u k) (vertical i j)

/-- Prescribe any centered horizontal displacement while keeping all
vertical coordinates zero. This is an actual continuous linear lift. -/
def canonicalLift (d n : ℕ) :
    ReducedValues (d+1) n →L[ℝ] (Fin n → Space (d+1)) where
  toFun v := fun i => (horizontalHeight d).symm (WithLp.toLp 2 (fun k => v.val k i),0)
  map_add' v w := by
    funext i
    change (horizontalHeight d).symm (WithLp.toLp 2 (fun k => (v+w).val k i),0) =
      (horizontalHeight d).symm (WithLp.toLp 2 (fun k => v.val k i),0) +
        (horizontalHeight d).symm (WithLp.toLp 2 (fun k => w.val k i),0)
    rw [← map_add]
    congr 1
    apply Prod.ext
    · ext k
      rfl
    · simp
  map_smul' a v := by
    funext i
    change (horizontalHeight d).symm (WithLp.toLp 2 (fun k => (a • v).val k i),0) =
      a • (horizontalHeight d).symm (WithLp.toLp 2 (fun k => v.val k i),0)
    rw [← map_smul]
    congr 1
    apply Prod.ext
    · ext k
      rfl
    · simp
  cont := by
    apply continuous_pi
    intro i
    apply (horizontalHeight d).symm.continuous.comp
    apply Continuous.prodMk _ continuous_const
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k =>
      (continuous_apply i).comp ((continuous_apply k).comp continuous_subtype_val)

@[simp] theorem canonicalLinear_lift (v : ReducedValues (d+1) n) :
    canonicalLinear d n (canonicalLift d n v) = v := by
  apply Subtype.ext
  funext k i
  change centered (fun j => (horizontalHeight d
    ((horizontalHeight d).symm (WithLp.toLp 2 (fun l => v.val l j),0))).1 k) i = v.val k i
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  change v.val k i - (∑ j,v.val k j)/(n : ℝ) = v.val k i
  rw [v.property k,zero_div,sub_zero]

theorem canonicalLinear_surjective : Function.Surjective (canonicalLinear d n) :=
  fun v => ⟨canonicalLift d n v,canonicalLinear_lift v⟩

end NRR.PrimePowerTopology
