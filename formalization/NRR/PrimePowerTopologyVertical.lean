import NRR.PrimePowerExistenceConfiguration
import NRR.Coordinates
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Order.Hom.Set

/-!
The actual lowest Fuks stratum in the distinct-site configuration space.

The vertical locus consists of configurations whose horizontal projections
coincide. We give its genuine Hausdorff-space homeomorphism with a horizontal
translation times configurations on the line. The latter split into the
pairwise disjoint contractible open ordering chambers. These are geometric
facts about the original configuration space, not assumptions about a model.
-/

noncomputable section
open Set Topology
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

abbrev LineConfiguration (n : ℕ) := {t : Fin n → ℝ // Function.Injective t}

def verticalSet (d n : ℕ) : Set (Configuration (d+1) n) :=
  {x | ∀ i j,(horizontalHeight d (x.val i)).1 = (horizontalHeight d (x.val j)).1}

theorem isClosed_verticalSet (d n : ℕ) : IsClosed (verticalSet d n) := by
  have repr : verticalSet d n = ⋂ i : Fin n,⋂ j : Fin n,
      {x : Configuration (d+1) n |
        (horizontalHeight d (x.val i)).1 = (horizontalHeight d (x.val j)).1} := by
    ext x
    simp only [verticalSet,mem_setOf_eq,mem_iInter]
  rw [repr]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  have cont (k : Fin n) : Continuous (fun x : Configuration (d+1) n =>
      (horizontalHeight d (x.val k)).1) :=
    continuous_fst.comp ((horizontalHeight d).continuous.comp
      ((continuous_apply k).comp continuous_subtype_val))
  exact isClosed_eq (cont i) (cont j)

/-- Coordinates for the actual vertical locus: its common horizontal
projection and its pairwise distinct heights. A base label is only used to
read the common horizontal coordinate. -/
def verticalCoordinates {d n : ℕ} (i₀ : Fin n) :
    verticalSet d n ≃ₜ Space d × LineConfiguration n where
  toFun x := ((horizontalHeight d (x.val.val i₀)).1,
    ⟨fun i => (horizontalHeight d (x.val.val i)).2,by
      intro i j he
      apply x.val.property
      apply (horizontalHeight d).injective
      exact Prod.ext (x.property i j) he⟩)
  invFun p := ⟨⟨fun i => (horizontalHeight d).symm (p.1,p.2.val i),by
    intro i j he
    apply p.2.property
    have h := congrArg (fun z => (horizontalHeight d z).2) he
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h⟩,by
      intro i j
      simp only [ContinuousLinearEquiv.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply (horizontalHeight d).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (x.property i₀ i) rfl
  right_inv p := by
    apply Prod.ext
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
    · apply Subtype.ext
      funext i
      simp only [ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := by
    have cont (i : Fin n) : Continuous (fun x : verticalSet d n =>
        horizontalHeight d (x.val.val i)) :=
      (horizontalHeight d).continuous.comp
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
    exact (continuous_fst.comp (cont i₀)).prodMk
      ((continuous_pi fun i => continuous_snd.comp (cont i)).subtype_mk _)
  continuous_invFun := by
    have cont : Continuous (fun p : Space d × LineConfiguration n =>
        fun i => (horizontalHeight d).symm (p.1,p.2.val i)) :=
      continuous_pi fun i => (horizontalHeight d).symm.continuous.comp
        (continuous_fst.prodMk
          ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    exact (cont.subtype_mk _).subtype_mk _

/-- A component of the one-dimensional configuration space, labelled by
the bottom-to-top permutation of its points. -/
def heightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {t | StrictMono (fun i => t (σ i))}

theorem isOpen_heightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (heightChamber n σ) := by
  have repr : heightChamber n σ = ⋂ i : Fin n,⋂ j : Fin n,
      {t : Fin n → ℝ | i < j → t (σ i) < t (σ j)} := by
    ext t
    simp only [heightChamber,mem_setOf_eq,mem_iInter,StrictMono]
  rw [repr]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i < j
  · simpa only [hij,true_implies] using
      (isOpen_lt (continuous_apply (σ i)) (continuous_apply (σ j)))
  · simp only [hij,false_implies,setOf_true,isOpen_univ]

theorem convex_heightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Convex ℝ (heightChamber n σ) := by
  intro x hx y hy a b ha hb hab i j hij
  change a*x (σ i)+b*y (σ i) < a*x (σ j)+b*y (σ j)
  rcases eq_or_lt_of_le ha with rfl | ha
  · have he : b = 1 := by linarith
    simpa only [zero_mul,zero_add,he,one_mul] using hy hij
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hx hij) ha)
      (mul_le_mul_of_nonneg_left (hy hij).le hb)

theorem heightChamber_nonempty (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (heightChamber n σ).Nonempty := by
  refine ⟨fun i => (σ.symm i).val,?_⟩
  intro i j hij
  simp only [Equiv.symm_apply_apply]
  exact_mod_cast hij

theorem contractible_heightChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ContractibleSpace (heightChamber n σ) :=
  (convex_heightChamber n σ).contractibleSpace (heightChamber_nonempty n σ)

theorem heightChamber_injective {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {t : Fin n → ℝ} (ht : t ∈ heightChamber n σ) : Function.Injective t := by
  intro i j he
  apply σ.symm.injective
  apply ht.injective
  simpa only [Equiv.apply_symm_apply] using he

theorem heightChamber_unique {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    {t : Fin n → ℝ} (hs : t ∈ heightChamber n σ) (ht : t ∈ heightChamber n τ) : σ = τ := by
  let e := σ.trans τ.symm
  have monotone : Monotone e := by
    intro i j hij
    apply ht.le_iff_le.mp
    simpa only [e,Equiv.trans_apply,Equiv.apply_symm_apply] using hs.monotone hij
  have inverse : Monotone e.symm := by
    intro i j hij
    apply hs.le_iff_le.mp
    simpa only [e,Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.apply_symm_apply] using ht.monotone hij
  have he : e = Equiv.refl (Fin n) := by
    apply Equiv.ext
    intro i
    exact DFunLike.congr_fun
      (Subsingleton.elim (e.toOrderIso monotone inverse) (OrderIso.refl _)) i
  apply Equiv.ext
  intro i
  have h := congrArg τ (Equiv.congr_fun he i)
  simpa only [e,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.refl_apply] using h

theorem heightChambers_pairwise_disjoint (n : ℕ) :
    Pairwise fun σ τ : Equiv.Perm (Fin n) => Disjoint (heightChamber n σ) (heightChamber n τ) := by
  intro σ τ hne
  exact Set.disjoint_left.mpr (fun _ hs ht => hne (heightChamber_unique hs ht))

private structure HeightIndex (n : ℕ) where
  val : Fin n

private def heightIndexEquiv (n : ℕ) : HeightIndex n ≃ Fin n where
  toFun := HeightIndex.val
  invFun := HeightIndex.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- Every actual configuration on the line lies in one and only one of
the open contractible chambers. -/
theorem exists_unique_heightChamber {n : ℕ} (t : LineConfiguration n) :
    ∃! σ : Equiv.Perm (Fin n), t.val ∈ heightChamber n σ := by
  letI : Fintype (HeightIndex n) := Fintype.ofEquiv (Fin n) (heightIndexEquiv n).symm
  letI : LinearOrder (HeightIndex n) := LinearOrder.lift' (fun i => t.val i.val) (by
    intro i j he
    cases i with | mk i => cases j with | mk j => exact congrArg HeightIndex.mk (t.property he))
  let e : Fin n ≃o HeightIndex n := monoEquivOfFin (HeightIndex n) (k := n)
    ((Fintype.card_congr (heightIndexEquiv n)).trans (Fintype.card_fin n))
  let σ : Equiv.Perm (Fin n) := e.toEquiv.trans (heightIndexEquiv n)
  have sorted : t.val ∈ heightChamber n σ := by
    intro i j hij
    change t.val (e i).val < t.val (e j).val
    exact e.strictMono hij
  exact ⟨σ,sorted,fun τ hτ => heightChamber_unique hτ sorted⟩

end NRR.PrimePowerTopology
