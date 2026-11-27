import NRR.PrimePowerTopologyCompactification

/-! A genuine two-column Fuks chart and its collision-aware closed collar.
The gap-zero face lands in the actual vertical chambers; collision faces
are sent continuously to infinity in the compactified configuration space. -/

noncomputable section
open Set Topology Filter
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

def twoColumnHeights {n : ℕ} (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {t | ∀ i j,i < j → (i ∈ S ↔ j ∈ S) → t i < t j}

theorem isOpen_twoColumnHeights {n : ℕ} (S : Finset (Fin n)) :
    IsOpen (twoColumnHeights S) := by
  have repr : twoColumnHeights S = ⋂ i : Fin n,⋂ j : Fin n,
      {t : Fin n → ℝ | i < j ∧ (i ∈ S ↔ j ∈ S) → t i < t j} := by
    ext t
    simp only [twoColumnHeights,mem_setOf_eq,mem_iInter,and_imp]
  rw [repr]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : i < j ∧ (i ∈ S ↔ j ∈ S)
  · simpa [h] using
      (isOpen_lt (continuous_apply i : Continuous (fun t : Fin n → ℝ => t i))
        (continuous_apply j : Continuous (fun t : Fin n → ℝ => t j)))
  · simp only [h,false_implies,setOf_true,isOpen_univ]

theorem convex_twoColumnHeights {n : ℕ} (S : Finset (Fin n)) :
    Convex ℝ (twoColumnHeights S) := by
  intro x hx y hy a b ha hb hab i j hij hmem
  change a*x i+b*y i < a*x j+b*y j
  rcases eq_or_lt_of_le ha with rfl | ha
  · have eq : b = 1 := by linarith
    simpa only [zero_mul,zero_add,eq,one_mul] using hy i j hij hmem
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hx i j hij hmem) ha)
      (mul_le_mul_of_nonneg_left (hy i j hij hmem).le hb)

theorem twoColumnHeights_nonempty {n : ℕ} (S : Finset (Fin n)) :
    (twoColumnHeights S).Nonempty := by
  refine ⟨fun i => i.val,fun i j hij _ => ?_⟩
  change (i.val : ℝ) < (j.val : ℝ)
  exact_mod_cast hij

abbrev TwoColumnAmbientParameters (d n : ℕ) := ((Space d × ℝ) × (Fin n → ℝ)) × ℝ

def twoColumnDomain {d n : ℕ} (S : Finset (Fin n)) :
    Set (TwoColumnAmbientParameters d n) := {p | 0 < p.2 ∧ p.1.2 ∈ twoColumnHeights S}

theorem isOpen_twoColumnDomain {d n : ℕ} (S : Finset (Fin n)) :
    IsOpen (twoColumnDomain (d := d) S) :=
  (isOpen_lt continuous_const continuous_snd).inter
    ((isOpen_twoColumnHeights S).preimage (continuous_snd.comp continuous_fst))

theorem convex_twoColumnDomain {d n : ℕ} (S : Finset (Fin n)) :
    Convex ℝ (twoColumnDomain (d := d) S) := by
  intro p hp q hq a b ha hb hab
  exact ⟨convex_Ioi (0 : ℝ) hp.1 hq.1 ha hb hab,
    convex_twoColumnHeights S hp.2 hq.2 ha hb hab⟩

theorem twoColumnDomain_nonempty {d n : ℕ} (S : Finset (Fin n)) :
    (twoColumnDomain (d := d) S).Nonempty := by
  obtain ⟨t,ht⟩ := twoColumnHeights_nonempty S
  exact ⟨(((0,0),t),1),zero_lt_one,ht⟩

theorem finrank_twoColumnAmbientParameters (d n : ℕ) :
    Module.finrank ℝ (TwoColumnAmbientParameters d n) = d+n+2 := by
  simp only [TwoColumnAmbientParameters,Module.finrank_prod,finrank_euclideanSpace_fin,
    Module.finrank_pi_fintype,Module.finrank_self,Fintype.card_fin,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one]
  omega

def twoColumnAmbient {d n : ℕ} (S : Finset (Fin n)) :
    C(TwoColumnAmbientParameters d n,(Fin n → Space (d+2))) := by
  classical
  refine ⟨fun p i => (horizontalHeight (d+1)).symm
    ((horizontalHeight d).symm (p.1.1.1,if i ∈ S then p.1.1.2 else p.1.1.2+p.2),p.1.2 i),?_⟩
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S <;> simp only [hi,if_true,if_false] <;> fun_prop

theorem twoColumnAmbient_injective {d n : ℕ} (S : Finset (Fin n))
    (p : TwoColumnAmbientParameters d n) (hp : p ∈ twoColumnDomain S) :
    Function.Injective (twoColumnAmbient S p) := by
  classical
  intro i j he
  have hcol := congrArg (fun z : Space (d+2) =>
    (horizontalHeight d ((horizontalHeight (d+1) z).1)).2) he
  have hheight := congrArg (fun z : Space (d+2) => (horizontalHeight (d+1) z).2) he
  simp only [twoColumnAmbient,ContinuousMap.coe_mk,ContinuousLinearEquiv.apply_symm_apply] at hcol hheight
  have same : i ∈ S ↔ j ∈ S := by
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp only [hi,hj,if_true,if_false] at hcol ⊢ <;>
      linarith [hp.1]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim ((hp.2 i j hij same).ne hheight)
  · exact hij
  · exact False.elim ((hp.2 j i hij same.symm).ne hheight.symm)

def twoColumnMap {d n : ℕ} (S : Finset (Fin n)) :
    C(twoColumnDomain (d := d) S,Configuration (d+2) n) :=
  ⟨fun p => ⟨twoColumnAmbient S p.val,twoColumnAmbient_injective S p.val p.property⟩,
    ((twoColumnAmbient S).continuous.comp continuous_subtype_val).subtype_mk _⟩

def twoColumnAttaching {d n : ℕ} (S : Finset (Fin n)) :
    C(TwoColumnAmbientParameters d n,OnePoint (Configuration (d+2) n)) :=
  (configurationCollapse (d+2) n).comp (twoColumnAmbient S)

@[simp] theorem twoColumnAttaching_interior {d n : ℕ} (S : Finset (Fin n))
    (p : twoColumnDomain (d := d) S) :
    twoColumnAttaching S p.val = ((twoColumnMap S p) : OnePoint (Configuration (d+2) n)) :=
  configurationCollapse_injective _ (twoColumnAmbient_injective S p.val p.property)

theorem twoColumnAmbient_injective_zero {d n : ℕ} (S : Finset (Fin n))
    (u : Space d × ℝ) (t : Fin n → ℝ) :
    Function.Injective (twoColumnAmbient S ((u,t),0)) ↔ Function.Injective t := by
  classical
  constructor
  · intro h i j he
    apply h
    simp only [twoColumnAmbient,ContinuousMap.coe_mk,add_zero,ite_self]
    exact congrArg (fun z => (horizontalHeight (d+1)).symm ((horizontalHeight d).symm u,z)) he
  · intro h i j he
    apply h
    have H := congrArg (fun z => (horizontalHeight (d+1) z).2) he
    simpa only [twoColumnAmbient,ContinuousMap.coe_mk,ContinuousLinearEquiv.apply_symm_apply] using H

theorem twoColumnAttaching_zero_collision {d n : ℕ} (S : Finset (Fin n))
    (u : Space d × ℝ) (t : Fin n → ℝ) (collision : ¬ Function.Injective t) :
    twoColumnAttaching S ((u,t),0) = ∞ := by
  apply configurationCollapse_collision
  exact collision ∘ (twoColumnAmbient_injective_zero S u t).mp

theorem twoColumnAttaching_zero_vertical {d n : ℕ} (S : Finset (Fin n)) (i₀ : Fin n)
    (u : Space d × ℝ) (t : LineConfiguration n) :
    twoColumnAttaching S ((u,t.val),0) =
      (((verticalCoordinates (d := d+1) i₀).symm ((horizontalHeight d).symm u,t)).val :
        OnePoint (Configuration (d+2) n)) := by
  classical
  have hinj := (twoColumnAmbient_injective_zero S u t.val).mpr t.property
  change configurationCollapse (d+2) n _ = _
  rw [configurationCollapse_injective _ hinj]
  apply congrArg (fun x : Configuration (d+2) n => (x : OnePoint (Configuration (d+2) n)))
  apply Subtype.ext
  funext i
  simp [twoColumnAmbient,verticalCoordinates]

def twoColumnRecovery {d n : ℕ} (iL iR : Fin n) :
    C((Fin n → Space (d+2)),TwoColumnAmbientParameters d n) :=
  ⟨fun x =>
    ((((horizontalHeight d ((horizontalHeight (d+1) (x iL)).1)).1,
      (horizontalHeight d ((horizontalHeight (d+1) (x iL)).1)).2),
      fun i => (horizontalHeight (d+1) (x i)).2),
    (horizontalHeight d ((horizontalHeight (d+1) (x iR)).1)).2-
      (horizontalHeight d ((horizontalHeight (d+1) (x iL)).1)).2),by fun_prop⟩

@[simp] theorem twoColumnRecovery_map {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S)
    (p : twoColumnDomain (d := d) S) :
    twoColumnRecovery iL iR (twoColumnMap S p).val = p.val := by
  simp [twoColumnRecovery,twoColumnMap,twoColumnAmbient,hL,hR]

/-- The chart is an actual topological embedding, witnessed by continuous
recovery of the common coordinates, both column positions, and every height. -/
theorem isEmbedding_twoColumnMap {d n : ℕ} (S : Finset (Fin n))
    (iL iR : Fin n) (hL : iL ∈ S) (hR : iR ∉ S) :
    IsEmbedding (twoColumnMap (d := d) S) := by
  have comp : (fun p : twoColumnDomain (d := d) S =>
      twoColumnRecovery iL iR (twoColumnMap S p).val) = Subtype.val :=
    funext (twoColumnRecovery_map S iL iR hL hR)
  have emb : IsEmbedding (fun p : twoColumnDomain (d := d) S =>
      twoColumnRecovery iL iR (twoColumnMap S p).val) := by
    rw [comp]
    exact IsEmbedding.subtypeVal
  exact IsEmbedding.of_comp (twoColumnMap S).continuous
    ((twoColumnRecovery iL iR).continuous.comp continuous_subtype_val) emb

def IsColumnShuffle {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j,i < j → (σ i ∈ S ↔ σ j ∈ S) → σ i < σ j

theorem twoColumnHeights_iff_shuffle {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) {t : Fin n → ℝ} (sorted : t ∈ heightChamber n σ) :
    t ∈ twoColumnHeights S ↔ IsColumnShuffle S σ := by
  constructor
  · intro ht i j hij same
    rcases lt_trichotomy (σ i) (σ j) with h | h | h
    · exact h
    · exact False.elim (hij.ne (σ.injective h))
    · exact False.elim (lt_asymm (sorted hij) (ht _ _ h same.symm))
  · intro shuffle i j hij same
    have order : σ.symm i < σ.symm j := by
      rcases lt_trichotomy (σ.symm i) (σ.symm j) with h | h | h
      · exact h
      · exact False.elim (hij.ne (σ.symm.injective h))
      · have bad := shuffle _ _ h (by simpa only [Equiv.apply_symm_apply] using same.symm)
        simp only [Equiv.apply_symm_apply] at bad
        exact False.elim (lt_asymm hij bad)
    simpa only [Equiv.apply_symm_apply] using sorted order

/-- Every collision-free boundary point belongs to precisely one actual
vertical chamber, and that chamber is an order-preserving two-block shuffle. -/
theorem exists_unique_twoColumnShuffle {n : ℕ} (S : Finset (Fin n))
    (t : LineConfiguration n) (ht : t.val ∈ twoColumnHeights S) :
    ∃! σ : Equiv.Perm (Fin n),IsColumnShuffle S σ ∧ t.val ∈ heightChamber n σ := by
  obtain ⟨σ,hσ,unique⟩ := exists_unique_heightChamber t
  refine ⟨σ,⟨(twoColumnHeights_iff_shuffle S σ hσ).mp ht,hσ⟩,?_⟩
  intro τ hτ
  exact unique τ hτ.2

end NRR.PrimePowerTopology
