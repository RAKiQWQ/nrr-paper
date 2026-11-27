import NRR.PrimePowerTopologyFiltration
import NRR.PrimePowerTopologyTwoColumns
import Mathlib.Data.Prod.Lex

/-! The actual first nonminimal Fox--Neuwirth stratum.
The cardinality constraints force a common initial horizontal projection
and at most two values of the final horizontal coordinate. -/

noncomputable section
open Set Topology Finset
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

theorem fuksProjection_card_pos {d n : ℕ} [NeZero n]
    (x : Configuration (d+1) n) (k : Fin d) :
    1 ≤ (Finset.univ.image (fuksProjection x k)).card := by
  exact Finset.card_pos.mpr ⟨fuksProjection x k 0,
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- If the horizontal complexity is at most one above its minimum, every
initial projection except the last still has exactly one value. -/
theorem nextFuks_initial_projection_card {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2)) (k : Fin d) :
    (Finset.univ.image (fuksProjection x k.castSucc)).card = 1 := by
  classical
  have htotal := (mem_fuksLevel_iff_complexity x).mp hx
  have positive := fuksProjection_card_pos x
  have monotone := fuksProjection_card_mono x
  by_contra hne
  have hk : 2 ≤ (Finset.univ.image (fuksProjection x k.castSucc)).card := by
    have := positive k.castSucc
    omega
  have hl : 2 ≤ (Finset.univ.image (fuksProjection x (Fin.last d))).card :=
    hk.trans (monotone (Fin.le_last k.castSucc))
  have hkl : k.castSucc ≠ Fin.last d := Fin.castSucc_ne_last k
  have bound : ∀ i : Fin (d+1),
      1 + (if i = k.castSucc then 1 else 0) +
        (if i = Fin.last d then 1 else 0) ≤
      (Finset.univ.image (fuksProjection x i)).card := by
    intro i
    by_cases hi : i = k.castSucc
    · subst i
      simpa [hkl] using hk
    · by_cases hil : i = Fin.last d
      · subst i
        simpa [Ne.symm hkl] using hl
      · simpa [hi, hil] using positive i
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bound i)
  have hs' : (d+1) + 1 + 1 ≤ fuksComplexity x := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, fuksComplexity] using hs
  omega

theorem nextFuks_last_projection_card_le_two {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2)) :
    (Finset.univ.image (fuksProjection x (Fin.last d))).card ≤ 2 := by
  have ht := (mem_fuksLevel_iff_complexity x).mp hx
  have he : fuksComplexity x = d +
      (Finset.univ.image (fuksProjection x (Fin.last d))).card := by
    rw [fuksComplexity, Fin.sum_univ_castSucc]
    simp only [nextFuks_initial_projection_card x hx, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- All but the final horizontal coordinate really coincide for every
configuration in the first nonminimal level. -/
theorem nextFuks_initial_coordinates_eq {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2)) (l : Fin d) (i j : Fin n) :
    (horizontalHeight (d+1) (x.val i)).1 l.castSucc =
      (horizontalHeight (d+1) (x.val j)).1 l.castSucc := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (nextFuks_initial_projection_card x hx l)
  have mem (q : Fin n) : fuksProjection x l.castSucc q = a := by
    apply Finset.mem_singleton.mp
    rw [← ha]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  have eq := congrFun ((mem i).trans (mem j).symm) l.castSucc
  simpa only [fuksProjection, le_refl, if_true] using eq

/-- The last horizontal coordinate distinguishes the two possible columns. -/
def nextFuksColumn {d n : ℕ} (x : Configuration (d+2) n) (i : Fin n) : ℝ :=
  (horizontalHeight (d+1) (x.val i)).1 (Fin.last d)

theorem nextFuks_column_card_le_two {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2)) :
    (Finset.univ.image (nextFuksColumn x)).card ≤ 2 := by
  classical
  have he : Finset.univ.image (nextFuksColumn x) =
      (Finset.univ.image (fuksProjection x (Fin.last d))).image
        (fun z => z (Fin.last d)) := by
    rw [Finset.image_image]
    congr 1
    funext i
    simp [nextFuksColumn, fuksProjection]
  rw [he]
  exact Finset.card_image_le.trans (nextFuks_last_projection_card_le_two x hx)

theorem nextFuks_vertical_of_column_card_one {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2))
    (hc : (Finset.univ.image (nextFuksColumn x)).card = 1) :
    x ∈ verticalSet (d+1) n := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have same (q : Fin n) : nextFuksColumn x q = a := by
    apply Finset.mem_singleton.mp
    rw [← ha]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  intro i j
  apply PiLp.ext
  intro l
  refine Fin.lastCases ?_ (fun k => ?_) l
  · exact (same i).trans (same j).symm
  · exact nextFuks_initial_coordinates_eq x hx k i j

/-- A genuinely nonvertical point of the next level has exactly two
nonempty, strictly ordered columns. -/
theorem nextFuks_two_column_values {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2))
    (hnv : x ∉ verticalSet (d+1) n) :
    ∃ a b : ℝ, a < b ∧ Finset.univ.image (nextFuksColumn x) = {a, b} := by
  classical
  have hp : 0 < (Finset.univ.image (nextFuksColumn x)).card :=
    Finset.card_pos.mpr ⟨nextFuksColumn x 0,
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hl := nextFuks_column_card_le_two x hx
  have hne : (Finset.univ.image (nextFuksColumn x)).card ≠ 1 :=
    fun he => hnv (nextFuks_vertical_of_column_card_one x hx he)
  have hc : (Finset.univ.image (nextFuksColumn x)).card = 2 := by omega
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hc
  rcases lt_or_gt_of_ne hab with hab | hab
  · exact ⟨a, b, hab, he⟩
  · exact ⟨b, a, hab, he.trans (Finset.pair_comm a b)⟩

private structure HeightSortIndex (n : ℕ) where
  val : Fin n

private def heightSortIndexEquiv (n : ℕ) : HeightSortIndex n ≃ Fin n where
  toFun := HeightSortIndex.val
  invFun := HeightSortIndex.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- Heights can always be sorted nondecreasingly, retaining labels to break
ties. Unlike a chamber ordering, this permits ties between distinct columns. -/
theorem exists_monotone_heightOrder {n : ℕ} (t : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (fun i => t (σ i)) := by
  letI : Fintype (HeightSortIndex n) :=
    Fintype.ofEquiv (Fin n) (heightSortIndexEquiv n).symm
  letI : LinearOrder (HeightSortIndex n) := LinearOrder.lift'
    (fun i => toLex (t i.val, i.val)) (by
      intro i j he
      have hv := congrArg (fun p : ℝ ×ₗ Fin n => (ofLex p).2) he
      cases i with
      | mk i => cases j with | mk j => exact congrArg HeightSortIndex.mk hv)
  let e : Fin n ≃o HeightSortIndex n := monoEquivOfFin (HeightSortIndex n) (k := n)
    ((Fintype.card_congr (heightSortIndexEquiv n)).trans (Fintype.card_fin n))
  refine ⟨e.toEquiv.trans (heightSortIndexEquiv n), ?_⟩
  intro i j hij
  exact Prod.Lex.monotone_fst _ _ (e.monotone hij)

private theorem horizontalHeight_first {d : ℕ} (v : Space (d+1)) (i : Fin d) :
    (horizontalHeight d v).1 i = v i.castSucc := rfl

private theorem horizontalHeight_last {d : ℕ} (v : Space (d+1)) :
    (horizontalHeight d v).2 = v (Fin.last d) := rfl

theorem nextFuks_same_column_height_injective {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2)) (i j : Fin n)
    (hc : nextFuksColumn x i = nextFuksColumn x j)
    (ht : (horizontalHeight (d+1) (x.val i)).2 =
      (horizontalHeight (d+1) (x.val j)).2) : i = j := by
  apply x.property
  apply (horizontalHeight (d+1)).injective
  apply Prod.ext _ ht
  apply PiLp.ext
  intro l
  refine Fin.lastCases hc (fun k => nextFuks_initial_coordinates_eq x hx k i j) l

/-- Every actual first-nonminimal configuration lies in a permutation image
of one of the existing two-column charts. Both columns are nonempty. -/
theorem nextFuks_exists_twoColumnChart {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n)
    (hx : x ∈ fuksLevel (d+1) n (d+2))
    (hnv : x ∉ verticalSet (d+1) n) :
    ∃ (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
      (p : twoColumnDomain (d := d) S),
      S.Nonempty ∧ S ≠ Finset.univ ∧ x = σ • twoColumnMap S p := by
  classical
  obtain ⟨a, b, hab, hvalues⟩ := nextFuks_two_column_values x hx hnv
  let t : Fin n → ℝ := fun i => (horizontalHeight (d+1) (x.val i)).2
  obtain ⟨σ, hσ⟩ := exists_monotone_heightOrder t
  let S : Finset (Fin n) := Finset.univ.filter (fun i => nextFuksColumn x (σ i) = a)
  have memS (i : Fin n) : i ∈ S ↔ nextFuksColumn x (σ i) = a := by simp [S]
  have values (i : Fin n) : nextFuksColumn x i = a ∨ nextFuksColumn x i = b := by
    have hm : nextFuksColumn x i ∈ Finset.univ.image (nextFuksColumn x) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa only [hvalues, Finset.mem_insert, Finset.mem_singleton] using hm
  have ha : ∃ i, nextFuksColumn x i = a := by
    have hm : a ∈ Finset.univ.image (nextFuksColumn x) := by rw [hvalues]; simp
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hm
  have hb : ∃ i, nextFuksColumn x i = b := by
    have hm : b ∈ Finset.univ.image (nextFuksColumn x) := by rw [hvalues]; simp
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hm
  have nonemptyS : S.Nonempty := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨σ.symm i, (memS _).mpr (by simpa using hi)⟩
  have properS : S ≠ Finset.univ := by
    obtain ⟨i, hi⟩ := hb
    intro he
    have hm : σ.symm i ∈ S := he ▸ Finset.mem_univ _
    have eq := (memS _).mp hm
    simp only [Equiv.apply_symm_apply, hi] at eq
    exact hab.ne eq.symm
  have sameColumn (i j : Fin n) (hmem : i ∈ S ↔ j ∈ S) :
      nextFuksColumn x (σ i) = nextFuksColumn x (σ j) := by
    by_cases hi : nextFuksColumn x (σ i) = a
    · have hj := (memS j).mp (hmem.mp ((memS i).mpr hi))
      exact hi.trans hj.symm
    · have hj : nextFuksColumn x (σ j) ≠ a := by
        intro hj
        exact hi ((memS i).mp (hmem.mpr ((memS j).mpr hj)))
      exact ((values (σ i)).resolve_left hi).trans
        ((values (σ j)).resolve_left hj).symm
  let v : Space d := (horizontalHeight d ((horizontalHeight (d+1) (x.val (σ 0))).1)).1
  let p : TwoColumnAmbientParameters d n := (((v, a), fun i => t (σ i)), b-a)
  have hp : p ∈ twoColumnDomain S := by
    refine ⟨sub_pos.mpr hab, ?_⟩
    intro i j hij hmem
    have hne : t (σ i) ≠ t (σ j) := by
      intro he
      have heq := nextFuks_same_column_height_injective x hx (σ i) (σ j)
        (sameColumn i j hmem) he
      exact hij.ne (σ.injective heq)
    exact lt_of_le_of_ne (hσ hij.le) hne
  have chart : twoColumnMap S ⟨p, hp⟩ = σ.symm • x := by
    apply Subtype.ext
    funext i
    apply (horizontalHeight (d+1)).injective
    simp only [twoColumnMap, twoColumnAmbient, ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply]
    change ((horizontalHeight d).symm
        (v, if i ∈ S then a else a+(b-a)), t (σ i)) =
      horizontalHeight (d+1) (x.val (σ.symm.symm i))
    rw [Equiv.symm_symm]
    apply Prod.ext
    swap
    · rfl
    apply (horizontalHeight d).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext
    · apply PiLp.ext
      intro l
      change (horizontalHeight d ((horizontalHeight (d+1) (x.val (σ 0))).1)).1 l = _
      rw [horizontalHeight_first, horizontalHeight_first]
      exact nextFuks_initial_coordinates_eq x hx l (σ 0) (σ i)
    · rw [horizontalHeight_last]
      change (if i ∈ S then a else a+(b-a)) = nextFuksColumn x (σ i)
      by_cases hi : i ∈ S
      · simpa only [if_pos hi] using ((memS i).mp hi).symm
      · have he := (values (σ i)).resolve_left (by simpa only [← memS i] using hi)
        simp only [if_neg hi]
        linarith
  refine ⟨σ, S, ⟨p, hp⟩, nonemptyS, properS, ?_⟩
  rw [chart, smul_smul]
  simp

private theorem horizontalHeight_symm_first {d : ℕ} (v : Space d) (s : ℝ) (i : Fin d) :
    (horizontalHeight d).symm (v, s) i.castSucc = v i := by
  have h := congrArg (fun q : Space d × ℝ => q.1 i)
    ((horizontalHeight d).apply_symm_apply (v, s))
  simpa only [horizontalHeight_first] using h

private theorem horizontalHeight_symm_last {d : ℕ} (v : Space d) (s : ℝ) :
    (horizontalHeight d).symm (v, s) (Fin.last d) = s := by
  have h := congrArg (fun q : Space d × ℝ => q.2)
    ((horizontalHeight d).apply_symm_apply (v, s))
  simpa only [horizontalHeight_last] using h

theorem twoColumnMap_initial_coordinate {d n : ℕ} (S : Finset (Fin n))
    (p : twoColumnDomain (d := d) S) (i : Fin n) (l : Fin d) :
    (horizontalHeight (d+1) ((twoColumnMap S p).val i)).1 l.castSucc =
      p.val.1.1.1 l := by
  simp only [twoColumnMap, twoColumnAmbient, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply]
  exact horizontalHeight_symm_first _ _ _

theorem twoColumnMap_column {d n : ℕ} (S : Finset (Fin n))
    (p : twoColumnDomain (d := d) S) (i : Fin n) :
    nextFuksColumn (twoColumnMap S p) i =
      if i ∈ S then p.val.1.1.2 else p.val.1.1.2+p.val.2 := by
  simp only [nextFuksColumn, twoColumnMap, twoColumnAmbient, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply]
  exact horizontalHeight_symm_last _ _

theorem twoColumnMap_initial_projection_card {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (p : twoColumnDomain (d := d) S) (k : Fin d) :
    (Finset.univ.image (fuksProjection (twoColumnMap S p) k.castSucc)).card = 1 := by
  classical
  have same (i : Fin n) : fuksProjection (twoColumnMap S p) k.castSucc i =
      fuksProjection (twoColumnMap S p) k.castSucc 0 := by
    funext a
    refine Fin.lastCases ?_ (fun j => ?_) a
    · have h : ¬ Fin.last d ≤ k.castSucc := not_le.mpr (Fin.castSucc_lt_last k)
      simp [fuksProjection, h]
    · by_cases h : j.castSucc ≤ k.castSucc
      · simp only [fuksProjection, h, if_true]
        rw [twoColumnMap_initial_coordinate, twoColumnMap_initial_coordinate]
      · simp [fuksProjection, h]
  have he : fuksProjection (twoColumnMap S p) k.castSucc =
      fun _ => fuksProjection (twoColumnMap S p) k.castSucc 0 := funext same
  rw [he]
  rw [Finset.image_const ⟨0, Finset.mem_univ _⟩, Finset.card_singleton]

theorem twoColumnMap_last_projection_card_le_two {d n : ℕ}
    (S : Finset (Fin n)) (p : twoColumnDomain (d := d) S) :
    (Finset.univ.image (fuksProjection (twoColumnMap S p) (Fin.last d))).card ≤ 2 := by
  classical
  let H : ℝ → (Fin (d+1) → ℝ) := fun s i => (horizontalHeight d).symm (p.val.1.1.1, s) i
  have repr (i : Fin n) :
      fuksProjection (twoColumnMap S p) (Fin.last d) i =
        H (if i ∈ S then p.val.1.1.2 else p.val.1.1.2+p.val.2) := by
    funext a
    simp only [fuksProjection, Fin.le_last, if_true, twoColumnMap, twoColumnAmbient,
      ContinuousMap.coe_mk, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have subset : Finset.univ.image (fuksProjection (twoColumnMap S p) (Fin.last d)) ⊆
      {H p.val.1.1.2, H (p.val.1.1.2+p.val.2)} := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rw [repr]
    by_cases hi : i ∈ S <;> simp [hi]
  exact (Finset.card_le_card subset).trans Finset.card_le_two

/-- The converse geometric inclusion: every genuine two-column chart
lands in the first nonminimal Fuks level. -/
theorem twoColumnMap_mem_nextFuks {d n : ℕ} [NeZero n]
    (S : Finset (Fin n)) (p : twoColumnDomain (d := d) S) :
    twoColumnMap S p ∈ fuksLevel (d+1) n (d+2) := by
  rw [mem_fuksLevel_iff_complexity, fuksComplexity, Fin.sum_univ_castSucc]
  simp only [twoColumnMap_initial_projection_card, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have := twoColumnMap_last_projection_card_le_two S p
  omega

theorem twoColumnMap_not_vertical {d n : ℕ} (S : Finset (Fin n))
    (p : twoColumnDomain (d := d) S) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    twoColumnMap S p ∉ verticalSet (d+1) n := by
  classical
  obtain ⟨i, hi⟩ := hne
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ S := by
    by_contra! hall
    exact hproper (Finset.eq_univ_of_forall hall)
  intro hv
  have h := congrArg (fun v : Space (d+1) => v (Fin.last d)) (hv i j)
  change nextFuksColumn (twoColumnMap S p) i = nextFuksColumn (twoColumnMap S p) j at h
  rw [twoColumnMap_column, twoColumnMap_column, if_pos hi, if_neg hj] at h
  linarith [p.property.1]

/-- An exact description of the first actual nonminimal stratum by the
permutation orbits of the nonempty proper two-column charts. -/
theorem mem_nextFuks_diff_vertical_iff {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n) :
    x ∈ fuksLevel (d+1) n (d+2) ∧ x ∉ verticalSet (d+1) n ↔
      ∃ (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
        (p : twoColumnDomain (d := d) S),
        S.Nonempty ∧ S ≠ Finset.univ ∧ x = σ • twoColumnMap S p := by
  constructor
  · rintro ⟨hx, hnv⟩
    exact nextFuks_exists_twoColumnChart x hx hnv
  · rintro ⟨σ, S, p, hne, hproper, rfl⟩
    refine ⟨(smul_mem_fuksLevel_iff σ _).mpr (twoColumnMap_mem_nextFuks S p), ?_⟩
    intro hv
    apply twoColumnMap_not_vertical S p hne hproper
    intro i j
    have he := hv (σ i) (σ j)
    change (horizontalHeight (d+1) ((twoColumnMap S p).val (σ.symm (σ i)))).1 =
      (horizontalHeight (d+1) ((twoColumnMap S p).val (σ.symm (σ j)))).1 at he
    simpa only [Equiv.symm_apply_apply] using he

end NRR.PrimePowerTopology
