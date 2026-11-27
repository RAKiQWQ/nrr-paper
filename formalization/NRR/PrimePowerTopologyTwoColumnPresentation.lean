import NRR.PrimePowerTopologyTwoColumnAttaching
import NRR.PrimePowerTopologyNextStratumOrbits
import Mathlib.Data.Fin.Tuple.Sort

/-! A finite compact characteristic presentation of the true first
nonminimal Fuks level, indexed by ordered nontrivial two-block partitions. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.Coordinates

namespace NRR.PrimePowerTopology

abbrev TwoColumnSplit (n : ℕ) := {k : Fin n // 0 < k.val}
abbrev TwoColumnCellIndex (n : ℕ) := TwoColumnSplit n × Equiv.Perm (Fin n)

def canonicalColumnLabels {n : ℕ} (k : TwoColumnSplit n) : Finset (Fin n) :=
  firstColumnLabels n k.val.val k.val.isLt

theorem zero_mem_canonicalColumnLabels {n : ℕ} [NeZero n] (k : TwoColumnSplit n) :
    (0 : Fin n) ∈ canonicalColumnLabels k := by
  simpa only [canonicalColumnLabels,mem_firstColumnLabels,Fin.val_zero] using k.property

theorem split_not_mem_canonicalColumnLabels {n : ℕ} (k : TwoColumnSplit n) :
    k.val ∉ canonicalColumnLabels k := by
  simp only [canonicalColumnLabels,mem_firstColumnLabels,lt_self_iff_false,not_false_eq_true]

def canonicalTwoColumnCharacteristic {d n : ℕ} [NeZero n] (k : TwoColumnSplit n) :
    C(OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels k)),
      compactifiedFuksLevel (d+1) n (d+2)) :=
  compactTwoColumnCharacteristic (canonicalColumnLabels k) 0 k.val
    (zero_mem_canonicalColumnLabels k) (split_not_mem_canonicalColumnLabels k)

def orderedTwoColumnCharacteristic {d n : ℕ} [NeZero n] (c : TwoColumnCellIndex n) :
    C(OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels c.1)),
      compactifiedFuksLevel (d+1) n (d+2)) :=
  (⟨compactifiedFuksRelabel c.2,(compactifiedFuksRelabel c.2).continuous⟩ :
    C(compactifiedFuksLevel (d+1) n (d+2),compactifiedFuksLevel (d+1) n (d+2))).comp
    (canonicalTwoColumnCharacteristic c.1)

@[simp] theorem orderedTwoColumnCharacteristic_infty {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n) :
    (orderedTwoColumnCharacteristic (d := d) c ∞).val = ∞ := by
  change compactifiedConfigurationRelabel c.2
    (compactTwoColumnAttaching (d := d) (canonicalColumnLabels c.1) 0 c.1.val _ _ ∞) = ∞
  rw [compactTwoColumnAttaching_infty]
  rfl

theorem orderedTwoColumnCharacteristic_interior {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n)
    (p : twoColumnDomain (d := d) (canonicalColumnLabels c.1)) :
    (orderedTwoColumnCharacteristic c
      ((twoColumnClosedInterior (canonicalColumnLabels c.1) p) :
        OnePoint (closedTwoColumnDomain (canonicalColumnLabels c.1)))).val =
      ((c.2 • twoColumnMap (canonicalColumnLabels c.1) p : Configuration (d+2) n) :
        OnePoint (Configuration (d+2) n)) := by
  change compactifiedConfigurationRelabel c.2
    (compactTwoColumnAttaching (canonicalColumnLabels c.1) 0 c.1.val _ _
      ((twoColumnClosedInterior (canonicalColumnLabels c.1) p) :
        OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels c.1)))) = _
  rw [compactTwoColumnAttaching_coe]
  change compactifiedConfigurationRelabel c.2
    (twoColumnAttaching (canonicalColumnLabels c.1) p.val) = _
  rw [twoColumnAttaching_interior (canonicalColumnLabels c.1) p]
  rfl

theorem orderedTwoColumnCharacteristic_boundary {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n)
    (p : twoColumnCharacteristicBoundary (d := d) (canonicalColumnLabels c.1)) :
    (orderedTwoColumnCharacteristic c p.val).val ∈
      compactifiedFuksLevel (d+1) n (d+1) := by
  change compactifiedConfigurationRelabel c.2
    (compactTwoColumnAttaching (canonicalColumnLabels c.1) 0 c.1.val _ _ p.val) ∈ _
  apply (compactifiedFuksLevel_relabel_mem_iff c.2 _).mpr
  exact compactTwoColumnAttaching_boundary_mem_lower (canonicalColumnLabels c.1)
    0 c.1.val (zero_mem_canonicalColumnLabels c.1)
    (split_not_mem_canonicalColumnLabels c.1) p

abbrev TwoColumnCharacteristicSum (d n : ℕ) :=
  compactifiedFuksLevel (d+1) n (d+1) ⊕
    (Σ c : TwoColumnCellIndex n,
      OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels c.1)))

instance compactSpace_twoColumnCharacteristicSum (d n : ℕ) :
    CompactSpace (TwoColumnCharacteristicSum d n) := by
  classical
  unfold TwoColumnCharacteristicSum
  letI : CompactSpace (compactifiedFuksLevel (d+1) n (d+1)) :=
    isCompact_iff_compactSpace.mp (isClosed_compactifiedFuksLevel (d+1) n (d+1)).isCompact
  infer_instance

def twoColumnCharacteristicPresentation {d n : ℕ} [NeZero n] :
    C(TwoColumnCharacteristicSum d n, compactifiedFuksLevel (d+1) n (d+2)) where
  toFun := Sum.elim (compactifiedFuksInclusion (show d+1 ≤ d+2 by omega))
    (fun p => orderedTwoColumnCharacteristic p.1 p.2)
  continuous_toFun := continuous_sumElim.mpr
    ⟨(compactifiedFuksInclusion (d := d+1) (n := n) (show d+1 ≤ d+2 by omega)).hom.continuous,
      continuous_sigma (fun c => (orderedTwoColumnCharacteristic (d := d) c).continuous)⟩

/-- Every actual next-level point is either in the genuine lower level or
in the interior of exactly one ordered two-column chart. This theorem
only records coverage; uniqueness is established separately. -/
theorem twoColumnCharacteristicPresentation_surjective {d n : ℕ} [NeZero n] :
    Function.Surjective (twoColumnCharacteristicPresentation (d := d) (n := n)) := by
  intro x
  rcases x.property with hx | ⟨y,hy,he⟩
  · exact ⟨Sum.inl ⟨∞,Or.inl rfl⟩,Subtype.ext hx.symm⟩
  · by_cases hv : y ∈ verticalSet (d+1) n
    · have hm : y ∈ fuksLevel (d+1) n (d+1) := by
        rw [fuksLevel_minimal]
        exact hv
      exact ⟨Sum.inl ⟨(y : OnePoint (Configuration (d+2) n)),Or.inr ⟨y,hm,rfl⟩⟩,
        Subtype.ext he⟩
    · obtain ⟨k,hk,σ,p,hk0,hp⟩ := nextFuks_exists_splitSize_chart y hy hv
      let c : TwoColumnCellIndex n := (⟨⟨k,hk⟩,hk0⟩,σ)
      refine ⟨Sum.inr ⟨c,
        ((twoColumnClosedInterior (canonicalColumnLabels c.1) p) :
          OnePoint (closedTwoColumnDomain (canonicalColumnLabels c.1)))⟩,?_⟩
      apply Subtype.ext
      change (orderedTwoColumnCharacteristic c
        ((twoColumnClosedInterior (canonicalColumnLabels c.1) p) :
          OnePoint (closedTwoColumnDomain (canonicalColumnLabels c.1)))).val = x.val
      rw [orderedTwoColumnCharacteristic_interior]
      change ((σ • twoColumnMap (firstColumnLabels n k hk) p : Configuration (d+2) n) :
        OnePoint (Configuration (d+2) n)) = x.val
      rw [← hp]
      exact he

/-- Finitely many genuine compact characteristic spaces give the actual
level its quotient topology. No homological quotient assertion is used. -/
theorem isQuotientMap_twoColumnCharacteristicPresentation {d n : ℕ} [NeZero n] :
    IsQuotientMap (twoColumnCharacteristicPresentation (d := d) (n := n)) :=
  twoColumnCharacteristicPresentation.continuous.isClosedMap.isQuotientMap
    twoColumnCharacteristicPresentation.continuous
    twoColumnCharacteristicPresentation_surjective

def twoColumnLexKey {d n : ℕ} (x : Configuration (d+2) n) (i : Fin n) : ℝ ×ₗ ℝ :=
  toLex (nextFuksColumn x i,(horizontalHeight (d+1) (x.val i)).2)

theorem twoColumnLexKey_injective {d n : ℕ} [NeZero n]
    (x : Configuration (d+2) n) (hx : x ∈ fuksLevel (d+1) n (d+2)) :
    Function.Injective (twoColumnLexKey x) := by
  intro i j he
  exact nextFuks_same_column_height_injective x hx i j
    (congrArg (fun z : ℝ ×ₗ ℝ => (ofLex z).1) he)
    (congrArg (fun z : ℝ ×ₗ ℝ => (ofLex z).2) he)

@[simp] theorem twoColumnLexKey_relabel {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Configuration (d+2) n) (i : Fin n) :
    twoColumnLexKey (σ • x) (σ i) = twoColumnLexKey x i := by
  simp only [twoColumnLexKey,nextFuksColumn]
  change toLex ((horizontalHeight (d+1) (x.val (σ.symm (σ i)))).1 (Fin.last d),
    (horizontalHeight (d+1) (x.val (σ.symm (σ i)))).2) = _
  rw [Equiv.symm_apply_apply]

/-- The canonical labelled blocks are already sorted by actual column,
then by height within each column. -/
theorem strictMono_twoColumnLexKey {d n : ℕ}
    (k : TwoColumnSplit n) (p : twoColumnDomain (d := d) (canonicalColumnLabels k)) :
    StrictMono (twoColumnLexKey (twoColumnMap (canonicalColumnLabels k) p)) := by
  intro i j hij
  have height (a : Fin n) :
      (horizontalHeight (d+1) ((twoColumnMap (canonicalColumnLabels k) p).val a)).2 =
        p.val.1.2 a := by
    simp only [twoColumnMap,twoColumnAmbient,ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply]
  unfold twoColumnLexKey
  rw [Prod.Lex.toLex_lt_toLex,twoColumnMap_column,twoColumnMap_column,height,height]
  by_cases hi : i ∈ canonicalColumnLabels k
  · by_cases hj : j ∈ canonicalColumnLabels k
    · simp only [if_pos hi,if_pos hj]
      exact Or.inr ⟨trivial,p.property.2 i j hij (iff_of_true hi hj)⟩
    · simp only [if_pos hi,if_neg hj]
      exact Or.inl (lt_add_of_pos_right _ p.property.1)
  · have hj : j ∉ canonicalColumnLabels k := by
      intro hj
      apply hi
      have hj' : j.val < k.val.val := (mem_firstColumnLabels _ _ _ _).mp hj
      exact (mem_firstColumnLabels _ _ _ _).mpr (lt_trans hij hj')
    simp only [if_neg hi,if_neg hj]
    exact Or.inr ⟨trivial,p.property.2 i j hij (iff_of_false hi hj)⟩

/-- Equality of two interior chart points forces the entire ordering of
their labelled sites to coincide. -/
theorem orderedTwoColumnMap_perm_unique {d n : ℕ} [NeZero n]
    (k l : TwoColumnSplit n) (σ τ : Equiv.Perm (Fin n))
    (p : twoColumnDomain (d := d) (canonicalColumnLabels k))
    (q : twoColumnDomain (d := d) (canonicalColumnLabels l))
    (he : σ • twoColumnMap (canonicalColumnLabels k) p =
      τ • twoColumnMap (canonicalColumnLabels l) q) : σ = τ := by
  let x := σ • twoColumnMap (canonicalColumnLabels k) p
  have hx : x ∈ fuksLevel (d+1) n (d+2) :=
    (smul_mem_fuksLevel_iff σ _).mpr (twoColumnMap_mem_nextFuks _ p)
  have hs : StrictMono (twoColumnLexKey x ∘ σ) := by
    simpa only [Function.comp_def,x,twoColumnLexKey_relabel] using strictMono_twoColumnLexKey k p
  have ht : StrictMono (twoColumnLexKey x ∘ τ) := by
    change StrictMono (twoColumnLexKey (σ • twoColumnMap _ p) ∘ τ)
    rw [he]
    simpa only [Function.comp_def,twoColumnLexKey_relabel] using strictMono_twoColumnLexKey l q
  have hsort := Tuple.unique_monotone hs.monotone ht.monotone
  apply Equiv.ext
  intro i
  exact twoColumnLexKey_injective x hx (congrFun hsort i)

/-- The positive gap makes the split size recoverable from the actual
configuration; distinct split sizes cannot describe one interior point. -/
theorem canonicalTwoColumnMap_split_unique {d n : ℕ} [NeZero n]
    (k l : TwoColumnSplit n)
    (p : twoColumnDomain (d := d) (canonicalColumnLabels k))
    (q : twoColumnDomain (d := d) (canonicalColumnLabels l))
    (he : twoColumnMap (canonicalColumnLabels k) p =
      twoColumnMap (canonicalColumnLabels l) q) : k = l := by
  have col (i : Fin n) := congrArg (fun x : Configuration (d+2) n => nextFuksColumn x i) he
  have hzero : p.val.1.1.2 = q.val.1.1.2 := by
    have h := col 0
    simpa only [twoColumnMap_column,if_pos (zero_mem_canonicalColumnLabels k),
      if_pos (zero_mem_canonicalColumnLabels l)] using h
  apply Subtype.ext
  apply Fin.ext
  apply le_antisymm
  · by_contra hn
    have hlk : l.val.val < k.val.val := lt_of_not_ge hn
    have hmem : l.val ∈ canonicalColumnLabels k :=
      (mem_firstColumnLabels _ _ _ _).mpr hlk
    have h := col l.val
    simp only [twoColumnMap_column,if_pos hmem,
      if_neg (split_not_mem_canonicalColumnLabels l)] at h
    linarith [q.property.1]
  · by_contra hn
    have hkl : k.val.val < l.val.val := lt_of_not_ge hn
    have hmem : k.val ∈ canonicalColumnLabels l :=
      (mem_firstColumnLabels _ _ _ _).mpr hkl
    have h := col k.val
    simp only [twoColumnMap_column,if_neg (split_not_mem_canonicalColumnLabels k),
      if_pos hmem] at h
    linarith [p.property.1]

theorem orderedTwoColumnMap_cell_unique {d n : ℕ} [NeZero n]
    (c e : TwoColumnCellIndex n)
    (p : twoColumnDomain (d := d) (canonicalColumnLabels c.1))
    (q : twoColumnDomain (d := d) (canonicalColumnLabels e.1))
    (he : c.2 • twoColumnMap (canonicalColumnLabels c.1) p =
      e.2 • twoColumnMap (canonicalColumnLabels e.1) q) : c = e := by
  have hperm := orderedTwoColumnMap_perm_unique c.1 e.1 c.2 e.2 p q he
  have hmaps : twoColumnMap (canonicalColumnLabels c.1) p =
      twoColumnMap (canonicalColumnLabels e.1) q := by
    rw [hperm] at he
    exact (MulAction.injective e.2) he
  exact Prod.ext (canonicalTwoColumnMap_split_unique c.1 e.1 p q hmaps) hperm

/-- Precisely the true characteristic boundary maps to the lower level. -/
theorem orderedTwoColumnCharacteristic_mem_lower_iff {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n)
    (p : OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels c.1))) :
    (orderedTwoColumnCharacteristic c p).val ∈ compactifiedFuksLevel (d+1) n (d+1) ↔
      p ∈ twoColumnCharacteristicBoundary (canonicalColumnLabels c.1) := by
  constructor
  · intro hlower
    induction p using OnePoint.rec with
    | infty =>
        rintro ⟨q,hq⟩
        exact OnePoint.coe_ne_infty _ hq
    | coe p =>
        rw [mem_twoColumnCharacteristicBoundary_coe]
        intro hinside
        let q : twoColumnDomain (d := d) (canonicalColumnLabels c.1) := ⟨p.val,hinside⟩
        have hp : p = twoColumnClosedInterior (canonicalColumnLabels c.1) q := Subtype.ext rfl
        rw [hp,orderedTwoColumnCharacteristic_interior] at hlower
        have hactual : c.2 • twoColumnMap (canonicalColumnLabels c.1) q ∈
            fuksLevel (d+1) n (d+1) := by
          rcases hlower with hi | ⟨y,hy,he⟩
          · exact False.elim (OnePoint.coe_ne_infty _ hi)
          · exact (Option.some.inj he) ▸ hy
        have horig := (smul_mem_fuksLevel_iff c.2 _).mp hactual
        rw [fuksLevel_minimal] at horig
        exact twoColumnMap_not_vertical (canonicalColumnLabels c.1) q
          (nonempty_firstColumnLabels n c.1.val.val c.1.val.isLt c.1.property)
          (proper_firstColumnLabels n c.1.val.val c.1.val.isLt) horig
  · intro hp
    exact orderedTwoColumnCharacteristic_boundary c ⟨p,hp⟩

/-- The genuine cell interiors embed in the next level. -/
theorem orderedTwoColumnCharacteristic_injective_on_interior {d n : ℕ} [NeZero n]
    (c : TwoColumnCellIndex n) :
    Set.InjOn (orderedTwoColumnCharacteristic (d := d) c)
      (twoColumnCharacteristicBoundary (canonicalColumnLabels c.1))ᶜ := by
  intro p hp q hq he
  have asInterior (z : OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels c.1)))
      (hz : z ∉ twoColumnCharacteristicBoundary (canonicalColumnLabels c.1)) :
      ∃ a : twoColumnDomain (d := d) (canonicalColumnLabels c.1),
        z = ((twoColumnClosedInterior (canonicalColumnLabels c.1) a) :
          OnePoint (closedTwoColumnDomain (canonicalColumnLabels c.1))) := by
    change ¬ z ∉ range _ at hz
    obtain ⟨a,ha⟩ := not_not.mp hz
    exact ⟨a,ha.symm⟩
  obtain ⟨a,rfl⟩ := asInterior p hp
  obtain ⟨b,rfl⟩ := asInterior q hq
  have hm := congrArg Subtype.val he
  rw [orderedTwoColumnCharacteristic_interior,orderedTwoColumnCharacteristic_interior] at hm
  have hab : twoColumnMap (canonicalColumnLabels c.1) a =
      twoColumnMap (canonicalColumnLabels c.1) b :=
    (MulAction.injective c.2) (Option.some.inj hm)
  have hab' : a = b := (isEmbedding_twoColumnMap (canonicalColumnLabels c.1)
    0 c.1.val (zero_mem_canonicalColumnLabels c.1)
      (split_not_mem_canonicalColumnLabels c.1)).injective hab
  rw [hab']

/-- Distinct ordered characteristic cells have no common image outside
the genuine lower Fuks level. -/
theorem orderedTwoColumnCharacteristic_intersection_lower {d n : ℕ} [NeZero n]
    (c e : TwoColumnCellIndex n) (hne : c ≠ e)
    (p : OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels c.1)))
    (q : OnePoint (closedTwoColumnDomain (d := d) (canonicalColumnLabels e.1)))
    (he : orderedTwoColumnCharacteristic c p = orderedTwoColumnCharacteristic e q) :
    (orderedTwoColumnCharacteristic c p).val ∈ compactifiedFuksLevel (d+1) n (d+1) := by
  classical
  by_contra hn
  have hp := mt (orderedTwoColumnCharacteristic_mem_lower_iff c p).mpr hn
  have hq : q ∉ twoColumnCharacteristicBoundary (canonicalColumnLabels e.1) := by
    intro hq
    apply hn
    rw [he]
    exact (orderedTwoColumnCharacteristic_mem_lower_iff e q).mpr hq
  obtain ⟨a,ha⟩ := not_not.mp hp
  obtain ⟨b,hb⟩ := not_not.mp hq
  change ((twoColumnClosedInterior (canonicalColumnLabels c.1) a) :
    OnePoint (closedTwoColumnDomain (canonicalColumnLabels c.1))) = p at ha
  change ((twoColumnClosedInterior (canonicalColumnLabels e.1) b) :
    OnePoint (closedTwoColumnDomain (canonicalColumnLabels e.1))) = q at hb
  rw [← ha,← hb] at he
  have hm := congrArg Subtype.val he
  rw [orderedTwoColumnCharacteristic_interior,orderedTwoColumnCharacteristic_interior] at hm
  exact hne (orderedTwoColumnMap_cell_unique c e a b (Option.some.inj hm))

end NRR.PrimePowerTopology
