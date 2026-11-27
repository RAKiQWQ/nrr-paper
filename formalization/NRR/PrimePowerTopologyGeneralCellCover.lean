import NRR.PrimePowerTopologyGeneralCellCones
import Mathlib.Data.Fin.Tuple.Sort

/-!
Every actual configuration has a unique lexicographic ordering and a unique
adjacent first-difference word. The resulting relabelled open general cells
therefore cover the configuration space, with pairwise disjoint chart images.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology
open NRR.PrimePower

namespace NRR.PrimePowerTopology

/-- The actual Euclidean coordinates, ordered lexicographically. -/
def configurationLexKey {D n : ℕ} (x : Configuration D n) (i : Fin n) :
    Lex (Fin D → ℝ) := toLex (fun k => x.val i k)

theorem configurationLexKey_injective {D n : ℕ} (x : Configuration D n) :
    Function.Injective (configurationLexKey x) := by
  intro i j hij
  apply x.property
  apply PiLp.ext
  intro k
  exact congrArg (fun z : Lex (Fin D → ℝ) => z k) hij

@[simp] theorem configurationLexKey_relabel {D n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Configuration D n) (i : Fin n) :
    configurationLexKey (σ • x) (σ i) = configurationLexKey x i := by
  change toLex (fun k => x.val (σ.symm (σ i)) k) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Position-to-label permutation of a configuration in lexicographic order. -/
def configurationLexOrder {D n : ℕ} (x : Configuration D n) : Equiv.Perm (Fin n) :=
  Tuple.sort (configurationLexKey x)

theorem strictMono_configurationLexOrder {D n : ℕ} (x : Configuration D n) :
    StrictMono (configurationLexKey x ∘ configurationLexOrder x) :=
  (Tuple.monotone_sort _).strictMono_of_injective
    ((configurationLexKey_injective x).comp (configurationLexOrder x).injective)

theorem configurationLexOrder_unique {D n : ℕ} (x : Configuration D n)
    (σ : Equiv.Perm (Fin n)) (hσ : StrictMono (configurationLexKey x ∘ σ)) :
    σ = configurationLexOrder x := by
  have h := Tuple.unique_monotone hσ.monotone (strictMono_configurationLexOrder x).monotone
  apply Equiv.ext
  intro i
  exact configurationLexKey_injective x (congrFun h i)

/-- Distinct actual sites admit exactly one strict lexicographic label order. -/
theorem existsUnique_configurationLexOrder {D n : ℕ} (x : Configuration D n) :
    ∃! σ : Equiv.Perm (Fin n), StrictMono (configurationLexKey x ∘ σ) :=
  ⟨configurationLexOrder x, strictMono_configurationLexOrder x,
    fun σ hσ => configurationLexOrder_unique x σ hσ⟩

/-- The first coordinate distinguishing each consecutive pair of sorted sites. -/
def configurationAdjacentWord {D m : ℕ} (x : Configuration D (m+1)) : Fin m → Fin D :=
  fun i => Classical.choose
    (strictMono_configurationLexOrder x (Fin.castSucc_lt_succ i))

theorem configurationAdjacentWord_prefix {D m : ℕ} (x : Configuration D (m+1))
    (i : Fin m) (k : Fin D) (hk : k < configurationAdjacentWord x i) :
    x.val (configurationLexOrder x i.castSucc) k =
      x.val (configurationLexOrder x i.succ) k :=
  (Classical.choose_spec
    (strictMono_configurationLexOrder x (Fin.castSucc_lt_succ i))).1 k hk

theorem configurationAdjacentWord_lt {D m : ℕ} (x : Configuration D (m+1)) (i : Fin m) :
    x.val (configurationLexOrder x i.castSucc) (configurationAdjacentWord x i) <
      x.val (configurationLexOrder x i.succ) (configurationAdjacentWord x i) :=
  (Classical.choose_spec
    (strictMono_configurationLexOrder x (Fin.castSucc_lt_succ i))).2

/-- A first coordinate with a strict difference is determined by its prefix equalities. -/
theorem firstDifference_unique {D : ℕ} {u v : Space D} {a b : Fin D}
    (ha : ∀ k < a, u k = v k) (hla : u a < v a)
    (hb : ∀ k < b, u k = v k) (hlb : u b < v b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact False.elim (hla.ne (hb a hab))
  · exact hab
  · exact False.elim (hlb.ne (ha b hba))

theorem configurationAdjacentWord_unique {D m : ℕ} (x : Configuration D (m+1))
    (a : Fin m → Fin D)
    (hp : ∀ i k, k < a i → x.val (configurationLexOrder x i.castSucc) k =
      x.val (configurationLexOrder x i.succ) k)
    (hl : ∀ i, x.val (configurationLexOrder x i.castSucc) (a i) <
      x.val (configurationLexOrder x i.succ) (a i)) :
    a = configurationAdjacentWord x := by
  funext i
  exact firstDifference_unique (hp i) (hl i)
    (configurationAdjacentWord_prefix x i) (configurationAdjacentWord_lt x i)

/-- Sorting the actual coordinates gives a point of the corresponding open cone. -/
def configurationGeneralCellParameter {D m : ℕ} (x : Configuration D (m+1)) :
    generalCellOpenDomain (configurationAdjacentWord x) :=
  ⟨⟨fun i => x.val (configurationLexOrder x i),
    fun i k hk => configurationAdjacentWord_prefix x i k hk⟩,
    fun i => sub_pos.mpr (configurationAdjacentWord_lt x i)⟩

/-- An open word chart, with its position-to-label permutation restored. -/
def generalCellRelabelledConfigurationMap {D m : ℕ} (σ : Equiv.Perm (Fin (m+1)))
    (a : Fin m → Fin D) : C(generalCellOpenDomain a, Configuration D (m+1)) where
  toFun p := σ • generalCellConfigurationMap a p
  continuous_toFun := (relabelConfiguration σ).continuous.comp
    (generalCellConfigurationMap a).continuous

@[simp] theorem generalCellRelabelledConfigurationMap_apply {D m : ℕ}
    (σ : Equiv.Perm (Fin (m+1))) (a : Fin m → Fin D) (p : generalCellOpenDomain a)
    (i : Fin (m+1)) :
    (generalCellRelabelledConfigurationMap σ a p).val i = p.val.val (σ.symm i) := rfl

theorem configurationGeneralCellParameter_map {D m : ℕ} (x : Configuration D (m+1)) :
    generalCellRelabelledConfigurationMap (configurationLexOrder x)
      (configurationAdjacentWord x) (configurationGeneralCellParameter x) = x := by
  apply Subtype.ext
  funext i
  change x.val (configurationLexOrder x ((configurationLexOrder x).symm i)) = x.val i
  rw [Equiv.apply_symm_apply]

/-- Every actual configuration lies in a relabelled open general cell. -/
theorem exists_generalCell_chart {D m : ℕ} (x : Configuration D (m+1)) :
    ∃ (σ : Equiv.Perm (Fin (m+1))) (a : Fin m → Fin D) (p : generalCellOpenDomain a),
      generalCellRelabelledConfigurationMap σ a p = x :=
  ⟨configurationLexOrder x, configurationAdjacentWord x,
    configurationGeneralCellParameter x, configurationGeneralCellParameter_map x⟩

theorem strictMono_generalCellConfigurationMap {D m : ℕ} (a : Fin m → Fin D)
    (p : generalCellOpenDomain a) :
    StrictMono (configurationLexKey (generalCellConfigurationMap a p)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine ⟨a i, fun k hk => p.val.property i k hk, ?_⟩
  exact sub_pos.mp (p.property i)

theorem configurationLexOrder_generalCellRelabelledConfigurationMap {D m : ℕ}
    (σ : Equiv.Perm (Fin (m+1))) (a : Fin m → Fin D) (p : generalCellOpenDomain a) :
    configurationLexOrder (generalCellRelabelledConfigurationMap σ a p) = σ := by
  symm
  apply configurationLexOrder_unique
  simpa only [generalCellRelabelledConfigurationMap, ContinuousMap.coe_mk,
    Function.comp_def, configurationLexKey_relabel]
    using strictMono_generalCellConfigurationMap a p

theorem configurationAdjacentWord_generalCellRelabelledConfigurationMap {D m : ℕ}
    (σ : Equiv.Perm (Fin (m+1))) (a : Fin m → Fin D) (p : generalCellOpenDomain a) :
    configurationAdjacentWord (generalCellRelabelledConfigurationMap σ a p) = a := by
  symm
  apply configurationAdjacentWord_unique
  · intro i k hk
    rw [configurationLexOrder_generalCellRelabelledConfigurationMap]
    simpa only [generalCellRelabelledConfigurationMap_apply, Equiv.symm_apply_apply]
      using p.val.property i k hk
  · intro i
    rw [configurationLexOrder_generalCellRelabelledConfigurationMap]
    simpa only [generalCellRelabelledConfigurationMap_apply, Equiv.symm_apply_apply]
      using sub_pos.mp (p.property i)

/-- Equality of interior chart points forces equality of both chart indices. -/
theorem generalCellRelabelledConfigurationMap_indices_unique {D m : ℕ}
    (σ τ : Equiv.Perm (Fin (m+1))) (a b : Fin m → Fin D)
    (p : generalCellOpenDomain a) (q : generalCellOpenDomain b)
    (h : generalCellRelabelledConfigurationMap σ a p =
      generalCellRelabelledConfigurationMap τ b q) : σ = τ ∧ a = b := by
  constructor
  · have he := congrArg configurationLexOrder h
    simpa only [configurationLexOrder_generalCellRelabelledConfigurationMap] using he
  · have he := congrArg configurationAdjacentWord h
    simpa only [configurationAdjacentWord_generalCellRelabelledConfigurationMap] using he

/-- Distinct permutation/word pairs have disjoint open chart images. -/
theorem disjoint_generalCellRelabelledConfigurationMap_range {D m : ℕ}
    (σ τ : Equiv.Perm (Fin (m+1))) (a b : Fin m → Fin D)
    (hne : (σ, a) ≠ (τ, b)) :
    Disjoint (Set.range (generalCellRelabelledConfigurationMap σ a))
      (Set.range (generalCellRelabelledConfigurationMap τ b)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp⟩ ⟨q, hq⟩
  obtain ⟨hσ, ha⟩ := generalCellRelabelledConfigurationMap_indices_unique σ τ a b p q
    (hp.trans hq.symm)
  exact hne (Prod.ext hσ ha)

/-- The actual configuration space is partitioned by its permutation/word charts. -/
theorem existsUnique_generalCell_chart_index {D m : ℕ} (x : Configuration D (m+1)) :
    ∃! c : Equiv.Perm (Fin (m+1)) × (Fin m → Fin D),
      x ∈ Set.range (generalCellRelabelledConfigurationMap c.1 c.2) := by
  refine ⟨(configurationLexOrder x, configurationAdjacentWord x),
    ⟨configurationGeneralCellParameter x, configurationGeneralCellParameter_map x⟩, ?_⟩
  rintro ⟨σ, a⟩ ⟨p, hp⟩
  obtain ⟨hσ, ha⟩ := generalCellRelabelledConfigurationMap_indices_unique σ
    (configurationLexOrder x) a (configurationAdjacentWord x) p
    (configurationGeneralCellParameter x) (hp.trans (configurationGeneralCellParameter_map x).symm)
  exact Prod.ext hσ ha

end NRR.PrimePowerTopology
