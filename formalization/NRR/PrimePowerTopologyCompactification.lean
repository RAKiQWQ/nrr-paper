import NRR.PrimePowerTopologyCells

/-! Collision faces really escape to the point at infinity of configuration
space. This is the continuous collapse used for actual Fuks attaching maps,
rather than an assumption that formal shuffle faces are topological cells. -/

noncomputable section
open Set Topology Filter
open scoped OnePoint
open NRR.PrimePower

namespace NRR.PrimePowerTopology

section OpenCollapse

variable {X : Type*} [TopologicalSpace X] [T2Space X] (S : Set X)

def openCollapse (x : X) : OnePoint S := by
  classical
  exact if h : x ∈ S then ((⟨x,h⟩ : S) : OnePoint S) else ∞

@[simp] theorem openCollapse_of_mem {x : X} (hx : x ∈ S) :
    openCollapse S x = ((⟨x,hx⟩ : S) : OnePoint S) := by simp [openCollapse,hx]

@[simp] theorem openCollapse_of_not_mem {x : X} (hx : x ∉ S) :
    openCollapse S x = ∞ := by simp [openCollapse,hx]

/-- An open subspace has a genuine continuous collapse from its ambient
Hausdorff space: its entire complement is sent to infinity. -/
theorem continuous_openCollapse (hS : IsOpen S) : Continuous (openCollapse S) := by
  classical
  apply continuous_def.mpr
  intro U hU
  by_cases hi : (∞ : OnePoint S) ∈ U
  · have compact : IsCompact (((↑) : S → OnePoint S) ⁻¹' U)ᶜ := hU.1 hi
    have repr : openCollapse S ⁻¹' U =
        (Subtype.val '' ((((↑) : S → OnePoint S) ⁻¹' U)ᶜ))ᶜ := by
      ext x
      by_cases hx : x ∈ S
      · simp only [mem_preimage,openCollapse_of_mem S hx,mem_compl_iff,mem_image]
        constructor
        · intro hu ⟨y,hy,he⟩
          have eq : y = (⟨x,hx⟩ : S) := Subtype.ext he
          exact hy (eq.symm ▸ hu)
        · intro hu
          by_contra hn
          exact hu ⟨⟨x,hx⟩,hn,rfl⟩
      · simp only [mem_preimage,openCollapse_of_not_mem S hx,hi,true_iff,mem_compl_iff,mem_image]
        rintro ⟨y,_,rfl⟩
        exact hx y.property
    rw [repr]
    exact (compact.image continuous_subtype_val).isClosed.isOpen_compl
  · have repr : openCollapse S ⁻¹' U =
        Subtype.val '' (((↑) : S → OnePoint S) ⁻¹' U) := by
      ext x
      by_cases hx : x ∈ S
      · simp only [mem_preimage,openCollapse_of_mem S hx,mem_image]
        exact ⟨fun hu => ⟨⟨x,hx⟩,hu,rfl⟩,by rintro ⟨y,hy,he⟩; subst x; exact hy⟩
      · simp only [mem_preimage,openCollapse_of_not_mem S hx,hi,false_iff,mem_image]
        rintro ⟨y,_,rfl⟩
        exact hx y.property
    rw [repr]
    exact hS.isOpenMap_subtype_val _ hU.2

theorem tendsto_cocompact_of_subtype_limit_not_mem {α : Type*} {l : Filter α}
    (x : α → S) {a : X} (outside : a ∉ S)
    (limit : Tendsto (fun t => (x t).val) l (𝓝 a)) :
    Tendsto x l (cocompact S) := by
  apply hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  have closed := (hK.image continuous_subtype_val).isClosed
  have avoid : a ∈ (Subtype.val '' K)ᶜ := by
    rintro ⟨y,_,rfl⟩
    exact outside y.property
  filter_upwards [limit (closed.isOpen_compl.mem_nhds avoid)] with t ht
  intro hx
  exact ht ⟨x t,hx,rfl⟩

theorem tendsto_infty_of_subtype_limit_not_mem {α : Type*} {l : Filter α}
    (x : α → S) {a : X} (outside : a ∉ S)
    (limit : Tendsto (fun t => (x t).val) l (𝓝 a)) :
    Tendsto (fun t => ((x t) : OnePoint S)) l (𝓝 ∞) := by
  apply OnePoint.tendsto_coe_infty.comp
  rw [coclosedCompact_eq_cocompact]
  exact tendsto_cocompact_of_subtype_limit_not_mem S x outside limit

end OpenCollapse

theorem isOpen_injectiveSites (d n : ℕ) :
    IsOpen {x : Fin n → Space d | Function.Injective x} := by
  have repr : {x : Fin n → Space d | Function.Injective x} =
      ⋂ i : Fin n,⋂ j : Fin n,{x | i ≠ j → x i ≠ x j} := by
    ext x
    simp only [mem_setOf_eq,mem_iInter,Function.Injective]
    constructor
    · intro h i j hij he
      exact hij (h he)
    · intro h i j he
      by_contra hij
      exact h i j hij he
  rw [repr]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp only [hij,ne_eq,not_true_eq_false,false_implies,setOf_true,isOpen_univ]
  · simpa only [hij,ne_eq,not_false_eq_true,true_implies] using
      (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl

instance configurationLocallyCompact (d n : ℕ) : LocallyCompactSpace (Configuration d n) :=
  (isOpen_injectiveSites d n).locallyCompactSpace

def configurationCollapse (d n : ℕ) : C((Fin n → Space d),OnePoint (Configuration d n)) :=
  ⟨openCollapse {x | Function.Injective x},continuous_openCollapse _ (isOpen_injectiveSites d n)⟩

@[simp] theorem configurationCollapse_injective {d n : ℕ} (x : Fin n → Space d)
    (hx : Function.Injective x) :
    configurationCollapse d n x = ((⟨x,hx⟩ : Configuration d n) : OnePoint (Configuration d n)) :=
  openCollapse_of_mem _ hx

@[simp] theorem configurationCollapse_collision {d n : ℕ} (x : Fin n → Space d)
    (hx : ¬ Function.Injective x) : configurationCollapse d n x = ∞ :=
  openCollapse_of_not_mem _ hx

theorem collision_tendsto_cocompact {α : Type*} {l : Filter α} {d n : ℕ}
    (x : α → Configuration d n) {a : Fin n → Space d} (collision : ¬ Function.Injective a)
    (limit : Tendsto (fun t => (x t).val) l (𝓝 a)) :
    Tendsto x l (cocompact (Configuration d n)) :=
  tendsto_cocompact_of_subtype_limit_not_mem _ x collision limit

theorem collision_tendsto_infty {α : Type*} {l : Filter α} {d n : ℕ}
    (x : α → Configuration d n) {a : Fin n → Space d} (collision : ¬ Function.Injective a)
    (limit : Tendsto (fun t => (x t).val) l (𝓝 a)) :
    Tendsto (fun t => ((x t) : OnePoint (Configuration d n))) l (𝓝 ∞) :=
  tendsto_infty_of_subtype_limit_not_mem _ x collision limit

end NRR.PrimePowerTopology
