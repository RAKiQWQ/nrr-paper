import NRR.PrimePowerTopologyInfinityNeighborhoodAttachments

/-! A genuine good neighborhood of infinity in the one-point
compactification of configuration space times any Euclidean space.
The construction is a finite iteration of explicit disk collars. -/

noncomputable section
set_option maxHeartbeats 1800000
open Set Topology Metric
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- A singleton filtration member has its tautological pointed contraction. -/
def stabilizedFuksZeroInfinityGoodNeighborhood (d m k : ℕ) :
    PointGoodNeighborhood (stabilizedFuksLevel d (m+1) k 0)
      ⟨∞,stabilizedFuksLevel_infty _ _ _ _⟩ := by
  let p : stabilizedFuksLevel d (m+1) k 0 := ⟨∞,stabilizedFuksLevel_infty _ _ _ _⟩
  have he (x : stabilizedFuksLevel d (m+1) k 0) : x = p := by
    apply Subtype.ext
    exact (stabilizedFuksLevel_zero d (m+1) k).subset x.property
  refine {
    neighborhood := univ
    isOpen := isOpen_univ
    mem := mem_univ p
    contraction := {
      toFun := Prod.snd
      continuous_toFun := continuous_snd
      map_zero_left := ?_
      map_one_left := fun _ => rfl }
    fixed := fun _ => rfl }
  intro x
  apply Subtype.ext
  exact he x.val

/-- Every finite compactified Fuks level has a pointed good neighborhood
of the actual common point at infinity. -/
def stabilizedFuksInfinityGoodNeighborhood (d m k r : ℕ) [NeZero m] :
    PointGoodNeighborhood (stabilizedFuksLevel d (m+1) k r)
      ⟨∞,stabilizedFuksLevel_infty _ _ _ _⟩ := by
  induction r with
  | zero => exact stabilizedFuksZeroInfinityGoodNeighborhood d m k
  | succ r ih =>
    exact InfinityCollar.extend (stabilizedFuksFiniteAttachment d m k r)
      (ih.homeomorph (stabilizedFuksLowerHomeomorph d m k r))

def stabilizedFuksTopHomeomorph (d m k : ℕ) :
    stabilizedFuksLevel d (m+1) k (d*(m+1)+1) ≃ₜ
      OnePoint (Configuration (d+1) (m+1) × Space k) where
  toFun := Subtype.val
  invFun p := ⟨p,by rw [stabilizedFuksLevel_top]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- An actual open neighborhood of infinity contracts to infinity while
fixing infinity, with no positive-dimensional condition on `Space k`.
There are `m+1 ≥ 2` labelled sites in `d+1 ≥ 1` ambient coordinates. -/
def configurationProductInfinityGoodNeighborhood (d m k : ℕ) [NeZero m] :
    PointGoodNeighborhood (OnePoint (Configuration (d+1) (m+1) × Space k)) ∞ :=
  (stabilizedFuksInfinityGoodNeighborhood d m k (d*(m+1)+1)).homeomorph
    (stabilizedFuksTopHomeomorph d m k)

/-- The existing good-pair interface needed by collapse and ordinary
suspension comparisons, for the actual configuration compactification. -/
def configurationProductInfinityNeighborhoodDeformation (d m k : ℕ) [NeZero m] :
    NeighborhoodDeformation ({∞} : Set (OnePoint (Configuration (d+1) (m+1) × Space k)))
      (configurationProductInfinityGoodNeighborhood d m k).neighborhood :=
  (configurationProductInfinityGoodNeighborhood d m k).deformation

theorem exists_configurationProductInfinityGoodNeighborhood (d m k : ℕ) [NeZero m] :
    ∃ U : Set (OnePoint (Configuration (d+1) (m+1) × Space k)),
      IsOpen U ∧ (∞ : OnePoint (Configuration (d+1) (m+1) × Space k)) ∈ U ∧
      Nonempty (NeighborhoodDeformation {∞} U) :=
  ⟨_,(configurationProductInfinityGoodNeighborhood d m k).isOpen,
    (configurationProductInfinityGoodNeighborhood d m k).mem,
    ⟨configurationProductInfinityNeighborhoodDeformation d m k⟩⟩

/-- The same concrete construction with the ambient dimension and number
of sites written without successor indexing. -/
def configurationSpaceProductInfinityGoodNeighborhood (d n k : ℕ)
    (hd : 0 < d) (hn : 2 ≤ n) :
    PointGoodNeighborhood (OnePoint (Configuration d n × Space k)) ∞ := by
  cases d with
  | zero => omega
  | succ d =>
    cases n with
    | zero => omega
    | succ n =>
      have hn0 : n ≠ 0 := by omega
      letI : NeZero n := ⟨hn0⟩
      exact configurationProductInfinityGoodNeighborhood d n k

theorem exists_configurationSpaceProductInfinityGoodNeighborhood (d n k : ℕ)
    (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ U : Set (OnePoint (Configuration d n × Space k)),
      IsOpen U ∧ (∞ : OnePoint (Configuration d n × Space k)) ∈ U ∧
      Nonempty (NeighborhoodDeformation {∞} U) := by
  let G := configurationSpaceProductInfinityGoodNeighborhood d n k hd hn
  exact ⟨G.neighborhood,G.isOpen,G.mem,⟨G.deformation⟩⟩

def configurationZeroSpaceHomeomorph (d n : ℕ) :
    (Configuration d n × Space 0) ≃ₜ Configuration d n where
  toFun := Prod.fst
  invFun x := (x,0)
  left_inv x := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

/-- In particular, the unstabilized configuration compactification itself
has the required actual pointed neighborhood; no positive suspension
coordinate is used to obtain it. -/
def configurationInfinityGoodNeighborhood (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    PointGoodNeighborhood (OnePoint (Configuration d n)) ∞ :=
  (configurationSpaceProductInfinityGoodNeighborhood d n 0 hd hn).homeomorph
    (configurationZeroSpaceHomeomorph d n).onePointCongr

def configurationInfinityNeighborhoodDeformation (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    NeighborhoodDeformation ({∞} : Set (OnePoint (Configuration d n)))
      (configurationInfinityGoodNeighborhood d n hd hn).neighborhood :=
  (configurationInfinityGoodNeighborhood d n hd hn).deformation

end NRR.PrimePowerTopology
