import NRR.SingularHomologyBMSuspensionProper
import NRR.PrimePowerTopologyInfinityNeighborhoodCore
import NRR.TopologyPort.Suspension

/-! The geometric unreduced suspension, its canonical caps and infinity arc. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
open Set Topology CategoryTheory Limits AlgebraicTopology unitInterval
open NRR.PrimePowerTopology NRR.SuspensionGeometry
open scoped OnePoint

namespace NRR.SingularHomology
namespace RealSuspension
variable {K : Type} [TopologicalSpace K]

def lower : Set (Susp K) := {z | (Susp.height z : ℝ) < 1}
def upper : Set (Susp K) := {z | 0 < (Susp.height z : ℝ)}

theorem lower_open : IsOpen (lower (K := K)) :=
  isOpen_lt (continuous_subtype_val.comp Susp.height.continuous) continuous_const
theorem upper_open : IsOpen (upper (K := K)) :=
  isOpen_lt continuous_const (continuous_subtype_val.comp Susp.height.continuous)

private def lowerCylinderMotion : C(I × (Susp.mk ⁻¹' lower (K := K)),lower (K := K)) :=
  ⟨fun p => ⟨Susp.mk (p.1 * p.2.val.1,p.2.val.2),by
    change (p.1 : ℝ) * (p.2.val.1 : ℝ) < 1
    calc
      (p.1 : ℝ) * (p.2.val.1 : ℝ) ≤ p.2.val.1 :=
        mul_le_of_le_one_left p.2.val.1.property.1 p.1.property.2
      _ < 1 := p.2.property⟩,by
    apply Continuous.subtype_mk
    apply Susp.mk.continuous.comp
    apply Continuous.prodMk _ (continuous_subtype_val.comp continuous_snd).snd
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd).fst)⟩

private theorem lowerCylinderMotion_fiber (s : I)
    (a b : Susp.mk ⁻¹' lower (K := K))
    (h : Susp.restrictMk lower a = Susp.restrictMk lower b) :
    lowerCylinderMotion (s,a) = lowerCylinderMotion (s,b) := by
  apply Subtype.ext
  rcases Susp.mk_eq_mk.mp (congrArg Subtype.val h) with he | ⟨ha,hb⟩ | ⟨ha,_⟩
  · exact congrArg (fun p : I × K => Susp.mk (s * p.1,p.2)) he
  · change Susp.mk (s * a.val.1,a.val.2) = Susp.mk (s * b.val.1,b.val.2)
    rw [ha,hb,mul_zero]
    exact Susp.mk_zero_eq_mk_zero _ _
  · have hh := a.property
    change (a.val.1 : ℝ) < 1 at hh
    rw [ha] at hh
    norm_num at hh

def lowerMotion : C(I × lower (K := K),lower (K := K)) :=
  quotientLiftParam (Susp.restrictMk lower) (Susp.quotient_restrictMk _ lower_open)
    lowerCylinderMotion lowerCylinderMotion_fiber

@[simp] theorem lowerMotion_mk (s t : I) (x : K)
    (ht : (t : ℝ) < 1) :
    (lowerMotion (s,⟨Susp.mk (t,x),ht⟩)).val = Susp.mk (s*t,x) := by
  exact congrArg Subtype.val (quotientLiftParam_apply (Susp.restrictMk lower)
    (Susp.quotient_restrictMk _ lower_open) lowerCylinderMotion lowerCylinderMotion_fiber
    s (⟨(t,x),ht⟩ : Susp.mk ⁻¹' lower))

def lowerContraction [Nonempty K] :
    (ContinuousMap.const lower (⟨Susp.south K,by
      change (Susp.height (Susp.mk (0,Classical.arbitrary K)) : ℝ) < 1
      norm_num⟩ : lower (K := K))).Homotopy (ContinuousMap.id lower) where
  toFun := lowerMotion
  continuous_toFun := lowerMotion.continuous
  map_zero_left := by
    intro z
    obtain ⟨p,hp⟩ := (Susp.quotient_restrictMk _ lower_open).surjective z
    rw [← hp]
    apply Subtype.ext
    change (lowerMotion (0,⟨Susp.mk (p.val.1,p.val.2),p.property⟩)).val = Susp.south K
    rw [lowerMotion_mk]
    simp only [zero_mul]
    exact Susp.mk_zero _
  map_one_left := by
    intro z
    obtain ⟨p,hp⟩ := (Susp.quotient_restrictMk _ lower_open).surjective z
    rw [← hp]
    apply Subtype.ext
    change (lowerMotion (1,⟨Susp.mk (p.val.1,p.val.2),p.property⟩)).val = Susp.mk p.val
    rw [lowerMotion_mk,one_mul]

theorem lower_contractible [Nonempty K] : ContractibleSpace (lower (K := K)) := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨_,⟨(lowerContraction (K := K)).symm⟩⟩

def lowerToUpper : C(lower (K := K),upper (K := K)) :=
  ⟨fun z => ⟨Susp.reflect z.val,by
    change 0 < (Susp.height (Susp.reflect z.val) : ℝ)
    rw [Susp.height_reflect]
    change 0 < 1 - (Susp.height z.val : ℝ)
    have hz : (Susp.height z.val : ℝ) < 1 := z.property
    linarith⟩,by
    apply Continuous.subtype_mk
    exact Susp.reflect.continuous.comp continuous_subtype_val⟩

def upperToLower : C(upper (K := K),lower (K := K)) :=
  ⟨fun z => ⟨Susp.reflect z.val,by
    change (Susp.height (Susp.reflect z.val) : ℝ) < 1
    rw [Susp.height_reflect]
    change 1 - (Susp.height z.val : ℝ) < 1
    have hz : 0 < (Susp.height z.val : ℝ) := z.property
    linarith⟩,by
    apply Continuous.subtype_mk
    exact Susp.reflect.continuous.comp continuous_subtype_val⟩

def capReflection : lower (K := K) ≃ₜ upper (K := K) where
  toFun := lowerToUpper
  invFun := upperToLower
  left_inv z := Subtype.ext (Susp.reflect_reflect _)
  right_inv z := Subtype.ext (Susp.reflect_reflect _)
  continuous_toFun := lowerToUpper.continuous
  continuous_invFun := upperToLower.continuous

theorem upper_contractible [Nonempty K] : ContractibleSpace (upper (K := K)) := by
  letI := lower_contractible (K := K)
  exact (capReflection (K := K)).symm.contractibleSpace

def interiorLevels : Set I := Ioo 0 1

theorem interiorLevels_open : IsOpen interiorLevels := isOpen_Ioo
theorem zero_not_interiorLevels : (0 : I) ∉ interiorLevels := by simp [interiorLevels]
theorem one_not_interiorLevels : (1 : I) ∉ interiorLevels := by simp [interiorLevels]

def levelHomeomorph : interiorLevels ≃ₜ Ioo (0 : ℝ) 1 where
  toFun t := ⟨t.val.val,t.property⟩
  invFun t := ⟨⟨t.val,le_of_lt t.property.1,le_of_lt t.property.2⟩,t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance interiorLevels_contractible : ContractibleSpace interiorLevels := by
  letI : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1/2,by norm_num⟩
  exact levelHomeomorph.contractibleSpace

def overlapCoordinates : (lower ∩ upper : Set (Susp K)) ≃ₜ interiorLevels × K :=
  (Homeomorph.setCongr (by
    ext z
    change ((Susp.height z : ℝ) < 1 ∧ 0 < (Susp.height z : ℝ)) ↔
      (0 < Susp.height z ∧ Susp.height z < 1)
    exact and_comm)).trans
    (Susp.bandCoordinates interiorLevels interiorLevels_open zero_not_interiorLevels
      one_not_interiorLevels)

/-- The forward overlap equivalence is literally the projection to the base. -/
def productProjection : ContinuousMap.HomotopyEquiv (interiorLevels × K) K :=
  ((Homeomorph.prodComm interiorLevels K).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl K).prodCongr
      (ContractibleSpace.hequiv_unit interiorLevels).some)).trans
    (Homeomorph.prodUnique K Unit).toHomotopyEquiv

@[simp] theorem productProjection_apply (p : interiorLevels × K) : productProjection p = p.2 := rfl

def cover [Nonempty K] : SuspensionCover (Susp K) K where
  lower := lower
  upper := upper
  cover := by
    rw [lower_open.interior_eq,upper_open.interior_eq]
    apply Set.eq_univ_of_forall
    intro z
    by_cases h : (Susp.height z : ℝ) < 1
    · exact Or.inl h
    · exact Or.inr (by
        change 0 < (Susp.height z : ℝ)
        linarith [Susp.height z |>.property.2])
  lower_contractible := lower_contractible
  upper_contractible := upper_contractible
  overlap := overlapCoordinates.toHomotopyEquiv.trans productProjection

@[simp] theorem overlap_mk [Nonempty K] (t : I) (x : K)
    (ht : (Susp.mk (t,x) : Susp K) ∈ lower ∩ upper) :
    (cover (K := K)).overlap ⟨Susp.mk (t,x),ht⟩ = x := by
  change (overlapCoordinates (K := K) ⟨Susp.mk (t,x),ht⟩).2 = x
  exact congrArg Prod.snd (Susp.bandCoordinates_mk interiorLevels interiorLevels_open
    zero_not_interiorLevels one_not_interiorLevels t x ⟨ht.2,ht.1⟩)

variable {L : Type} [TopologicalSpace L] [Nonempty K] [Nonempty L]

def map (f : C(K,L)) : (cover (K := K)).Map (cover (K := L)) where
  total := TopCat.ofHom (Susp.map f)
  base := TopCat.ofHom f
  lower := by
    intro z hz
    change (Susp.height (Susp.map f z) : ℝ) < 1
    simpa using hz
  upper := by
    intro z hz
    change 0 < (Susp.height (Susp.map f z) : ℝ)
    simpa using hz
  overlap := by
    ext z
    rcases z with ⟨z,hz⟩
    obtain ⟨⟨t,x⟩,rfl⟩ := Susp.mk_surjective z
    change (cover (K := L)).overlap ⟨Susp.mk (t,f x),_⟩ =
      f ((cover (K := K)).overlap ⟨Susp.mk (t,x),hz⟩)
    rw [overlap_mk,overlap_mk]

def reversingMap (f : C(K,L)) : (cover (K := K)).ReversingMap (cover (K := L)) where
  total := TopCat.ofHom (Susp.reflect.comp (Susp.map f))
  base := TopCat.ofHom f
  lower := by
    intro z hz
    change 0 < (Susp.height (Susp.reflect (Susp.map f z)) : ℝ)
    rw [Susp.height_reflect,Susp.height_map]
    change 0 < 1 - (Susp.height z : ℝ)
    have hh : (Susp.height z : ℝ) < 1 := hz
    linarith
  upper := by
    intro z hz
    change (Susp.height (Susp.reflect (Susp.map f z)) : ℝ) < 1
    rw [Susp.height_reflect,Susp.height_map]
    change 1 - (Susp.height z : ℝ) < 1
    have hh : 0 < (Susp.height z : ℝ) := hz
    linarith
  overlap := by
    ext z
    rcases z with ⟨z,hz⟩
    obtain ⟨⟨t,x⟩,rfl⟩ := Susp.mk_surjective z
    change (cover (K := L)).overlap ⟨Susp.mk (σ t,f x),_⟩ =
      f ((cover (K := K)).overlap ⟨Susp.mk (t,x),hz⟩)
    rw [overlap_mk,overlap_mk]

end RealSuspension

namespace SuspensionArc
variable {K : Type} [TopologicalSpace K] {p : K}

def cylinder (U : Set K) : Set (I × K) :=
  {z | (z.1 : ℝ) < 1/4 ∨ 3/4 < (z.1 : ℝ) ∨ z.2 ∈ U}

def neighborhood (U : Set K) : Set (Susp K) := Susp.mk '' cylinder U

theorem preimage_neighborhood (U : Set K) :
    Susp.mk ⁻¹' neighborhood U = cylinder U := by
  ext a
  constructor
  · rintro ⟨b,hb,he⟩
    rcases Susp.mk_eq_mk.mp he with h | ⟨_,ha⟩ | ⟨_,ha⟩
    · exact h ▸ hb
    · left; change (a.1 : ℝ) < 1/4; rw [ha]; norm_num
    · right; left; change (3:ℝ)/4 < (a.1 : ℝ); rw [ha]; norm_num
  · intro ha; exact ⟨a,ha,rfl⟩

@[simp] theorem mk_mem_neighborhood (U : Set K) (t : I) (x : K) :
    Susp.mk (t,x) ∈ neighborhood U ↔ (t : ℝ) < 1/4 ∨ 3/4 < (t : ℝ) ∨ x ∈ U := by
  change (t,x) ∈ Susp.mk ⁻¹' neighborhood U ↔ _
  rw [preimage_neighborhood]
  rfl

theorem neighborhood_open (U : Set K) (hU : IsOpen U) : IsOpen (neighborhood U) := by
  apply Susp.isQuotientMap_mk.isOpen_preimage.mp
  rw [preimage_neighborhood]
  exact (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).union
    ((isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).union
      (hU.preimage continuous_snd))

theorem arc_subset (U : Set K) (hp : p ∈ U) : Susp.arc p ⊆ neighborhood U := by
  rintro _ ⟨t,rfl⟩
  exact (mk_mem_neighborhood U t p).mpr (Or.inr (Or.inr hp))

/-- A fixed-width collar pushes both caps to their poles. -/
def clamp : C(I,I) :=
  ⟨fun t => ⟨min 1 (max 0 (2*(t:ℝ)-1/2)),by
      constructor
      · exact le_min (by norm_num) (le_max_left _ _)
      · exact min_le_left _ _⟩,by
    apply Continuous.subtype_mk
    fun_prop⟩

theorem clamp_zero_of_le (t : I) (ht : (t : ℝ) ≤ 1/4) : clamp t = 0 := by
  apply Subtype.ext
  change min 1 (max 0 (2*(t:ℝ)-1/2)) = 0
  rw [max_eq_left (by linarith)]
  norm_num

theorem clamp_one_of_le (t : I) (ht : (3:ℝ)/4 ≤ t) : clamp t = 1 := by
  apply Subtype.ext
  change min 1 (max 0 (2*(t:ℝ)-1/2)) = 1
  apply min_eq_left
  exact le_trans (by linarith) (le_max_right _ _)

@[simp] theorem clamp_zero : clamp 0 = 0 := clamp_zero_of_le _ (by norm_num)
@[simp] theorem clamp_one : clamp 1 = 1 := clamp_one_of_le _ (by norm_num)

/-- The linear motion from a clamped level to its original level. -/
def unclampLevel : C(I × I,I) :=
  ⟨fun z => ⟨(z.1 : ℝ)*(z.2 : ℝ)+(1-z.1)*(clamp z.2 : ℝ),by
      have hs := z.1.property
      have ht := z.2.property
      have hg := (clamp z.2).property
      constructor
      · exact add_nonneg (mul_nonneg hs.1 ht.1)
          (mul_nonneg (sub_nonneg.mpr hs.2) hg.1)
      · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hg.2),
          mul_nonneg hs.1 (sub_nonneg.mpr ht.2)]⟩,by
    apply Continuous.subtype_mk
    fun_prop⟩

@[simp] theorem unclampLevel_zero (t : I) : unclampLevel (0,t) = clamp t := by
  apply Subtype.ext
  simp [unclampLevel]
@[simp] theorem unclampLevel_one (t : I) : unclampLevel (1,t) = t := by
  apply Subtype.ext
  simp [unclampLevel]
@[simp] theorem unclampLevel_bottom (s : I) : unclampLevel (s,0) = 0 := by
  apply Subtype.ext
  simp [unclampLevel]
@[simp] theorem unclampLevel_top (s : I) : unclampLevel (s,1) = 1 := by
  apply Subtype.ext
  simp [unclampLevel]

theorem unclampLevel_lower (s t : I) (ht : (t : ℝ) < 1/4) :
    (unclampLevel (s,t) : ℝ) < 1/4 := by
  change (s : ℝ)*(t : ℝ)+(1-s)*(clamp t : ℝ) < 1/4
  rw [clamp_zero_of_le t ht.le]
  change (s : ℝ)*(t : ℝ)+(1-s)*0 < 1/4
  simp only [mul_zero,add_zero]
  exact (mul_le_of_le_one_left t.property.1 s.property.2).trans_lt ht

theorem unclampLevel_upper (s t : I) (ht : (3:ℝ)/4 < t) :
    (3:ℝ)/4 < unclampLevel (s,t) := by
  change (3:ℝ)/4 < (s : ℝ)*(t : ℝ)+(1-s)*(clamp t : ℝ)
  rw [clamp_one_of_le t ht.le]
  change (3:ℝ)/4 < (s : ℝ)*(t : ℝ)+(1-s)*1
  simp only [mul_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr t.property.2)]

private def unclampCylinder (U : Set K) :
    C(I × (Susp.mk ⁻¹' neighborhood U),neighborhood U) :=
  ⟨fun z => ⟨Susp.mk (unclampLevel (z.1,z.2.val.1),z.2.val.2),by
    apply (mk_mem_neighborhood _ _ _).mpr
    rcases (mk_mem_neighborhood U _ _).mp z.2.property with ht | ht | hx
    · exact Or.inl (unclampLevel_lower _ _ ht)
    · exact Or.inr (Or.inl (unclampLevel_upper _ _ ht))
    · exact Or.inr (Or.inr hx)⟩,by
    apply Continuous.subtype_mk
    apply Susp.mk.continuous.comp
    exact (unclampLevel.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd).fst)).prodMk
      (continuous_subtype_val.comp continuous_snd).snd⟩

private theorem unclampCylinder_fiber (U : Set K) (s : I)
    (a b : Susp.mk ⁻¹' neighborhood U)
    (h : Susp.restrictMk (neighborhood U) a = Susp.restrictMk (neighborhood U) b) :
    unclampCylinder U (s,a) = unclampCylinder U (s,b) := by
  apply Subtype.ext
  rcases Susp.mk_eq_mk.mp (congrArg Subtype.val h) with he | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact congrArg (fun z : I × K => Susp.mk (unclampLevel (s,z.1),z.2)) he
  · change Susp.mk (unclampLevel (s,a.val.1),a.val.2) =
      Susp.mk (unclampLevel (s,b.val.1),b.val.2)
    rw [ha,hb,unclampLevel_bottom]
    exact Susp.mk_zero_eq_mk_zero _ _
  · change Susp.mk (unclampLevel (s,a.val.1),a.val.2) =
      Susp.mk (unclampLevel (s,b.val.1),b.val.2)
    rw [ha,hb,unclampLevel_top]
    exact Susp.mk_one_eq_mk_one _ _

def unclampMotion (U : Set K) (hU : IsOpen U) : C(I × neighborhood U,neighborhood U) :=
  quotientLiftParam (Susp.restrictMk (neighborhood U))
    (Susp.quotient_restrictMk _ (neighborhood_open _ hU))
    (unclampCylinder U) (unclampCylinder_fiber U)

@[simp] theorem unclampMotion_mk (U : Set K) (hU : IsOpen U) (s t : I) (x : K)
    (ht : Susp.mk (t,x) ∈ neighborhood U) :
    (unclampMotion U hU (s,⟨Susp.mk (t,x),ht⟩)).val =
      Susp.mk (unclampLevel (s,t),x) :=
  congrArg Subtype.val (quotientLiftParam_apply (Susp.restrictMk (neighborhood U))
    (Susp.quotient_restrictMk _ (neighborhood_open _ hU))
    (unclampCylinder U) (unclampCylinder_fiber U) s ⟨(t,x),ht⟩)

variable (G : PointGoodNeighborhood K p)

private def contractCylinderFun (z : I × (Susp.mk ⁻¹' neighborhood G.neighborhood)) : Susp K :=
  if hx : z.2.val.2 ∈ G.neighborhood then
    Susp.mk (clamp z.2.val.1,(G.contraction (z.1,⟨z.2.val.2,hx⟩)).val)
  else Susp.mk (clamp z.2.val.1,z.2.val.2)

private theorem contractCylinderFun_lower (z : I × (Susp.mk ⁻¹' neighborhood G.neighborhood))
    (ht : (z.2.val.1 : ℝ) < 1/4) :
    contractCylinderFun G z = Susp.mk (0,p) := by
  unfold contractCylinderFun
  rw [clamp_zero_of_le _ ht.le]
  split_ifs <;> exact Susp.mk_zero_eq_mk_zero _ _

private theorem contractCylinderFun_upper (z : I × (Susp.mk ⁻¹' neighborhood G.neighborhood))
    (ht : (3:ℝ)/4 < z.2.val.1) :
    contractCylinderFun G z = Susp.mk (1,p) := by
  unfold contractCylinderFun
  rw [clamp_one_of_le _ ht.le]
  split_ifs <;> exact Susp.mk_one_eq_mk_one _ _

private theorem continuous_contractCylinderFun : Continuous (contractCylinderFun G) := by
  let S0 : Set (I × (Susp.mk ⁻¹' neighborhood G.neighborhood)) := {z | (z.2.val.1 : ℝ) < 1/4}
  let S1 : Set (I × (Susp.mk ⁻¹' neighborhood G.neighborhood)) := {z | (3:ℝ)/4 < z.2.val.1}
  let S2 : Set (I × (Susp.mk ⁻¹' neighborhood G.neighborhood)) := {z | z.2.val.2 ∈ G.neighborhood}
  have h0 : IsOpen S0 := isOpen_lt (by fun_prop) continuous_const
  have h1 : IsOpen S1 := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen S2 := G.isOpen.preimage (by fun_prop)
  have hc0 : ContinuousOn (contractCylinderFun G) S0 := by
    apply continuousOn_iff_continuous_restrict.mpr
    have he : S0.restrict (contractCylinderFun G) = fun _ => Susp.mk (0,p) :=
      funext fun z => contractCylinderFun_lower G z.val z.property
    rw [he]
    exact continuous_const
  have hc1 : ContinuousOn (contractCylinderFun G) S1 := by
    apply continuousOn_iff_continuous_restrict.mpr
    have he : S1.restrict (contractCylinderFun G) = fun _ => Susp.mk (1,p) :=
      funext fun z => contractCylinderFun_upper G z.val z.property
    rw [he]
    exact continuous_const
  have hc2 : ContinuousOn (contractCylinderFun G) S2 := by
    apply continuousOn_iff_continuous_restrict.mpr
    let b : C(S2,I × G.neighborhood) :=
      ⟨fun z => (z.val.1,⟨z.val.2.val.2,z.property⟩),by fun_prop⟩
    let f : C(S2,Susp K) :=
      ⟨fun z => Susp.mk (clamp z.val.2.val.1,(G.contraction (b z)).val),
        Susp.mk.continuous.comp ((clamp.continuous.comp (by fun_prop)).prodMk
          (continuous_subtype_val.comp (G.contraction.continuous.comp b.continuous)))⟩
    have he : S2.restrict (contractCylinderFun G) = f := by
      funext z
      exact dif_pos z.property
    rw [he]
    exact f.continuous
  have hc := hc0.union_of_isOpen (hc1.union_of_isOpen hc2 h1 h2) h0 (h1.union h2)
  have he : S0 ∪ (S1 ∪ S2) = univ := by
    apply eq_univ_of_forall
    intro z
    exact (mk_mem_neighborhood G.neighborhood _ _).mp z.2.property
  rw [he] at hc
  exact continuousOn_univ.mp hc

private theorem contractCylinderFun_mem (z : I × (Susp.mk ⁻¹' neighborhood G.neighborhood)) :
    contractCylinderFun G z ∈ neighborhood G.neighborhood := by
  by_cases hx : z.2.val.2 ∈ G.neighborhood
  · unfold contractCylinderFun
    rw [dif_pos hx]
    exact (mk_mem_neighborhood _ _ _).mpr (Or.inr (Or.inr (G.contraction _).property))
  · rcases (mk_mem_neighborhood G.neighborhood _ _).mp z.2.property with ht | ht | hx'
    · rw [contractCylinderFun_lower G z ht]
      exact (mk_mem_neighborhood _ _ _).mpr (Or.inl (by norm_num))
    · rw [contractCylinderFun_upper G z ht]
      exact (mk_mem_neighborhood _ _ _).mpr (Or.inr (Or.inl (by norm_num)))
    · exact (hx hx').elim

private def contractCylinder :
    C(I × (Susp.mk ⁻¹' neighborhood G.neighborhood),neighborhood G.neighborhood) :=
  ⟨fun z => ⟨contractCylinderFun G z,contractCylinderFun_mem G z⟩,
    (continuous_contractCylinderFun G).subtype_mk _⟩

private theorem contractCylinder_fiber (s : I)
    (a b : Susp.mk ⁻¹' neighborhood G.neighborhood)
    (h : Susp.restrictMk (neighborhood G.neighborhood) a =
      Susp.restrictMk (neighborhood G.neighborhood) b) :
    contractCylinder G (s,a) = contractCylinder G (s,b) := by
  apply Subtype.ext
  rcases Susp.mk_eq_mk.mp (congrArg Subtype.val h) with he | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have he' : a = b := Subtype.ext he
    rw [he']
  · exact (contractCylinderFun_lower G (s,a) (by rw [ha]; norm_num)).trans
      (contractCylinderFun_lower G (s,b) (by rw [hb]; norm_num)).symm
  · exact (contractCylinderFun_upper G (s,a) (by rw [ha]; norm_num)).trans
      (contractCylinderFun_upper G (s,b) (by rw [hb]; norm_num)).symm

def contractMotion : C(I × neighborhood G.neighborhood,neighborhood G.neighborhood) :=
  quotientLiftParam (Susp.restrictMk (neighborhood G.neighborhood))
    (Susp.quotient_restrictMk _ (neighborhood_open _ G.isOpen))
    (contractCylinder G) (contractCylinder_fiber G)

@[simp] theorem contractMotion_mk (s t : I) (x : K)
    (ht : Susp.mk (t,x) ∈ neighborhood G.neighborhood) :
    (contractMotion G (s,⟨Susp.mk (t,x),ht⟩)).val =
      contractCylinderFun G (s,⟨(t,x),ht⟩) :=
  congrArg Subtype.val (quotientLiftParam_apply (Susp.restrictMk (neighborhood G.neighborhood))
    (Susp.quotient_restrictMk _ (neighborhood_open _ G.isOpen))
    (contractCylinder G) (contractCylinder_fiber G) s ⟨(t,x),ht⟩)

theorem contractMotion_zero (z : neighborhood G.neighborhood) :
    (contractMotion G (0,z)).val = Susp.mk (clamp (Susp.height z.val),p) := by
  obtain ⟨⟨⟨t,x⟩,ht⟩,hz⟩ := (Susp.quotient_restrictMk _ (neighborhood_open _ G.isOpen)).surjective z
  rw [← hz]
  change (contractMotion G (0,⟨Susp.mk (t,x),ht⟩)).val = Susp.mk (clamp t,p)
  rw [contractMotion_mk]
  unfold contractCylinderFun
  split_ifs with hx
  · change Susp.mk (clamp t,(G.contraction (0,⟨x,hx⟩)).val) = _
    rw [G.contraction.apply_zero]
    rfl
  · rcases (mk_mem_neighborhood _ _ _).mp ht with hh | hh | hh
    · rw [clamp_zero_of_le _ hh.le]
      exact Susp.mk_zero_eq_mk_zero _ _
    · rw [clamp_one_of_le _ hh.le]
      exact Susp.mk_one_eq_mk_one _ _
    · exact (hx hh).elim

theorem contractMotion_one (z : neighborhood G.neighborhood) :
    contractMotion G (1,z) = unclampMotion G.neighborhood G.isOpen (0,z) := by
  obtain ⟨⟨⟨t,x⟩,ht⟩,hz⟩ := (Susp.quotient_restrictMk _ (neighborhood_open _ G.isOpen)).surjective z
  rw [← hz]
  apply Subtype.ext
  change (contractMotion G (1,⟨Susp.mk (t,x),ht⟩)).val =
    (unclampMotion G.neighborhood G.isOpen (0,⟨Susp.mk (t,x),ht⟩)).val
  rw [contractMotion_mk,unclampMotion_mk,unclampLevel_zero]
  unfold contractCylinderFun
  split_ifs with hx
  · change Susp.mk (clamp t,(G.contraction (1,⟨x,hx⟩)).val) = _
    rw [G.contraction.apply_one]
    rfl
  · rfl

def retract : C(neighborhood G.neighborhood,Susp.arc p) :=
  ⟨fun z => ⟨Susp.mk (Susp.height z.val,p),⟨_,rfl⟩⟩,by
    apply Continuous.subtype_mk
    exact Susp.mk.continuous.comp
      ((Susp.height.continuous.comp continuous_subtype_val).prodMk continuous_const)⟩

def inclusion : C(Susp.arc p,neighborhood G.neighborhood) :=
  ⟨fun z => ⟨z.val,arc_subset _ G.mem z.property⟩,continuous_subtype_val.subtype_mk _⟩

def clamped : C(neighborhood G.neighborhood,neighborhood G.neighborhood) :=
  ⟨fun z => unclampMotion G.neighborhood G.isOpen (0,z),
    (unclampMotion G.neighborhood G.isOpen).continuous.comp
      (continuous_const.prodMk continuous_id)⟩

def contracted : C(neighborhood G.neighborhood,neighborhood G.neighborhood) :=
  ⟨fun z => ⟨Susp.mk (clamp (Susp.height z.val),p),arc_subset _ G.mem ⟨_,rfl⟩⟩,by
    apply Continuous.subtype_mk
    exact Susp.mk.continuous.comp
      ((clamp.continuous.comp (Susp.height.continuous.comp continuous_subtype_val)).prodMk
        continuous_const)⟩

/-- Restoring the height on the arc makes the endpoint retraction fix the arc exactly. -/
def restoreArcHomotopy : ((inclusion G).comp (retract G)).Homotopy (contracted G) where
  toFun z := ⟨Susp.mk (unclampLevel (σ z.1,Susp.height z.2.val),p),
    arc_subset _ G.mem ⟨_,rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Susp.mk.continuous.comp
      ((unclampLevel.continuous.comp ((continuous_symm.comp continuous_fst).prodMk
        (Susp.height.continuous.comp (continuous_subtype_val.comp continuous_snd)))).prodMk
        continuous_const)
  map_zero_left := by
    intro z
    apply Subtype.ext
    change Susp.mk (unclampLevel (σ 0,Susp.height z.val),p) = _
    rw [symm_zero,unclampLevel_one]
    rfl
  map_one_left := by
    intro z
    apply Subtype.ext
    change Susp.mk (unclampLevel (σ 1,Susp.height z.val),p) = _
    rw [symm_one,unclampLevel_zero]
    rfl

def contractHomotopy : (contracted G).Homotopy (clamped G) where
  toFun := contractMotion G
  continuous_toFun := (contractMotion G).continuous
  map_zero_left z := Subtype.ext (contractMotion_zero G z)
  map_one_left z := contractMotion_one G z

def unclampHomotopy : (clamped G).Homotopy (ContinuousMap.id (neighborhood G.neighborhood)) where
  toFun := unclampMotion G.neighborhood G.isOpen
  continuous_toFun := (unclampMotion G.neighborhood G.isOpen).continuous
  map_zero_left _ := rfl
  map_one_left := by
    intro z
    obtain ⟨⟨⟨t,x⟩,ht⟩,hz⟩ := (Susp.quotient_restrictMk _ (neighborhood_open _ G.isOpen)).surjective z
    rw [← hz]
    apply Subtype.ext
    change (unclampMotion G.neighborhood G.isOpen (1,⟨Susp.mk (t,x),ht⟩)).val = Susp.mk (t,x)
    rw [unclampMotion_mk,unclampLevel_one]

theorem contractHomotopy_preserve (s : I) (z : neighborhood G.neighborhood)
    (hz : z.val ∈ Susp.arc p) : (contractHomotopy G (s,z)).val ∈ Susp.arc p := by
  rcases z with ⟨z,hzN⟩
  obtain ⟨t,rfl⟩ := hz
  change (contractMotion G (s,⟨Susp.mk (t,p),hzN⟩)).val ∈ Susp.arc p
  rw [contractMotion_mk]
  unfold contractCylinderFun
  rw [dif_pos G.mem]
  change Susp.mk (clamp t,(G.contraction (s,⟨p,G.mem⟩)).val) ∈ Susp.arc p
  rw [G.fixed]
  exact ⟨_,rfl⟩

theorem unclampHomotopy_preserve (s : I) (z : neighborhood G.neighborhood)
    (hz : z.val ∈ Susp.arc p) : (unclampHomotopy G (s,z)).val ∈ Susp.arc p := by
  rcases z with ⟨z,hzN⟩
  obtain ⟨t,rfl⟩ := hz
  change (unclampMotion G.neighborhood G.isOpen (s,⟨Susp.mk (t,p),hzN⟩)).val ∈ Susp.arc p
  rw [unclampMotion_mk]
  exact ⟨_,rfl⟩

/-- The actual open good neighborhood of the marked suspension arc. -/
def deformation : NeighborhoodDeformation (Susp.arc p) (neighborhood G.neighborhood) where
  subset := arc_subset _ G.mem
  retract := retract G
  retraction := by
    rintro ⟨z,hz⟩
    obtain ⟨t,rfl⟩ := hz
    rfl
  homotopy := (restoreArcHomotopy G).trans ((contractHomotopy G).trans (unclampHomotopy G))
  preserve := by
    intro s a
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact ⟨_,rfl⟩
    · rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact contractHomotopy_preserve G _ _ a.property
      · exact unclampHomotopy_preserve G _ _ a.property

end SuspensionArc
end NRR.SingularHomology
