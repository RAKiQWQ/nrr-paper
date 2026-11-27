import NRR.CubeSectionMass
import Mathlib.Analysis.Convex.Continuous

/-! The analytic section argument uses a supporting affine function at the
interior projected centroid. It does not assume continuity of section volumes
at the boundary of their convex projection. -/

noncomputable section
open Set Filter Topology MeasureTheory

namespace NRR.CubeSectionMass

/-- A finite concave function has a continuous affine majorant touching it
at an interior point. Boundary continuity of the function is not needed. -/
theorem exists_concave_majorant_at_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {g : E → ℝ}
    (hg : ConcaveOn ℝ s g) (h0 : (0 : E) ∈ interior s) :
    ∃ L : E →L[ℝ] ℝ, ∀ u ∈ s,g u ≤ g 0 + L u := by
  let H : Set (E × ℝ) := {p | p.1 ∈ interior s ∧ p.2 < g p.1}
  have hcont := hg.continuousOn_interior
  have hdiff : ContinuousOn (fun p : E × ℝ => p.2-g p.1)
      {p | p.1 ∈ interior s} :=
    continuous_snd.continuousOn.sub
      (hcont.comp continuous_fst.continuousOn (fun _ hp => hp))
  have hopen : IsOpen H := by
    convert hdiff.isOpen_inter_preimage
      (isOpen_interior.preimage continuous_fst) (isOpen_Iio (a := (0 : ℝ))) using 1
    ext p
    simp only [H,mem_setOf_eq,mem_inter_iff,mem_preimage,mem_Iio,sub_neg]
  have hconv : Convex ℝ H :=
    (hg.subset interior_subset hg.1.interior).convex_strict_hypograph
  have hout : ((0,g 0) : E × ℝ) ∉ H := by simp [H]
  obtain ⟨F,hF⟩ := geometric_hahn_banach_open_point hconv hopen hout
  let c : ℝ := F (0,1)
  have eval (u : E) (z : ℝ) : F (u,z) = F (u,0) + z*c := by
    have eq : (u,z) = (u,0) + z • ((0,1) : E × ℝ) := by ext <;> simp
    rw [eq,map_add,map_smul]
    rfl
  have cpos : 0 < c := by
    have h := hF (0,g 0-1) ⟨h0,by linarith⟩
    rw [eval 0 (g 0-1),eval 0 (g 0)] at h
    nlinarith
  let L : E →L[ℝ] ℝ := (-c⁻¹) • (F.comp (ContinuousLinearMap.inl ℝ E ℝ))
  have relation (u : E) : L u*c = -F (u,0) := by
    change (-c⁻¹) * F (u,0) * c = -F (u,0)
    field_simp [cpos.ne']
  have interior_bound (u : E) (hu : u ∈ interior s) : g u ≤ g 0 + L u := by
    have below (z : ℝ) (hz : z < g u) : z < g 0 + L u := by
      have h := hF (u,z) ⟨hu,hz⟩
      rw [eval u z,eval 0 (g 0),show F ((0 : E),(0 : ℝ)) = 0 from F.map_zero] at h
      apply (mul_lt_mul_iff_right₀ cpos).mp
      nlinarith [relation u]
    by_contra! h
    have hmid := below ((g u + (g 0 + L u))/2) (by linarith)
    linarith
  refine ⟨L,?_⟩
  intro u hu
  have hhalf : (1/2 : ℝ) • u ∈ interior s := by
    have h := hg.1.combo_interior_self_mem_interior h0 hu
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simpa using h
  have hlower := hg.2 (interior_subset h0) hu
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have hupper := interior_bound _ hhalf
  simp only [smul_zero,zero_add,smul_eq_mul,map_smul] at hlower hupper
  linarith


open CubeProductMoments
variable {k : ℕ}

def rootMass (C : Set (Active × Passive k)) (u : Passive k) : ℝ :=
  (mass C u)^(1/3 : ℝ)

theorem integrable_root_mass_on_cell {C : Set (Active × Passive k)} (hc : IsCompact C) :
    IntegrableOn (fun p : Active × Passive k => rootMass C p.2) C volume := by
  letI : IsFiniteMeasure (volume.restrict C) :=
    isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  have cr : Continuous (fun a : ℝ => a^(1/3 : ℝ)) :=
    continuous_id.rpow_const (fun _ => Or.inr (by norm_num))
  refine (integrable_const ((volume.real (Prod.fst '' C))^(1/3 : ℝ))).mono'
    ((cr.measurable.comp (measurable_mass hc)).comp measurable_snd).aestronglyMeasurable ?_
  filter_upwards with p
  dsimp only [rootMass]
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (mass_nonneg C p.2) _)]
  exact Real.rpow_le_rpow (mass_nonneg C p.2) (mass_le_projection_volume hc p.2) (by norm_num)

/-- Supporting the cube-root section density and integrating over the actual
cell turns the projected centroid condition into the weighted Jensen bound.
Concavity is explicit here and must be supplied by genuine Brunn--Minkowski. -/
theorem integral_root_mass_le_of_concavity {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k))
    (concavity : ConcaveOn ℝ (projection C) (rootMass C)) :
    (∫ p in C,rootMass C p.2 ∂volume) ≤ volume.real C * rootMass C 0 := by
  obtain ⟨L,major⟩ := exists_concave_majorant_at_zero concavity
    (zero_mem_interior_projection hc hv hm centered)
  have hi : IntegrableOn (fun p : Active × Passive k => p.2) C volume :=
    continuous_snd.continuousOn.integrableOn_compact hc
  have hL : IntegrableOn (fun p : Active × Passive k => L p.2) C volume :=
    (L.continuous.comp continuous_snd).continuousOn.integrableOn_compact hc
  have hconst : IntegrableOn (fun _ : Active × Passive k => rootMass C 0) C volume :=
    integrableOn_const hc.measure_lt_top.ne
  have bound := integral_mono_ae (integrable_root_mass_on_cell hc) (hconst.add hL) (by
    filter_upwards [ae_restrict_mem hc.measurableSet] with p hp
    exact major p.2 ⟨p,hp,rfl⟩)
  have comm := L.integral_comp_comm hi
  change (∫ p in C,L p.2 ∂volume) = L (∫ p in C,p.2 ∂volume) at comm
  change (∫ p in C,rootMass C p.2 ∂volume) ≤
    ∫ p in C,rootMass C 0 + L p.2 ∂volume at bound
  rw [integral_add hconst hL,setIntegral_const,comm,centered,map_zero,add_zero] at bound
  simpa only [smul_eq_mul] using bound

private theorem mass_mul_rootMass (C : Set (Active × Passive k)) (u : Passive k) :
    mass C u * rootMass C u = (mass C u)^(4/3 : ℝ) := by
  unfold rootMass
  rw [show (4/3 : ℝ) = 1 + (1/3 : ℝ) by norm_num,
    Real.rpow_add' (mass_nonneg C u) (by norm_num),Real.rpow_one]

theorem integral_rpow_uniform_eq {C : Set (Active × Passive k)} (hc : IsCompact C)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k) :
    (∫ u,(mass C u)^(4/3 : ℝ) ∂uniform k) =
      ((2 : ℝ)^k)⁻¹ * (∫ p in C,rootMass C p.2 ∂volume) := by
  have outside (u : Passive k) (hu : u ∉ passiveCube k) :
      (mass C u)^(4/3 : ℝ) = 0 := by
    rw [mass_eq_zero_outside sub hu,Real.zero_rpow (by norm_num)]
  rw [uniform,integral_smul_measure,ENNReal.toReal_inv,passiveCube_volume]
  change ((2 : ℝ)^k)⁻¹ * (∫ u in passiveCube k,(mass C u)^(4/3 : ℝ) ∂volume) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero outside,
    integral_passive_on hc (rootMass C) (integrable_root_mass_on_cell hc)]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  exact (mass_mul_rootMass C u).symm

theorem integral_rpow_upper_of_concavity {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k))
    (concavity : ConcaveOn ℝ (projection C) (rootMass C)) :
    (∫ u,(mass C u)^(4/3 : ℝ) ∂uniform k) ≤
      (∫ u,mass C u ∂uniform k) * rootMass C 0 := by
  rw [integral_rpow_uniform_eq hc sub,integral_mass_uniform hc sub]
  have h := mul_le_mul_of_nonneg_left
    (integral_root_mass_le_of_concavity hc hv hm centered concavity)
    (by positivity : 0 ≤ ((2 : ℝ)^k)⁻¹)
  convert h using 1 <;> ring


/-- The centroid and genuine root-volume concavity force the central
section volume to dominate the normalized mean section volume. -/
theorem central_mass_lower_of_concavity {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k))
    (concavity : ConcaveOn ℝ (projection C) (rootMass C)) :
    (∫ u,mass C u ∂uniform k) ≤ mass C 0 := by
  letI := uniform_probability k
  let M : ℝ := ∫ u,mass C u ∂uniform k
  have hM : 0 < M := by
    dsimp [M]
    rw [integral_mass_uniform hc sub]
    positivity
  have lower := mean_mass_rpow_le_integral_rpow (uniform k) hc
    (by norm_num : (1 : ℝ) ≤ 4/3)
  have upper := integral_rpow_upper_of_concavity hc hv hm sub centered concavity
  have power : M^(4/3 : ℝ) = M * M^(1/3 : ℝ) := by
    rw [show (4/3 : ℝ) = 1 + (1/3 : ℝ) by norm_num,
      Real.rpow_add hM,Real.rpow_one]
  change M^(4/3 : ℝ) ≤ _ at lower
  change _ ≤ M * (mass C 0)^(1/3 : ℝ) at upper
  rw [power] at lower
  have root_le : M^(1/3 : ℝ) ≤ (mass C 0)^(1/3 : ℝ) :=
    le_of_mul_le_mul_left (lower.trans upper) hM
  exact (Real.rpow_le_rpow_iff hM.le (mass_nonneg C 0) (by norm_num : (0 : ℝ) < 1/3)).mp root_le

theorem ae_constant_mass_of_concavity_of_central_eq {C : Set (Active × Passive k)}
    (hc : IsCompact C) (hv : Convex ℝ C) (hm : 0 < volume.real C)
    {D : Set Active} (sub : C ⊆ D ×ˢ passiveCube k)
    (centered : ∫ p in C,p.2 ∂volume = (0 : Passive k))
    (concavity : ConcaveOn ℝ (projection C) (rootMass C))
    (central_eq : mass C 0 = ∫ u,mass C u ∂uniform k) :
    ∀ᵐ u ∂uniform k,mass C u = ∫ v,mass C v ∂uniform k := by
  letI := uniform_probability k
  let M : ℝ := ∫ u,mass C u ∂uniform k
  have hM : 0 < M := by
    dsimp [M]
    rw [integral_mass_uniform hc sub]
    positivity
  have power : M^(4/3 : ℝ) = M * M^(1/3 : ℝ) := by
    rw [show (4/3 : ℝ) = 1 + (1/3 : ℝ) by norm_num,
      Real.rpow_add hM,Real.rpow_one]
  have root_eq : rootMass C 0 = M^(1/3 : ℝ) := by
    unfold rootMass
    rw [central_eq]
  have upper := integral_rpow_upper_of_concavity hc hv hm sub centered concavity
  change _ ≤ M * rootMass C 0 at upper
  rw [root_eq,← power] at upper
  exact ae_constant_mass_of_rpow_eq (uniform k) hc
    (by norm_num : (1 : ℝ) < 4/3)
    (le_antisymm upper
      (mean_mass_rpow_le_integral_rpow (uniform k) hc (by norm_num : (1 : ℝ) ≤ 4/3)))

end NRR.CubeSectionMass
