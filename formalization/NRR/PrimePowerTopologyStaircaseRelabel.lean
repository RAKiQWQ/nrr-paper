import NRR.PrimePowerTopologyTwistedFundamental
import NRR.PrimePowerTopologyRelativePairOrbitBasis

/-! The actual label action on cube coordinates and staircase chambers.
Its orientation character is the determinant character already computed
for ambient configuration space. -/

noncomputable section
open Set Topology CategoryTheory Limits Opposite Simplicial
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

/-- Relabel scalar coordinates by relabeling their site component. -/
def configurationAxisRelabel (d : ℕ) {n : ℕ} (σ : ConfigurationGroup n) :
    Equiv.Perm (Fin (n*d)) :=
  (configurationAxisEquiv d n).permCongr
    (Equiv.prodCongrLeft (fun _ : Fin d => σ))

@[simp] theorem configurationAxisRelabel_apply {d n : ℕ} (σ : ConfigurationGroup n)
    (i : Fin n) (j : Fin d) :
    configurationAxisRelabel d σ (configurationAxisEquiv d n (i,j)) =
      configurationAxisEquiv d n (σ i,j) := by
  simp [configurationAxisRelabel]

@[simp] theorem configurationAxisRelabel_one (d n : ℕ) :
    configurationAxisRelabel d (1 : ConfigurationGroup n) = 1 := by
  ext a
  obtain ⟨⟨i,j⟩,rfl⟩ := (configurationAxisEquiv d n).surjective a
  simp

theorem configurationAxisRelabel_mul (d : ℕ) {n : ℕ} (σ τ : ConfigurationGroup n) :
    configurationAxisRelabel d (σ*τ) =
      configurationAxisRelabel d σ * configurationAxisRelabel d τ := by
  ext a
  obtain ⟨⟨i,j⟩,rfl⟩ := (configurationAxisEquiv d n).surjective a
  simp [Equiv.Perm.mul_apply]

@[simp] theorem configurationAxisRelabel_inv (d : ℕ) {n : ℕ} (σ : ConfigurationGroup n) :
    configurationAxisRelabel d σ⁻¹ = (configurationAxisRelabel d σ)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [← configurationAxisRelabel_mul, inv_mul_cancel, configurationAxisRelabel_one]

theorem configurationAxisRelabel_sign (d : ℕ) {n : ℕ} (σ : ConfigurationGroup n) :
    Equiv.Perm.sign (configurationAxisRelabel d σ) = (Equiv.Perm.sign σ)^d := by
  rw [configurationAxisRelabel, Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_prodCongrLeft]
  simp

theorem configurationAxisRelabel_orientation (p d : ℕ) {n : ℕ}
    (σ : ConfigurationGroup n) :
    Units.map (Int.castRingHom (ZMod p)).toMonoidHom
        (Equiv.Perm.sign (configurationAxisRelabel d σ)) =
      associatedAmbientOrientationMod p d n σ := by
  rw [configurationAxisRelabel_sign, map_pow]
  rfl

theorem configurationAxisRelabel_faithful {d n : ℕ} (hd : 0 < d)
    (σ : ConfigurationGroup n) (hσ : configurationAxisRelabel d σ = 1) : σ = 1 := by
  apply Equiv.ext
  intro i
  have h := congrArg (fun τ : Equiv.Perm (Fin (n*d)) =>
    (configurationAxisEquiv d n).symm
      (τ (configurationAxisEquiv d n (i,⟨0,hd⟩)))) hσ
  have he : (σ i, (⟨0,hd⟩ : Fin d)) = (i, (⟨0,hd⟩ : Fin d)) := by simpa using h
  exact congrArg Prod.fst he

/-- The cube action uses the same inverse-label convention as actual
configuration relabeling. -/
def configurationCubeRelabel (d : ℕ) {n : ℕ} (σ : ConfigurationGroup n) :
    C(ConfigurationCube d n,ConfigurationCube d n) :=
  ⟨fun x a => x ((configurationAxisRelabel d σ).symm a), by fun_prop⟩

theorem configurationCubeRelabel_mem_interior_iff {d n : ℕ}
    (σ : ConfigurationGroup n) (x : ConfigurationCube d n) :
    configurationCubeRelabel d σ x ∈ configurationCubeInterior d n ↔
      x ∈ configurationCubeInterior d n := by
  constructor
  · intro h a
    simpa [configurationCubeRelabel] using h (configurationAxisRelabel d σ a)
  · intro h a
    exact h ((configurationAxisRelabel d σ).symm a)

theorem configurationCubeInteriorEuclidean_relabel {d n : ℕ}
    (σ : ConfigurationGroup n) (x : configurationCubeInterior d n) :
    configurationCubeInteriorEuclidean d n
      ⟨configurationCubeRelabel d σ x.val,
        (configurationCubeRelabel_mem_interior_iff σ x.val).mpr x.property⟩ =
      ambientRelabel d σ (configurationCubeInteriorEuclidean d n x) := by
  funext i
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  funext j
  change (unitOpenIntervalToReal
      ⟨(x.val ((configurationAxisRelabel d σ).symm
        (configurationAxisEquiv d n (i,j)))).val, _⟩) =
    (unitOpenIntervalToReal ⟨(x.val (configurationAxisEquiv d n (σ.symm i,j))).val, _⟩)
  have hidx : (configurationAxisRelabel d σ).symm
      (configurationAxisEquiv d n (i,j)) =
      configurationAxisEquiv d n (σ.symm i,j) := by
    apply (configurationAxisRelabel d σ).injective
    simp
  simp only [hidx]

/-- The cube collapse commutes with actual configuration relabeling before
any chain, coefficient or orbit quotient is taken. -/
theorem configurationCubeCollapse_relabel {d n : ℕ}
    (σ : ConfigurationGroup n) (x : ConfigurationCube d n) :
    configurationCubeCollapse d n (configurationCubeRelabel d σ x) =
      compactifiedConfigurationRelabel σ (configurationCubeCollapse d n x) := by
  by_cases hx : x ∈ configurationCubeInterior d n
  · let y : configurationCubeInterior d n := ⟨x,hx⟩
    have hy : configurationCubeRelabel d σ x ∈ configurationCubeInterior d n :=
      (configurationCubeRelabel_mem_interior_iff σ x).mpr hx
    rw [configurationCubeCollapse_interior ⟨_,hy⟩, configurationCubeCollapse_interior y,
      configurationCubeInteriorEuclidean_relabel σ y]
    simpa only [associatedCompactifiedAmbientRelabel, Homeomorph.onePointCongr_apply]
      using configurationOnePointCollapse_equivariant (d := d) σ
        ((configurationCubeInteriorEuclidean d n y : Fin n → Space d) :
          OnePoint (Fin n → Space d))
  · have hy := mt (configurationCubeRelabel_mem_interior_iff σ x).mp hx
    rw [configurationCubeCollapse_boundary _ hy, configurationCubeCollapse_boundary _ hx]
    rfl

theorem staircaseCubeSimplex_relabel {d n : ℕ} (σ : ConfigurationGroup n)
    (π : Equiv.Perm (Fin (n*d))) :
    (configurationCubeRelabel d σ).comp (staircaseCubeSimplex π) =
      staircaseCubeSimplex (π * (configurationAxisRelabel d σ)⁻¹) := by
  ext x a
  rfl

theorem configurationStaircaseSimplex_relabel {d n : ℕ} (σ : ConfigurationGroup n)
    (π : Equiv.Perm (Fin (n*d))) :
    (associatedBMSourceRelabelMap σ).hom.comp (configurationStaircaseSimplex π) =
      configurationStaircaseSimplex (π * (configurationAxisRelabel d σ)⁻¹) := by
  ext x
  change compactifiedConfigurationRelabel σ
    (configurationCubeCollapse d n (staircaseCubeSimplex π x)) = _
  rw [← configurationCubeCollapse_relabel]
  rfl

/-- The finite chamber action whose quotient supplies one representative
per label orbit in the global twisted fundamental chain. -/
instance configurationStaircaseChamberAction (d n : ℕ) :
    MulAction (ConfigurationGroup n) (Equiv.Perm (Fin (n*d))) where
  smul σ π := π * (configurationAxisRelabel d σ)⁻¹
  one_smul π := by
    change π * (configurationAxisRelabel d (1 : ConfigurationGroup n))⁻¹ = π
    simp
  mul_smul σ τ π := by
    change π * (configurationAxisRelabel d (σ*τ))⁻¹ =
      (π * (configurationAxisRelabel d τ)⁻¹) * (configurationAxisRelabel d σ)⁻¹
    simp [configurationAxisRelabel_mul, mul_inv_rev, mul_assoc]

theorem configurationStaircaseChamber_action_free {d n : ℕ} (hd : 0 < d)
    (σ : ConfigurationGroup n) (π : Equiv.Perm (Fin (n*d)))
    (h : σ • π = π) : σ = 1 := by
  apply configurationAxisRelabel_faithful hd
  have hh : π * (configurationAxisRelabel d σ)⁻¹ = π * 1 := h.trans (mul_one π).symm
  exact inv_eq_one.mp (mul_left_cancel hh)

end NRR.PrimePowerTopology
