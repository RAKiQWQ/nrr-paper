import NRR.PrimePowerTopologyFiltration
import NRR.PrimePowerTopologyBoundary
import NRR.SingularHomologyRelMap
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! Twisted coinvariants of the genuine singular chain complex of ordered
configuration space. This supplies an actual chain complex in which the
orientation character acts, rather than declaring an abstract scalar matrix
to be the full cellular boundary. Comparison with cellular chains remains a
separate geometric theorem. -/

noncomputable section
open Set Topology CategoryTheory Limits
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R]

section ChainActions

variable {G : Type} [Group G] (χ : G →* Rˣ)
  (K : ChainComplex (ModuleCat R) ℕ) (ρ : G → (K ⟶ K))

def chainActionRelation (g : G) : K ⟶ K := ρ g - (χ g : R) • 𝟙 K

def chainActionRelations : (∐ fun _g : G => K) ⟶ K :=
  Sigma.desc (chainActionRelation R χ K ρ)

/-- Orientation-twisted coinvariants in the category of actual chain
complexes of R-modules. The construction also applies to relative chains. -/
def twistedChainComplex : ChainComplex (ModuleCat R) ℕ :=
  cokernel (chainActionRelations R χ K ρ)

def twistedChainProj : K ⟶ twistedChainComplex R χ K ρ :=
  cokernel.π (chainActionRelations R χ K ρ)

theorem chainActionRelation_proj (g : G) :
    chainActionRelation R χ K ρ g ≫ twistedChainProj R χ K ρ = 0 := by
  have h := congrArg (fun f => (Sigma.ι (fun _g : G => K) g) ≫ f)
    (cokernel.condition (chainActionRelations R χ K ρ))
  simpa only [chainActionRelations,twistedChainProj,← Category.assoc,
    Sigma.ι_desc,comp_zero] using h

theorem chainAction_proj (g : G) :
    ρ g ≫ twistedChainProj R χ K ρ = (χ g : R) • twistedChainProj R χ K ρ := by
  have h := chainActionRelation_proj R χ K ρ g
  rw [chainActionRelation,Preadditive.sub_comp,Linear.smul_comp,
    Category.id_comp,sub_eq_zero] at h
  exact h

variable {L : ChainComplex (ModuleCat R) ℕ} (τ : G → (L ⟶ L))
  (f : K ⟶ L) (equivariant : ∀ g,ρ g ≫ f = f ≫ τ g)

/-- A genuinely equivariant chain map descends to the twisted complexes. -/
def twistedChainMap : twistedChainComplex R χ K ρ ⟶ twistedChainComplex R χ L τ :=
  cokernel.desc (chainActionRelations R χ K ρ) (f ≫ twistedChainProj R χ L τ) (by
    apply Sigma.hom_ext
    intro g
    simp only [← Category.assoc,chainActionRelations,Sigma.ι_desc,comp_zero]
    rw [chainActionRelation,Preadditive.sub_comp,Preadditive.sub_comp,
      Linear.smul_comp,Linear.smul_comp,Category.id_comp,equivariant g,
      Category.assoc,chainAction_proj,Linear.comp_smul,sub_self])

@[reassoc (attr := simp)] theorem twistedChainProj_map :
    twistedChainProj R χ K ρ ≫ twistedChainMap R χ K ρ τ f equivariant =
      f ≫ twistedChainProj R χ L τ :=
  cokernel.π_desc _ _ _

theorem twistedChainMap_id :
    twistedChainMap R χ K ρ ρ (𝟙 K) (fun _ => by simp) = 𝟙 _ := by
  have hepi : Epi (twistedChainProj R χ K ρ) := coequalizer.π_epi
  apply hepi.left_cancellation
  simp only [twistedChainProj_map,Category.id_comp,Category.comp_id]

theorem twistedChainMap_comp {M : ChainComplex (ModuleCat R) ℕ}
    (υ : G → (M ⟶ M)) (g : L ⟶ M) (gequiv : ∀ a,τ a ≫ g = g ≫ υ a) :
    twistedChainMap R χ K ρ τ f equivariant ≫
      twistedChainMap R χ L τ υ g gequiv =
    twistedChainMap R χ K ρ υ (f ≫ g) (fun a => by
      rw [← Category.assoc,equivariant a,Category.assoc,gequiv a,Category.assoc]) := by
  have hepi : Epi (twistedChainProj R χ K ρ) := coequalizer.π_epi
  apply hepi.left_cancellation
  simp only [← Category.assoc,twistedChainProj_map]
  rw [Category.assoc,twistedChainProj_map,Category.assoc]

end ChainActions

def configurationRelabelMap {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TopCat.of (Configuration d n) ⟶ TopCat.of (Configuration d n) :=
  TopCat.ofHom ⟨relabelConfiguration σ,(relabelConfiguration σ).continuous⟩

@[simp] theorem configurationRelabelMap_one (d n : ℕ) :
    configurationRelabelMap (d := d) (1 : Equiv.Perm (Fin n)) = 𝟙 _ := by
  ext x i
  rfl

theorem configurationRelabelMap_mul {d n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    configurationRelabelMap (d := d) (σ*τ) =
      configurationRelabelMap τ ≫ configurationRelabelMap σ := by
  ext x i
  rfl

def singularConfigurationRelabel {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Csing R (TopCat.of (Configuration d n)) ⟶ Csing R (TopCat.of (Configuration d n)) :=
  CsingMap R (configurationRelabelMap σ)

@[simp] theorem singularConfigurationRelabel_one (d n : ℕ) :
    singularConfigurationRelabel R (d := d) (1 : Equiv.Perm (Fin n)) = 𝟙 _ := by
  rw [singularConfigurationRelabel,configurationRelabelMap_one,CsingMap_id]

theorem singularConfigurationRelabel_mul {d n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    singularConfigurationRelabel R (d := d) (σ*τ) =
      singularConfigurationRelabel R τ ≫ singularConfigurationRelabel R σ := by
  rw [singularConfigurationRelabel,configurationRelabelMap_mul,CsingMap_comp]
  rfl

/-- The chain-map relation for a single label permutation. Since these
are actual chain maps, the differential automatically preserves all relations. -/
def twistedConfigurationRelation {d n : ℕ} (χ : Equiv.Perm (Fin n) →* Rˣ)
    (σ : Equiv.Perm (Fin n)) :
    Csing R (TopCat.of (Configuration d n)) ⟶ Csing R (TopCat.of (Configuration d n)) :=
  singularConfigurationRelabel R σ - (χ σ : R) • 𝟙 _

def twistedConfigurationRelations {d n : ℕ} (χ : Equiv.Perm (Fin n) →* Rˣ) :
    (∐ fun _σ : Equiv.Perm (Fin n) => Csing R (TopCat.of (Configuration d n))) ⟶
      Csing R (TopCat.of (Configuration d n)) :=
  Sigma.desc (twistedConfigurationRelation R χ)

def twistedConfigurationComplex {d n : ℕ} (χ : Equiv.Perm (Fin n) →* Rˣ) :
    ChainComplex (ModuleCat R) ℕ :=
  cokernel (twistedConfigurationRelations R (d := d) χ)

def twistedConfigurationProj {d n : ℕ} (χ : Equiv.Perm (Fin n) →* Rˣ) :
    Csing R (TopCat.of (Configuration d n)) ⟶ twistedConfigurationComplex R (d := d) χ :=
  cokernel.π (twistedConfigurationRelations R χ)

theorem twistedConfigurationRelation_proj {d n : ℕ}
    (χ : Equiv.Perm (Fin n) →* Rˣ) (σ : Equiv.Perm (Fin n)) :
    twistedConfigurationRelation R (d := d) χ σ ≫ twistedConfigurationProj R χ = 0 := by
  have h := congrArg (fun f =>
    (Sigma.ι (fun _σ : Equiv.Perm (Fin n) => Csing R (TopCat.of (Configuration d n))) σ) ≫ f)
    (cokernel.condition (twistedConfigurationRelations R (d := d) χ))
  simpa only [twistedConfigurationRelations,twistedConfigurationProj,← Category.assoc,
    Sigma.ι_desc,comp_zero] using h

/-- This quotient imposes the genuine orientation-twisted action on chains,
without dividing by the symmetric group order. -/
theorem singularConfigurationRelabel_proj {d n : ℕ}
    (χ : Equiv.Perm (Fin n) →* Rˣ) (σ : Equiv.Perm (Fin n)) :
    singularConfigurationRelabel R (d := d) σ ≫ twistedConfigurationProj R χ =
      (χ σ : R) • twistedConfigurationProj R χ := by
  have h := twistedConfigurationRelation_proj R (d := d) χ σ
  rw [twistedConfigurationRelation,Preadditive.sub_comp,Linear.smul_comp,
    Category.id_comp,sub_eq_zero] at h
  exact h

end NRR.PrimePowerTopology
