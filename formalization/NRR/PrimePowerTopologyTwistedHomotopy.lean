import NRR.PrimePowerTopologyChainTransfer
import NRR.SingularHomologyRelHomotopy
import NRR.TopologyPort.SingularPrism

/-! Equivariant chain homotopies descend to the genuine twisted chain
complexes. This descent is proved in all characteristics, degree by degree. -/

noncomputable section
open CategoryTheory Limits
open NRR.SingularHomology

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {G : Type} [Group G]
  (χ : G →* Rˣ) {K L : ChainComplex (ModuleCat R) ℕ}
  (ρ : G → (K ⟶ K)) (τ : G → (L ⟶ L))

def twistedRelationsMap (f : K ⟶ L) :
    (∐ fun _g : G => K) ⟶ (∐ fun _g : G => L) :=
  Sigma.desc (fun g => f ≫ Sigma.ι (fun _g : G => L) g)

theorem twistedRelationsMap_comm (f : K ⟶ L)
    (equivariant : ∀ g,ρ g ≫ f = f ≫ τ g) :
    chainActionRelations R χ K ρ ≫ f =
      twistedRelationsMap R (G := G) f ≫ chainActionRelations R χ L τ := by
  apply Sigma.hom_ext
  intro g
  simp only [← Category.assoc,chainActionRelations,twistedRelationsMap,Sigma.ι_desc]
  rw [Category.assoc,Sigma.ι_desc]
  simp only [chainActionRelation,Preadditive.sub_comp,Preadditive.comp_sub,
    Linear.smul_comp,Linear.comp_smul,Category.id_comp,Category.comp_id,equivariant g]

theorem twistedChainMap_eq_cokernelMap (f : K ⟶ L)
    (equivariant : ∀ g,ρ g ≫ f = f ≫ τ g) :
    twistedChainMap R χ K ρ τ f equivariant =
      cokernel.map (chainActionRelations R χ K ρ) (chainActionRelations R χ L τ)
        (twistedRelationsMap R (G := G) f) f (twistedRelationsMap_comm R χ ρ τ f equivariant) := by
  have hepi : Epi (twistedChainProj R χ K ρ) := coequalizer.π_epi
  apply hepi.left_cancellation
  rw [twistedChainProj_map]
  change f ≫ cokernel.π _ = cokernel.π _ ≫ cokernel.map _ _ _ _ _
  rw [cokernel.map,cokernel.π_desc]

private theorem coproduct_degree_hom_ext (p : ℕ) {T : ModuleCat R}
    (a b : (∐ fun _g : G => K).X p ⟶ T)
    (same : ∀ g,(Sigma.ι (fun _g : G => K) g).f p ≫ a =
      (Sigma.ι (fun _g : G => K) g).f p ≫ b) : a = b := by
  apply (isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) p)
    (coproductIsCoproduct (fun _g : G => K))).hom_ext
  intro ⟨g⟩
  exact same g

private theorem relations_degree_homotopy_zero {f g : K ⟶ L}
    (H : Homotopy f g)
    (equivariant : ∀ a p q,(ρ a).f p ≫ H.hom p q = H.hom p q ≫ (τ a).f q)
    (p q : ℕ) :
    (chainActionRelations R χ K ρ).f p ≫ H.hom p q ≫
      (cokernel.π (chainActionRelations R χ L τ)).f q = 0 := by
  apply coproduct_degree_hom_ext R (G := G)
  intro a
  have hi : (Sigma.ι (fun _g : G => K) a).f p ≫
      (chainActionRelations R χ K ρ).f p = (chainActionRelation R χ K ρ a).f p := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun m => m.f p) (Sigma.ι_desc (chainActionRelation R χ K ρ) a)
  rw [← Category.assoc,← Category.assoc,hi,comp_zero]
  simp only [chainActionRelation,HomologicalComplex.sub_f_apply,
    HomologicalComplex.smul_f_apply,HomologicalComplex.id_f,Preadditive.sub_comp,
    Linear.smul_comp,Category.id_comp]
  rw [equivariant a p q,Category.assoc]
  have ht := congrArg (fun m => m.f q) (chainAction_proj R χ L τ a)
  simp only [HomologicalComplex.comp_f,HomologicalComplex.smul_f_apply] at ht
  change (τ a).f q ≫ (cokernel.π (chainActionRelations R χ L τ)).f q =
    (χ a : R) • (cokernel.π (chainActionRelations R χ L τ)).f q at ht
  rw [ht,Linear.comp_smul,sub_self]

/-- A chain homotopy equivariant at every operator, such as the actual
singular prism of a pointwise equivariant continuous homotopy, descends
without averaging to orientation-twisted coinvariants. -/
def twistedChainHomotopy {f g : K ⟶ L}
    (equivf : ∀ a,ρ a ≫ f = f ≫ τ a) (equivg : ∀ a,ρ a ≫ g = g ≫ τ a)
    (H : Homotopy f g)
    (equivariant : ∀ a p q,(ρ a).f p ≫ H.hom p q = H.hom p q ≫ (τ a).f q) :
    Homotopy (twistedChainMap R χ K ρ τ f equivf)
      (twistedChainMap R χ K ρ τ g equivg) := by
  rw [twistedChainMap_eq_cokernelMap,twistedChainMap_eq_cokernelMap]
  exact descHomotopy R (chainActionRelations R χ K ρ) (chainActionRelations R χ L τ)
    (twistedRelationsMap_comm R χ ρ τ f equivf)
    (twistedRelationsMap_comm R χ ρ τ g equivg) H
    (relations_degree_homotopy_zero R χ ρ τ H equivariant)

theorem twistedHomologyMap_eq_of_equivariant_homotopy {f g : K ⟶ L}
    (equivf : ∀ a,ρ a ≫ f = f ≫ τ a) (equivg : ∀ a,ρ a ≫ g = g ≫ τ a)
    (H : Homotopy f g)
    (equivariant : ∀ a p q,(ρ a).f p ≫ H.hom p q = H.hom p q ≫ (τ a).f q) (k : ℕ) :
    HomologicalComplex.homologyMap (twistedChainMap R χ K ρ τ f equivf) k =
      HomologicalComplex.homologyMap (twistedChainMap R χ K ρ τ g equivg) k :=
  (twistedChainHomotopy R χ ρ τ equivf equivg H equivariant).homologyMap_eq k

section ContinuousHomotopy

variable {X Y : TopCat.{0}} (α : G → (X ⟶ X)) (β : G → (Y ⟶ Y))

theorem CsingMap_equivariant (f : X ⟶ Y)
    (equivariant : ∀ a,α a ≫ f = f ≫ β a) (a : G) :
    CsingMap R (α a) ≫ CsingMap R f = CsingMap R f ≫ CsingMap R (β a) := by
  rw [← CsingMap_comp,← CsingMap_comp,equivariant a]

/-- A pointwise equivariant continuous homotopy induces a homotopy on
actual twisted singular complexes. The prism operators are equivariant
before quotienting, so this construction requires no averaging. -/
def twistedSingularChainHomotopy {f g : X ⟶ Y}
    (equivf : ∀ a,α a ≫ f = f ≫ β a) (equivg : ∀ a,α a ≫ g = g ≫ β a)
    (H : f.hom.Homotopy g.hom)
    (equivariant : ∀ a t x,H (t,(α a).hom x) = (β a).hom (H (t,x))) :
    Homotopy
      (twistedChainMap R χ (Csing R X) (fun a => CsingMap R (α a))
        (fun a => CsingMap R (β a)) (CsingMap R f) (CsingMap_equivariant R α β f equivf))
      (twistedChainMap R χ (Csing R X) (fun a => CsingMap R (α a))
        (fun a => CsingMap R (β a)) (CsingMap R g) (CsingMap_equivariant R α β g equivg)) := by
  apply twistedChainHomotopy R χ (fun a => CsingMap R (α a)) (fun a => CsingMap R (β a))
    (CsingMap_equivariant R α β f equivf) (CsingMap_equivariant R α β g equivg)
    (NRR.TopologyPort.singularChainHomotopy (ModuleCat.of R R) H)
  intro a p q
  exact NRR.TopologyPort.singularChainHomotopy_pair_naturality (ModuleCat.of R R)
    (α a) (β a) H H (equivariant a) p q

end ContinuousHomotopy

end NRR.PrimePowerTopology
