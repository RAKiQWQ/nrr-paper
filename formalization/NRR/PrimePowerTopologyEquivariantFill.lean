import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Basis.Defs

/-! Equivariant fillings in a bounded below complex with a free orbit basis.

Vanishing ordinary homology and a basis freely permuted by the group suffice
to construct equivariant linear boundary sections, without dividing by the
group order. The construction proceeds upwards from degree zero.
-/

noncomputable section

open CategoryTheory Limits

namespace NRR.PrimePowerTopology

variable {R : Type*} [CommRing R] {G : Type*} [Group G]
    {K : ChainComplex (ModuleCat R) ℕ}

private theorem exists_boundary_of_isZero_homology (q : ℕ)
    (hK : IsZero (K.homology q)) (x : K.X q)
    (hx : K.d q (q-1) x = 0) :
    ∃ y : K.X (q+1), K.d (q+1) q y = x := by
  have hn : (ComplexShape.down ℕ).next q = q-1 := by
    cases q with
    | zero => exact ChainComplex.next_nat_zero
    | succ q => simp
  exact (K.sc' (q+1) q (q-1)).moduleCat_exact_iff.mp
    ((K.exactAt_iff' (q+1) q (q-1) (ChainComplex.prev ℕ q) hn).mp
      ((K.exactAt_iff_isZero_homology q).mpr hK)) x hx

/-- Extend arbitrary lifts on orbit representatives equivariantly, using
the free orbit basis to obtain a linear lift on the whole module. -/
private theorem exists_equivariant_lift_of_basis
    (ρ : G → (K ⟶ K)) (law : ∀ g h, ρ (g*h) = ρ h ≫ ρ g)
    (q : ℕ) {I : Type*} (b : Module.Basis (G × I) R (K.X q))
    (hb : ∀ g h i, (ρ g).f q (b (h,i)) = b (g*h,i))
    (hK : IsZero (K.homology q)) (p : K.X q ⟶ K.X q)
    (hp : ∀ g, (ρ g).f q ≫ p = p ≫ (ρ g).f q)
    (hcycle : ∀ x, K.d q (q-1) (p x) = 0) :
    ∃ s : K.X q ⟶ K.X (q+1),
      (∀ g, (ρ g).f q ≫ s = s ≫ (ρ g).f (q+1)) ∧
      s ≫ K.d (q+1) q = p := by
  classical
  choose y hy using fun i : I =>
    exists_boundary_of_isZero_homology q hK (p (b (1,i))) (hcycle _)
  let s : K.X q ⟶ K.X (q+1) :=
    ModuleCat.ofHom (b.constr R (fun hi => (ρ hi.1).f (q+1) (y hi.2)))
  have hs (h : G) (i : I) : s (b (h,i)) = (ρ h).f (q+1) (y i) :=
    b.constr_basis R _ (h,i)
  refine ⟨s, ?_, ?_⟩
  · intro g
    apply ModuleCat.hom_ext
    apply b.ext
    rintro ⟨h,i⟩
    change s ((ρ g).f q (b (h,i))) = (ρ g).f (q+1) (s (b (h,i)))
    rw [hb, hs, hs]
    exact congrArg (fun f : K ⟶ K => f.f (q+1) (y i)) (law g h)
  · apply ModuleCat.hom_ext
    apply b.ext
    rintro ⟨h,i⟩
    change K.d (q+1) q (s (b (h,i))) = p (b (h,i))
    rw [hs]
    have hc := congrArg (fun f => f (y i)) ((ρ h).comm (q+1) q)
    change K.d (q+1) q ((ρ h).f (q+1) (y i)) =
      (ρ h).f q (K.d (q+1) q (y i)) at hc
    rw [hc, hy]
    have he := congrArg (fun f => f (b (1,i))) (hp h)
    change p ((ρ h).f q (b (1,i))) = (ρ h).f q (p (b (1,i))) at he
    rw [← he, hb, mul_one]

/-- In every degree below the first possible nonzero homology, a chain
complex with a free orbit basis admits an equivariant linear filling of
all cycles. No finiteness or invertibility of the group order is needed. -/
theorem exists_equivariantBoundarySection_of_basis
    (ρ : G → (K ⟶ K)) (law : ∀ g h, ρ (g*h) = ρ h ≫ ρ g)
    {I : ℕ → Type*} (b : ∀ q, Module.Basis (G × I q) R (K.X q))
    (hb : ∀ q g h i, (ρ g).f q (b q (h,i)) = b q (g*h,i))
    (t : ℕ) (hK : ∀ j, j < t → IsZero (K.homology j))
    (q : ℕ) (hq : q < t) :
    ∃ s : K.X q ⟶ K.X (q+1),
      (∀ g, (ρ g).f q ≫ s = s ≫ (ρ g).f (q+1)) ∧
      ∀ x : K.X q, K.d q (q-1) x = 0 → K.d (q+1) q (s x) = x := by
  induction q with
  | zero =>
    obtain ⟨s, hs, hd⟩ := exists_equivariant_lift_of_basis ρ law 0 (b 0) (hb 0)
      (hK 0 hq) (𝟙 _) (fun _ => by simp) (by
        intro x
        rw [K.shape 0 0 (by simp [ComplexShape.down_Rel])]
        rfl)
    refine ⟨s, hs, fun x _ => ?_⟩
    exact congrArg (fun f => f x) hd
  | succ q ih =>
    obtain ⟨s₀, hs₀, hd₀⟩ := ih (Nat.lt_of_succ_lt hq)
    let p : K.X (q+1) ⟶ K.X (q+1) := 𝟙 _ - K.d (q+1) q ≫ s₀
    have hp (g : G) : (ρ g).f (q+1) ≫ p = p ≫ (ρ g).f (q+1) := by
      dsimp [p]
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, ← Category.assoc, (ρ g).comm, Category.assoc, hs₀,
        Category.assoc]
    have hcycle (x : K.X (q+1)) : K.d (q+1) q (p x) = 0 := by
      have hdx : K.d q (q-1) (K.d (q+1) q x) = 0 :=
        congrArg (fun f => f x) (K.d_comp_d (q+1) q (q-1))
      change K.d (q+1) q (x - s₀ (K.d (q+1) q x)) = 0
      rw [map_sub, hd₀ _ hdx, sub_self]
    obtain ⟨s, hs, hd⟩ := exists_equivariant_lift_of_basis ρ law (q+1) (b (q+1))
      (hb (q+1)) (hK (q+1) hq) p hp (by simpa using hcycle)
    refine ⟨s, hs, fun x hx => ?_⟩
    change K.d (q+1) q x = 0 at hx
    have he := congrArg (fun f => f x) hd
    change K.d (q+1+1) (q+1) (s x) = x - s₀ (K.d (q+1) q x) at he
    simpa only [hx, map_zero, sub_zero] using he

end NRR.PrimePowerTopology
