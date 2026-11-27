import NRR.PrimePowerTopologyAssociatedEuler
import NRR.PrimePowerTopologyCompactification

/-!
The fiberwise graph homotopies extend continuously to the actual one-point
compactifications, uniformly in the homotopy parameter.  The key fact is
that the base coordinate is unchanged: projecting any compact set in the
product supplies one compact exceptional set valid for every parameter.
This is the proper-homotopy input needed for Borel--Moore Euler comparison.
-/

noncomputable section
open Set Topology Filter CategoryTheory
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology

namespace NRR.PrimePowerTopology

section GraphFamily
variable {T X V : Type*} [TopologicalSpace T] [TopologicalSpace X]
  [TopologicalSpace V] [T2Space X]

/-- Compactify an arbitrary base-preserving family of graphs. -/
def onePointGraphFamily (F : T × X → V) : T × OnePoint X → OnePoint (X × V) :=
  fun p => p.2.elim ∞ (fun x => ((x,F (p.1,x)) : X × V))

omit [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace V] [T2Space X] in
@[simp] theorem onePointGraphFamily_infty (F : T × X → V) (t : T) :
    onePointGraphFamily F (t,∞) = ∞ := rfl

omit [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace V] [T2Space X] in
@[simp] theorem onePointGraphFamily_coe (F : T × X → V) (t : T) (x : X) :
    onePointGraphFamily F (t,(x : OnePoint X)) = ((x,F (t,x)) : X × V) := rfl

/-- Joint continuity at infinity follows from projection of compact sets;
no bound on the vector-valued family and no compactness of T is needed. -/
theorem continuous_onePointGraphFamily {F : T × X → V} (hF : Continuous F) :
    Continuous (onePointGraphFamily F) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,z⟩
  induction z using OnePoint.rec with
  | infty =>
    change Filter.map (onePointGraphFamily F) (𝓝 (t,(∞ : OnePoint X))) ≤ 𝓝 ∞
    apply OnePoint.le_nhds_infty.mpr
    intro K hKc hKk
    let A : Set X := Prod.fst '' K
    have hAk : IsCompact A := hKk.image continuous_fst
    have hAc : IsClosed A := hAk.isClosed
    have hV : (((↑) : X → OnePoint X) '' A)ᶜ ∈ 𝓝 (∞ : OnePoint X) := by
      apply (OnePoint.isOpen_compl_image_coe.mpr ⟨hAc,hAk⟩).mem_nhds
      rintro ⟨x,hx,heq⟩
      exact OnePoint.coe_ne_infty x heq
    have hW : (Set.univ : Set T) ×ˢ (((↑) : X → OnePoint X) '' A)ᶜ ∈
        𝓝 (t,(∞ : OnePoint X)) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod Filter.univ_mem hV
    apply Filter.mem_of_superset hW
    rintro ⟨u,w⟩ ⟨_,hw⟩
    induction w using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe x =>
      apply Or.inl
      refine ⟨(x,F (u,x)),?_,rfl⟩
      intro hxK
      exact hw ⟨x,⟨(x,F (u,x)),hxK,rfl⟩,rfl⟩
  | coe x =>
    have he : IsOpenEmbedding
        (Prod.map (id : T → T) ((↑) : X → OnePoint X)) :=
      IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
    apply (he.continuousAt_iff (g := onePointGraphFamily F) (x := (t,x))).mp
    change ContinuousAt (fun p : T × X =>
      (((p.2,F p) : X × V) : OnePoint (X × V))) (t,x)
    exact (OnePoint.continuous_coe.comp (continuous_snd.prodMk hF)).continuousAt

def onePointGraph (f : C(X,V)) : C(OnePoint X,OnePoint (X × V)) :=
  ⟨fun z => onePointGraphFamily (fun p : Unit × X => f p.2) ((),z),
    (continuous_onePointGraphFamily (f.continuous.comp continuous_snd)).comp
      (continuous_const.prodMk continuous_id)⟩

@[simp] theorem onePointGraph_infty (f : C(X,V)) : onePointGraph f ∞ = ∞ := rfl
@[simp] theorem onePointGraph_coe (f : C(X,V)) (x : X) :
    onePointGraph f (x : OnePoint X) = ((x,f x) : X × V) := rfl

end GraphFamily

/-- The actual compactified graph-to-zero proper homotopy. -/
def associatedCompactGraphZeroHomotopy {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) :
    ContinuousMap.Homotopy (onePointGraph f)
      (onePointGraph (ContinuousMap.const (Configuration d n) (0 : ReducedValues d n))) where
  toFun := onePointGraphFamily (fun p : unitInterval × Configuration d n =>
    (1-(p.1 : ℝ)) • f p.2)
  continuous_toFun := continuous_onePointGraphFamily
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (f.continuous.comp continuous_snd))
  map_zero_left z := by
    induction z using OnePoint.rec with
    | infty => rfl
    | coe x => simp
  map_one_left z := by
    induction z using OnePoint.rec with
    | infty => rfl
    | coe x => simp

@[simp] theorem associatedCompactGraphZeroHomotopy_infty {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (t : unitInterval) :
    associatedCompactGraphZeroHomotopy f (t,∞) = ∞ := rfl

@[simp] theorem associatedCompactGraphZeroHomotopy_coe {d n : ℕ}
    (f : C(Configuration d n,ReducedValues d n)) (t : unitInterval)
    (x : Configuration d n) :
    associatedCompactGraphZeroHomotopy f (t,(x : OnePoint (Configuration d n))) =
      ((x,(1-(t : ℝ)) • f x) : AssociatedCover d n) := rfl

end NRR.PrimePowerTopology