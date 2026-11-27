/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

The diameter estimate and Lebesgue-number strategy follow
Hatcher/Excision/SubdivisionDiameter.lean and SmallSimplices.lean by
Joël Riou and Jack McCarthy in akopjan/toptverbert-nandakumar,
revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
The coordinate proof is adapted to Mathlib 4.24's actual NNReal simplices
and this project's recursively signed SubdivisionIndex, rather than the
upstream ConvexSpace/StdSimplex and permutation representation.
-/
import NRR.SingularHomologySubdivisionFormula
import NRR.SingularHomologySmallChains
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-! Coordinate estimates for the actual recursive barycentric subsimplices. -/
noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite Set
namespace NRR.SingularHomology.SimplexGeometry

instance simplex_compactSpace (n : ℕ) : CompactSpace (Simplex n) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : Fin (n+1) → NNReal | ∑ i, x i = 1}
  apply (isCompact_Icc (a := (0 : Fin (n+1) → NNReal)) (b := 1)).of_isClosed_subset
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro x hx
    refine ⟨fun i => bot_le, fun i => ?_⟩
    have hi : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => zero_le (x j)) (Finset.mem_univ i)
    change ∑ j, x j = 1 at hx
    change x i ≤ 1
    exact hi.trans_eq hx
theorem affine_coordinate_bound {n m : ℕ} (v : Fin (n+1) → Simplex m)
    (x : Simplex n) (j : Fin (m+1)) (c D : ℝ)
    (bound : ∀ i, |(v i j : ℝ)-c| ≤ D) :
    |(affine v x j : ℝ)-c| ≤ D := by
  have total : ∑ i : Fin (n+1), (x i : ℝ) = 1 := by exact_mod_cast x.property
  have expr : (affine v x j : ℝ)-c =
      ∑ i : Fin (n+1), (x i : ℝ)*((v i j : ℝ)-c) := by
    simp only [affine_apply, NNReal.coe_sum, NNReal.coe_mul,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, total, one_mul]
    rfl
  rw [expr]
  calc
    _ ≤ ∑ i : Fin (n+1), |(x i : ℝ)*((v i j : ℝ)-c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n+1), (x i : ℝ)*D := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (x i).coe_nonneg]
      exact mul_le_mul_of_nonneg_left (bound i) (x i).coe_nonneg
    _ = D := by rw [← Finset.sum_mul, total, one_mul]

theorem affineCenter_coordinate {n m : ℕ} (v : Fin (n+1) → Simplex m)
    (j : Fin (m+1)) :
    (affineCenter v j : ℝ) = (n+1 : ℝ)⁻¹ * ∑ i, (v i j : ℝ) := by
  simp [affineCenter, affine_apply, faceCenter_apply, ← Finset.mul_sum]
  left
  rfl

theorem affineCenter_vertex_coordinate_bound {n m : ℕ}
    (v : Fin (n+1) → Simplex m) (j : Fin (m+1)) (D : ℝ)
    (bound : ∀ a b, |(v a j : ℝ)-(v b j : ℝ)| ≤ D) (a : Fin (n+1)) :
    |(affineCenter v j : ℝ)-(v a j : ℝ)| ≤ (n : ℝ)/(n+1)*D := by
  have expr : (affineCenter v j : ℝ)-(v a j : ℝ) =
      (n+1 : ℝ)⁻¹ * ∑ i : Fin (n+1), ((v i j : ℝ)-(v a j : ℝ)) := by
    rw [affineCenter_coordinate, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hsum : (∑ i : Fin (n+1), |(v i j : ℝ)-(v a j : ℝ)|) ≤ (n : ℝ)*D := by
    calc
      _ = ∑ i ∈ Finset.univ.erase a, |(v i j : ℝ)-(v a j : ℝ)| := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ a)]
        simp
      _ ≤ ∑ i ∈ Finset.univ.erase a, D := Finset.sum_le_sum (fun i _ => bound i a)
      _ = _ := by simp
  rw [expr, abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n+1))]
  calc
    _ ≤ (n+1 : ℝ)⁻¹ * (∑ i : Fin (n+1), |(v i j : ℝ)-(v a j : ℝ)|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (n+1 : ℝ)⁻¹ * ((n : ℝ)*D) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem subdivisionVertices_coordinate_bound {m : ℕ} :
    ∀ (n : ℕ) (v : Fin (n+1) → Simplex m) (a : SubdivisionIndex n)
      (i : Fin (n+1)) (j : Fin (m+1)) (c D : ℝ),
      (∀ k, |(v k j : ℝ)-c| ≤ D) →
      |(subdivisionVertices n v a i j : ℝ)-c| ≤ D
  | 0, v, a, i, j, c, D, bound => bound i
  | n+1, v, a, i, j, c, D, bound => by
    rcases a with ⟨k, a⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact affine_coordinate_bound v _ j c D bound
    · exact subdivisionVertices_coordinate_bound n (fun t => v (k.succAbove t))
        a i j c D (fun t => bound (k.succAbove t))

/-- One recursive barycentric subdivision contracts every coordinate
diameter by n/(n+1), uniformly in the chosen signed subsimplex. -/
theorem subdivisionVertices_coordinate_diameter {m : ℕ} :
    ∀ (n : ℕ) (v : Fin (n+1) → Simplex m) (a : SubdivisionIndex n)
      (j : Fin (m+1)) (D : ℝ), 0 ≤ D →
      (∀ k l, |(v k j : ℝ)-(v l j : ℝ)| ≤ D) →
      ∀ k l, |(subdivisionVertices n v a k j : ℝ)-
        (subdivisionVertices n v a l j : ℝ)| ≤ (n : ℝ)/(n+1)*D
  | 0, v, a, j, D, hD, bound, k, l => by
    have hk : k = 0 := Fin.ext (by omega)
    have hl : l = 0 := Fin.ext (by omega)
    simp [subdivisionVertices, hk, hl]
  | n+1, v, a, j, D, hD, bound, k, l => by
    rcases a with ⟨q, a⟩
    have center (t : Fin (n+2)) :=
      affineCenter_vertex_coordinate_bound v j D bound t
    have fromCenter (i : Fin (n+1)) :
        |(subdivisionVertices n (fun t => v (q.succAbove t)) a i j : ℝ)-
          (affineCenter v j : ℝ)| ≤ ((n+1 : ℕ) : ℝ)/((n+1 : ℕ)+1)*D := by
      apply subdivisionVertices_coordinate_bound
      intro t
      rw [abs_sub_comm]
      exact center (q.succAbove t)
    refine Fin.cases ?_ (fun k => ?_) k <;>
      refine Fin.cases ?_ (fun l => ?_) l
    · simp only [subdivisionVertices, Fin.cases_zero, sub_self, abs_zero]
      positivity
    · simpa only [subdivisionVertices, Fin.cases_zero, Fin.cases_succ, abs_sub_comm]
        using fromCenter l
    · simpa only [subdivisionVertices, Fin.cases_zero, Fin.cases_succ]
        using fromCenter k
    · have ih := subdivisionVertices_coordinate_diameter n
        (fun t => v (q.succAbove t)) a j D hD (fun b c => bound _ _) k l
      have ratio : (n : ℝ)/(n+1) ≤ (n+1)/((n+1)+1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact ih.trans (mul_le_mul_of_nonneg_right (by simpa using ratio) hD)


/-- A coordinate diameter bounds the distance between any two affine points. -/
theorem affine_dist_le_of_coordinate_bound {n m : ℕ}
    (v : Fin (n+1) → Simplex m) (D : ℝ) (hD : 0 ≤ D)
    (bound : ∀ a b j, |(v a j : ℝ)-(v b j : ℝ)| ≤ D)
    (x y : Simplex n) : dist (affine v x) (affine v y) ≤ D := by
  change dist (affine v x).val (affine v y).val ≤ D
  rw [dist_pi_le_iff hD]
  intro j
  rw [NNReal.dist_eq]
  apply affine_coordinate_bound v x j (affine v y j : ℝ) D
  intro a
  rw [abs_sub_comm]
  exact affine_coordinate_bound v y j (v a j : ℝ) D (fun b => bound b a j)

/-- Iterated actual barycentric vertex lists, keeping the chain formula's index. -/
def subdivisionVerticesIter {m : ℕ} (n : ℕ) :
    (k : ℕ) → (Fin (n+1) → Simplex m) →
      (Fin k → SubdivisionIndex n) → (Fin (n+1) → Simplex m)
  | 0, v, _ => v
  | k+1, v, a => subdivisionVertices n
      (subdivisionVerticesIter n k v (fun i => a i.succ)) (a 0)

theorem subdivisionVerticesIter_coordinate_diameter {m : ℕ} (n : ℕ) :
    ∀ (k : ℕ) (v : Fin (n+1) → Simplex m) (a : Fin k → SubdivisionIndex n)
      (j : Fin (m+1)) (D : ℝ), 0 ≤ D →
      (∀ b c, |(v b j : ℝ)-(v c j : ℝ)| ≤ D) →
      ∀ b c, |(subdivisionVerticesIter n k v a b j : ℝ)-
        (subdivisionVerticesIter n k v a c j : ℝ)| ≤
          ((n : ℝ)/(n+1))^k*D
  | 0, v, a, j, D, hD, bound, b, c => by simpa [subdivisionVerticesIter] using bound b c
  | k+1, v, a, j, D, hD, bound, b, c => by
    have ih := subdivisionVerticesIter_coordinate_diameter n k v
      (fun i => a i.succ) j D hD bound
    have hbound := subdivisionVertices_coordinate_diameter n
      (subdivisionVerticesIter n k v (fun i => a i.succ)) (a 0) j
      (((n : ℝ)/(n+1))^k*D) (by positivity) ih b c
    calc
      _ ≤ ((n : ℝ)/(n+1))*(((n : ℝ)/(n+1))^k*D) := hbound
      _ = _ := by rw [pow_succ]; ring

theorem affine_subdivisionVerticesIter_dist (n k : ℕ)
    (a : Fin k → SubdivisionIndex n) (x y : Simplex n) :
    dist (affine (subdivisionVerticesIter n k (vertex n) a) x)
      (affine (subdivisionVerticesIter n k (vertex n) a) y) ≤
        ((n : ℝ)/(n+1))^k := by
  apply affine_dist_le_of_coordinate_bound _ _ (by positivity)
  intro b c j
  have h := subdivisionVerticesIter_coordinate_diameter n k (vertex n) a j 1
    (by norm_num) (fun b c => ?_) b c
  · simpa only [mul_one] using h
  · simp only [vertex_apply]
    split_ifs <;> norm_num

/-- Recursive subdivision commutes with actual affine coordinate maps. -/
theorem subdivisionVertices_affine {m l : ℕ}
    (w : Fin (m+1) → Simplex l) :
    ∀ (n : ℕ) (v : Fin (n+1) → Simplex m) (a : SubdivisionIndex n),
      subdivisionVertices n (fun i => affine w (v i)) a =
        fun i => affine w (subdivisionVertices n v a i)
  | 0, v, a => rfl
  | n+1, v, a => by
    rcases a with ⟨q,a⟩
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact affineCenter_naturality v w
    · exact congrFun (subdivisionVertices_affine w n
        (fun j => v (q.succAbove j)) a) i

theorem affine_comp_subdivisionVertices {n m : ℕ}
    (v : Fin (n+1) → Simplex m) (a : SubdivisionIndex n) :
    (affine v).comp (affine (subdivisionVertices n (vertex n) a)) =
      affine (subdivisionVertices n v a) := by
  rw [affine_comp]
  congr 1
  have h := subdivisionVertices_affine v n (vertex n) a
  simpa only [affine_vertex] using h.symm

end NRR.SingularHomology.SimplexGeometry

namespace NRR.SingularHomology
open SimplexGeometry

def subdivisionSimplexIter {X : TopCat.{0}} {n : ℕ} :
    (k : ℕ) → TopCat.toSSet.obj X _⦋n⦌ →
      (Fin k → SubdivisionIndex n) → TopCat.toSSet.obj X _⦋n⦌
  | 0, s, _ => s
  | k+1, s, a => subdivisionSimplex (subdivisionSimplexIter k s (fun i => a i.succ)) (a 0)

theorem simplexTopMap_subdivisionSimplexIter {X : TopCat.{0}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    ∀ (k : ℕ) (a : Fin k → SubdivisionIndex n),
      simplexTopMap (subdivisionSimplexIter k s a) =
        TopCat.ofHom (affine (subdivisionVerticesIter n k (vertex n) a)) ≫ simplexTopMap s
  | 0, a => by simp [subdivisionSimplexIter, subdivisionVerticesIter, affine_vertices]
  | k+1, a => by
    rw [subdivisionSimplexIter, simplexTopMap_subdivisionSimplex,
      simplexTopMap_subdivisionSimplexIter s k]
    rw [← Category.assoc]
    congr 1
    change TopCat.ofHom ((affine (subdivisionVerticesIter n k (vertex n)
      (fun i => a i.succ))).comp (affine (subdivisionVertices n (vertex n) (a 0)))) = _
    rw [affine_comp_subdivisionVertices]
    rfl

/-- A family whose interiors cover the ambient space. -/
structure SmallSimplicesCondition {X : TopCat.{0}} {ι : Type} (U : ι → Set X) : Prop where
  iUnion_interior : ⋃ i, interior (U i) = univ

/-- Every actual singular simplex eventually subdivides into simplices lying
in members of an arbitrary cover by interiors. -/
theorem exists_subdivisionSimplexIter_small {X : TopCat.{0}} {ι : Type}
    (U : ι → Set X) (cover : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ k, ∀ a : Fin k → SubdivisionIndex n,
      subdivisionSimplexIter k s a ∈ (smallSubcomplex U).obj _ := by
  let V (i : ι) : Set (Simplex n) := simplexTopMap s ⁻¹' interior (U i)
  have hV (i) : IsOpen (V i) := isOpen_interior.preimage (simplexTopMap s).hom.continuous
  have covers : (univ : Set (Simplex n)) ⊆ ⋃ i, V i := by
    intro x _
    have hx : simplexTopMap s x ∈ ⋃ i, interior (U i) := by rw [cover.iUnion_interior]; trivial
    simpa only [mem_iUnion, V, mem_preimage] using hx
  obtain ⟨ε, hε, radius⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV covers
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
    (y := (n : ℝ)/(n+1)) (by rw [div_lt_one (by positivity)]; linarith)
  refine ⟨k, fun a => ?_⟩
  let f := affine (subdivisionVerticesIter n k (vertex n) a)
  obtain ⟨i, hi⟩ := radius (f (vertex n 0)) (mem_univ _)
  rw [mem_smallSubcomplex_iff]
  refine ⟨i, ?_⟩
  rintro y ⟨x, rfl⟩
  have hx : f x ∈ Metric.ball (f (vertex n 0)) ε :=
    (affine_subdivisionVerticesIter_dist n k a x (vertex n 0)).trans_lt hk
  have him := hi hx
  have heq := congrArg (fun q : TopCat.of (Simplex n) ⟶ X => q x)
    (simplexTopMap_subdivisionSimplexIter s k a)
  change simplexTopMap (subdivisionSimplexIter k s a) x ∈ U i
  change simplexTopMap (subdivisionSimplexIter k s a) x = simplexTopMap s (f x) at heq
  exact heq.symm ▸ interior_subset him

end NRR.SingularHomology

