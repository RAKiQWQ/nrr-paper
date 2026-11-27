/-
Copyright (c) 2026 Joël Riou and Jack McCarthy.
Released under Apache 2.0 license.

The recursive cone homotopy adapts Hatcher/Excision/AffineChains.lean from
akopjan/toptverbert-nandakumar, revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
The construction is expressed directly using Mathlib 4.24 topological simplices.
-/
import NRR.SingularHomologyAffineChains

noncomputable section
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
namespace NRR.SingularHomology
open SimplexGeometry
variable (R : Type) [Ring R]

/-- The cone contraction identity in strictly positive degrees. -/
theorem vertexChain_d_comp_cone_add_cone_comp_d {Y : Type} (y : Y) {n : ℕ} :
    (CsingSSet R (vertexSSet Y)).d (n + 1) n ≫ vertexChainCone R y n +
      vertexChainCone R y (n + 1) ≫ (CsingSSet R (vertexSSet Y)).d (n + 2) (n + 1) =
        𝟙 _ := by
  have h := (((vertexExtraDegeneracy y).map
    (sigmaConst.obj (ModuleCat.of R R))).homotopyEquiv.homotopyHomInvId.symm.comm (n + 1)).symm
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex] at h
  simpa [-AlternatingFaceMapComplex.obj_d_eq,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, vertexChainCone] using h

/-- The image of the center under an affine simplex. -/
def affineCenter {n m : ℕ} (v : Fin (n + 1) → Simplex m) : Simplex m :=
  affine v (faceCenter Finset.univ (Finset.univ_nonempty))

/-- Affine maps preserve the center computed from barycentric coordinates. -/
theorem affineCenter_naturality {n m k : ℕ} (v : Fin (n + 1) → Simplex m)
    (w : Fin (m + 1) → Simplex k) :
    affineCenter (affine w ∘ v) = affine w (affineCenter v) := by
  exact (congrArg (fun f : C(Simplex n, Simplex k) =>
    f (faceCenter Finset.univ Finset.univ_nonempty)) (affine_comp v w)).symm

/-- The recursive degree-raising operator defining the subdivision homotopy. -/
def affineSubdivisionAux (m : ℕ) (n : ℕ) :
    (CsingSSet R (vertexSSet (Simplex m))).X n ⟶
      (CsingSSet R (vertexSSet (Simplex m))).X (n + 1) :=
  Nat.rec (motive := fun n =>
      (CsingSSet R (vertexSSet (Simplex m))).X n ⟶
        (CsingSSet R (vertexSSet (Simplex m))).X (n + 1))
    0
    (fun n h => ccDesc R fun v =>
      (simplexι R v - simplexι R v ≫
        (CsingSSet R (vertexSSet (Simplex m))).d (n + 1) n ≫ h) ≫
        vertexChainCone R (affineCenter v) (n + 1)) n

@[simp] theorem affineSubdivisionAux_zero (m : ℕ) : affineSubdivisionAux R m 0 = 0 := rfl

@[reassoc (attr := simp)] theorem simplexι_affineSubdivisionAux_succ {m n : ℕ}
    (v : Fin (n + 2) → Simplex m) :
    simplexι R (Y := vertexSSet (Simplex m)) v ≫ affineSubdivisionAux R m (n + 1) =
      (simplexι R v - simplexι R v ≫
        (CsingSSet R (vertexSSet (Simplex m))).d (n + 1) n ≫ affineSubdivisionAux R m n) ≫
        vertexChainCone R (affineCenter v) (n + 1) :=
  ι_ccDesc R _ _

/-- The recursive homotopy, extended by zero off the adjacent degree. -/
def affineSubdivisionComponent (m : ℕ) (n k : ℕ) :
    (CsingSSet R (vertexSSet (Simplex m))).X n ⟶
      (CsingSSet R (vertexSSet (Simplex m))).X k :=
  if h : n + 1 = k then affineSubdivisionAux R m n ≫ eqToHom (by rw [h]) else 0

@[simp] theorem affineSubdivisionComponent_eq (m n : ℕ) :
    affineSubdivisionComponent R m n (n + 1) = affineSubdivisionAux R m n := by
  simp [affineSubdivisionComponent]

theorem affineSubdivisionComponent_zero (m n k : ℕ) (h : n + 1 ≠ k) :
    affineSubdivisionComponent R m n k = 0 := by
  simp [affineSubdivisionComponent, h]

/-- Barycentric subdivision on affine vertex chains, obtained from the actual
cone homotopy. The chain-map relation is built into `nullHomotopicMap`. -/
def affineChainSubdivision (m : ℕ) :
    CsingSSet R (vertexSSet (Simplex m)) ⟶ CsingSSet R (vertexSSet (Simplex m)) :=
  𝟙 _ - Homotopy.nullHomotopicMap (affineSubdivisionComponent R m)

/-- The actual chain homotopy from the identity to affine subdivision. -/
def affineChainHomotopyIdSubdivision (m : ℕ) :
    Homotopy (𝟙 _) (affineChainSubdivision R m) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [affineChainSubdivision]))
      (.nullHomotopy (affineSubdivisionComponent R m)
        (affineSubdivisionComponent_zero R m)))

@[simp] theorem affineChainSubdivision_f_zero (m : ℕ) :
    (affineChainSubdivision R m).f 0 = 𝟙 _ := by
  simp [affineChainSubdivision,
    Homotopy.nullHomotopicMap_f_of_not_rel_left
      (ComplexShape.down_mk 1 0 rfl) (by simp)]

theorem affineChainSubdivision_f_succ (m n : ℕ) :
    (affineChainSubdivision R m).f (n + 1) = 𝟙 _ -
      (CsingSSet R (vertexSSet (Simplex m))).d (n + 1) n ≫ affineSubdivisionAux R m n -
      affineSubdivisionAux R m (n + 1) ≫
        (CsingSSet R (vertexSSet (Simplex m))).d (n + 2) (n + 1) := by
  simp [affineChainSubdivision,
    Homotopy.nullHomotopicMap_f (ComplexShape.down_mk (n + 2) (n + 1) rfl)
      (ComplexShape.down_mk (n + 1) n rfl), sub_sub, affineSubdivisionComponent_eq]

/-- Subdivision acts as the identity on actual affine-chain homology. -/
theorem affineChainSubdivision_homologyMap (m n : ℕ) :
    HomologicalComplex.homologyMap (affineChainSubdivision R m) n = 𝟙 _ := by
  rw [← (affineChainHomotopyIdSubdivision R m).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

/-- The recursive cone operator commutes with affine maps of its target simplex. -/
@[reassoc] theorem affineSubdivisionAux_naturality {m k : ℕ}
    (w : Fin (m + 1) → Simplex k) (n : ℕ) :
    (simplicialChainMap R (vertexMap (affine w))).f n ≫ affineSubdivisionAux R k n =
      affineSubdivisionAux R m n ≫
        (simplicialChainMap R (vertexMap (affine w))).f (n + 1) := by
  induction n with
  | zero => simp
  | succ n hn =>
    apply simplicialChain_hom_ext R
    intro v
    simp only [simplexι_affineSubdivisionAux_succ_assoc,
      ← vertexChainCone_naturality, Preadditive.sub_comp, Category.assoc,
      ← reassoc_of% hn, simplexι_chainMap_f_assoc,
      simplexι_affineSubdivisionAux_succ, vertexMap_app,
      ← (simplicialChainMap R (vertexMap (affine w))).comm_assoc]
    simp only [affineCenter_naturality]

/-- Naturality of every component of the affine subdivision homotopy. -/
@[reassoc] theorem affineSubdivisionComponent_naturality {m k : ℕ}
    (w : Fin (m + 1) → Simplex k) (n l : ℕ) :
    (simplicialChainMap R (vertexMap (affine w))).f n ≫
        affineSubdivisionComponent R k n l =
      affineSubdivisionComponent R m n l ≫
        (simplicialChainMap R (vertexMap (affine w))).f l := by
  by_cases h : n + 1 = l
  · subst h
    simp only [affineSubdivisionComponent_eq, affineSubdivisionAux_naturality]
  · simp [affineSubdivisionComponent_zero, h]

/-- Subdivision commutes with actual affine maps between standard simplices. -/
theorem affineChainSubdivision_naturality {m k : ℕ}
    (w : Fin (m + 1) → Simplex k) :
    simplicialChainMap R (vertexMap (affine w)) ≫ affineChainSubdivision R k =
      affineChainSubdivision R m ≫ simplicialChainMap R (vertexMap (affine w)) := by
  simp only [affineChainSubdivision, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp]
  congr 1
  rw [Homotopy.comp_nullHomotopicMap, Homotopy.nullHomotopicMap_comp]
  congr 1
  funext n l
  exact affineSubdivisionComponent_naturality R w n l

/-- A convenient rearrangement of the cone contraction. -/
theorem vertexChain_cone_comp_d_eq_sub {Y : Type} (y : Y) {n : ℕ} :
    vertexChainCone R y (n + 1) ≫ (CsingSSet R (vertexSSet Y)).d (n + 2) (n + 1) =
      𝟙 _ - (CsingSSet R (vertexSSet Y)).d (n + 1) n ≫ vertexChainCone R y n := by
  rw [← vertexChain_d_comp_cone_add_cone_comp_d R y]
  abel

/-- The subdivision of a positive-dimensional generator is the cone on the
subdivision of its boundary, with the original center as cone point. -/
@[reassoc] theorem simplexι_affineChainSubdivision_f_succ {m n : ℕ}
    (v : Fin (n + 2) → Simplex m) :
    simplexι R (Y := vertexSSet (Simplex m)) v ≫ (affineChainSubdivision R m).f (n + 1) =
      simplexι R v ≫ (CsingSSet R (vertexSSet (Simplex m))).d (n + 1) n ≫
        (affineChainSubdivision R m).f n ≫ vertexChainCone R (affineCenter v) n := by
  obtain _ | n := n
  · simp [affineChainSubdivision_f_succ, vertexChain_cone_comp_d_eq_sub]
  · simp [affineChainSubdivision_f_succ,
      simplexι_affineSubdivisionAux_succ_assoc, vertexChain_cone_comp_d_eq_sub]

/-- A finite recursive index for barycentric subsimplices, avoiding any
choice of coordinates or permutations in the chain formulas. -/
def SubdivisionIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin (n + 2) × SubdivisionIndex n

instance subdivisionIndexFintype : ∀ n, Fintype (SubdivisionIndex n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := subdivisionIndexFintype n
    exact inferInstanceAs (Fintype (Fin (n + 2) × SubdivisionIndex n))

/-- The actual vertices of each recursively defined barycentric subsimplex. -/
def subdivisionVertices {m : ℕ} : (n : ℕ) →
    (Fin (n + 1) → Simplex m) → SubdivisionIndex n → (Fin (n + 1) → Simplex m)
  | 0, v, _ => v
  | n + 1, v, ⟨i, s⟩ => Fin.cases (affineCenter v)
      (subdivisionVertices n (fun j => v (i.succAbove j)) s)

/-- The incidence sign of a recursively indexed subsimplex. -/
def subdivisionSign : (n : ℕ) → SubdivisionIndex n → ℤ
  | 0, _ => 1
  | n + 1, ⟨i, s⟩ => (-1) ^ i.val * subdivisionSign n s

/-- Explicit finite formula for the actual subdivision chain map. -/
@[reassoc] theorem simplexι_affineChainSubdivision_eq_sum {m n : ℕ}
    (v : Fin (n + 1) → Simplex m) :
    simplexι R (Y := vertexSSet (Simplex m)) v ≫ (affineChainSubdivision R m).f n =
      ∑ s : SubdivisionIndex n,
        subdivisionSign n s • simplexι R (Y := vertexSSet (Simplex m))
          (subdivisionVertices n v s) := by
  induction n with
  | zero => simp [SubdivisionIndex, subdivisionSign, subdivisionVertices]
  | succ n ih =>
    rw [simplexι_affineChainSubdivision_f_succ]
    simp only [simplexι_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
      vertexSSet_delta, reassoc_of% ih, Finset.smul_sum, Preadditive.sum_comp, Preadditive.zsmul_comp,
      simplexι_vertexChainCone, smul_smul]
    simp only [SubdivisionIndex, Fintype.sum_prod_type, subdivisionSign, subdivisionVertices]
    rfl

end NRR.SingularHomology
