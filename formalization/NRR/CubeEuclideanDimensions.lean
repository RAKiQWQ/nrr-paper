import NRR.CubeAllDimensions
import NRR.Statement

/-! The uniform cube construction in the manuscript's Euclidean spaces.
All characteristics are defined on all nonempty compact convex sets. -/

noncomputable section
open Set Topology MeasureTheory
open scoped NNReal

namespace NRR.CubeEuclideanDimensions
open CubeProductMoments CubeAllDimensions Coordinates

private def activeLinear : (Fin 3 → ℝ) ≃ₗ[ℝ] Active where
  toFun x := ((x 0,x 1),x 2)
  invFun p := ![p.1.1,p.1.2,p.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def activeCoordinates : Space 3 ≃L[ℝ] Active :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).trans
    activeLinear.toContinuousLinearEquiv

/-- The first three coordinates are active; every later coordinate is
passive. This is the ordinary coordinate splitting of Euclidean space. -/
def baseCoordinates (k : ℕ) : Space (3+k) ≃L[ℝ] Ambient k :=
  (EuclideanSpace.finAddEquivProd (n := 3) (m := k)).trans
    (activeCoordinates.prodCongr
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)))

theorem baseCoordinates_apply (k : ℕ) (x : Space (3+k)) :
    baseCoordinates k x =
      (((x (Fin.castAdd k (0 : Fin 3)),x (Fin.castAdd k (1 : Fin 3))),
        x (Fin.castAdd k (2 : Fin 3))), fun j => x (Fin.natAdd 3 j)) := by
  rfl

def baseCube (k : ℕ) : Set (Space (3+k)) :=
  baseCoordinates k ⁻¹' (CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k)

theorem mem_baseCube_iff (k : ℕ) (x : Space (3+k)) :
    x ∈ baseCube k ↔ ∀ j, x j ∈ Icc (-1 : ℝ) 1 := by
  rw [baseCube, mem_preimage, baseCoordinates_apply]
  change (((x (Fin.castAdd k (0 : Fin 3)) ∈ Icc (-1 : ℝ) 1 ∧
      x (Fin.castAdd k (1 : Fin 3)) ∈ Icc (-1 : ℝ) 1) ∧
      x (Fin.castAdd k (2 : Fin 3)) ∈ Icc (-1 : ℝ) 1) ∧
      ((∀ j, -1 ≤ x (Fin.natAdd 3 j)) ∧
        (∀ j, x (Fin.natAdd 3 j) ≤ 1))) ↔ _
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,lo,hi⟩ j
    refine Fin.addCases (fun i => ?_) (fun i => ⟨lo i,hi i⟩) j
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨⟨h _,h _⟩,h _⟩,fun i => (h _).1,fun i => (h _).2⟩

theorem baseCube_eq_standardCube (k : ℕ) :
    baseCube k = {x : Space (3+k) | ∀ j, x j ∈ Icc (-1 : ℝ) 1} := by
  ext x
  exact mem_baseCube_iff k x

def coordinatePerm (k : ℕ) : Equiv.Perm (Fin (3+k)) where
  toFun j := if h₁ : j.val < 2 then j else if h₂ : j.val = 2 then ⟨2+k,by omega⟩
    else ⟨j.val-1,by omega⟩
  invFun j := if h₁ : j.val < 2 then j else if h₂ : j.val = 2+k then ⟨2,by omega⟩
    else ⟨j.val+1,by omega⟩
  left_inv j := by
    ext
    dsimp
    split_ifs <;> dsimp at *
    all_goals try omega
    · rename_i h
      exact False.elim (h rfl)
    · rename_i h
      change j.val-1 = 2+k at h
      omega
  right_inv j := by ext; dsimp; split_ifs <;> dsimp at * <;> omega

def permute (k : ℕ) : Space (3+k) ≃ₗᵢ[ℝ] Space (3+k) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coordinatePerm k).symm

@[simp] theorem permute_apply (k : ℕ) (x : Space (3+k)) (j : Fin (3+k)) :
    permute k x j = x (coordinatePerm k j) := rfl

/-- The manuscript's coordinates: `x₁,x₂,z=x_d` are active and the
remaining coordinates `x₃,…,x_{d-1}` stay in their natural passive order. -/
def E (k : ℕ) : Space (3+k) ≃L[ℝ] Ambient k :=
  (permute k).toContinuousLinearEquiv.trans (baseCoordinates k)

theorem E_apply (k : ℕ) (x : Space (3+k)) :
    E k x = (((x (Fin.castAdd k (0 : Fin 3)),x (Fin.castAdd k (1 : Fin 3))),
      x ⟨2+k,by omega⟩), fun j => x ⟨j.val+2,by omega⟩) := by
  change baseCoordinates k (permute k x) = _
  rw [baseCoordinates_apply]
  simp only [permute_apply]
  have low (j : Fin 3) (hj : j.val < 2) :
      coordinatePerm k (Fin.castAdd k j) = Fin.castAdd k j := by
    simp [coordinatePerm,hj]
  have top : coordinatePerm k (Fin.castAdd k (2 : Fin 3)) = ⟨2+k,by omega⟩ := by
    rfl
  have mid (j : Fin k) : coordinatePerm k (Fin.natAdd 3 j) = ⟨j.val+2,by omega⟩ := by
    apply Fin.ext
    dsimp [coordinatePerm]
    split_ifs <;> dsimp at * <;> omega
  exact Prod.ext
    (Prod.ext (Prod.ext (congrArg x (low 0 (by decide)))
      (congrArg x (low 1 (by decide)))) (congrArg x top))
    (funext fun j => congrArg x (mid j))

def cube (k : ℕ) : Set (Space (3+k)) :=
  E k ⁻¹' (CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k)

theorem mem_cube_iff (k : ℕ) (x : Space (3+k)) :
    x ∈ cube k ↔ ∀ j, x j ∈ Icc (-1 : ℝ) 1 := by
  change permute k x ∈ baseCube k ↔ _
  rw [mem_baseCube_iff]
  constructor
  · intro h j
    have hv := h ((coordinatePerm k).symm j)
    change x ((coordinatePerm k) ((coordinatePerm k).symm j)) ∈ Icc (-1 : ℝ) 1 at hv
    rwa [(coordinatePerm k).apply_symm_apply j] at hv
  · intro h j
    exact h (coordinatePerm k j)

theorem cube_eq_standardCube (k : ℕ) :
    cube k = {x : Space (3+k) | ∀ j, x j ∈ Icc (-1 : ℝ) 1} := by
  ext x
  exact mem_cube_iff k x

theorem image_cube (k : ℕ) :
    E k '' cube k = CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k :=
  (E k).surjective.image_preimage _

def haarFactor (k : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor
    ((volume : Measure (Ambient k)).map (E k).symm) volume

theorem map_symm_volume (k : ℕ) :
    (volume : Measure (Ambient k)).map (E k).symm = haarFactor k • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

/-- Coordinate transport multiplies every volume by the same positive
factor, so actual equal-volume partitions remain equal-volume. -/
theorem volume_image (k : ℕ) (A : Set (Space (3+k))) :
    volume.real (E k '' A) = (haarFactor k : ℝ) * volume.real A := by
  have h := setIntegral_map_equiv (μ := (volume : Measure (Ambient k)))
    (E k).symm.toHomeomorph.toMeasurableEquiv (fun _ => (1 : ℝ)) A
  change (∫ y in A, (1 : ℝ) ∂Measure.map (E k).symm volume) =
    ∫ x in (E k).symm ⁻¹' A, (1 : ℝ) ∂volume at h
  rw [map_symm_volume, Measure.restrict_smul, integral_smul_nnreal_measure] at h
  have hp : (E k).symm ⁻¹' A = E k '' A := by
    ext y
    constructor
    · intro hy
      exact ⟨(E k).symm y,hy,(E k).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
  simpa only [hp, setIntegral_one_eq_measureReal, smul_eq_mul] using h.symm

theorem volume_cube (k : ℕ) : volume.real (cube k) = (2 : ℝ) ^ (3+k) := by
  let B : Set (Fin (3+k) → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  have eq : cube k = WithLp.ofLp ⁻¹' B := by
    ext x
    rw [mem_cube_iff]
    change (∀ j, -1 ≤ x j ∧ x j ≤ 1) ↔
      ((∀ j, -1 ≤ x j) ∧ ∀ j, x j ≤ 1)
    exact forall_and
  calc
    volume.real (cube k) = volume.real B := by
      rw [eq]
      exact congrArg ENNReal.toReal
        ((PiLp.volume_preserving_ofLp (ι := Fin (3+k))).measure_preimage
          measurableSet_Icc.nullMeasurableSet)
    _ = (2 : ℝ) ^ (3+k) := by
      change (volume (Icc (fun _ : Fin (3+k) => (-1 : ℝ)) (fun _ => 1))).toReal = _
      rw [Real.volume_Icc_pi_toReal (by intro i; norm_num)]
      norm_num

theorem volume_activeCube : volume.real CubePlaneCoordinates.coordinateCube = 8 := by
  change volume.real ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1) = 8
  simp only [Measure.volume_eq_prod, measureReal_prod_prod]
  norm_num

/-- The concrete coordinate change has Haar factor exactly one, not just
an unspecified common factor. -/
theorem haarFactor_eq_one (k : ℕ) : haarFactor k = 1 := by
  have h := volume_image k (cube k)
  rw [image_cube, volume_cube] at h
  have target : volume.real (CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k) =
      (2 : ℝ) ^ (3+k) := by
    rw [Measure.volume_eq_prod, measureReal_prod_prod, volume_activeCube,
      show volume.real (passiveCube k) = (2 : ℝ)^k from passiveCube_volume k, pow_add]
    norm_num
  rw [target] at h
  apply NNReal.coe_injective
  change (haarFactor k : ℝ) = 1
  have pos : (0 : ℝ) < 2 ^ (3+k) := by positivity
  nlinarith

/-- Exact change of variables for every actual set and density, with no
hidden scaling of the normalized four moments. -/
theorem setIntegral_image_E (k : ℕ) (A : Set (Space (3+k)))
    (f : Ambient k → ℝ) :
    (∫ y in E k '' A, f y ∂volume) = ∫ x in A, f (E k x) ∂volume := by
  have h := setIntegral_map_equiv (μ := (volume : Measure (Ambient k)))
    (E k).symm.toHomeomorph.toMeasurableEquiv (fun x => f (E k x)) A
  change (∫ y in A, f (E k y) ∂Measure.map (E k).symm volume) =
    ∫ x in (E k).symm ⁻¹' A, f (E k ((E k).symm x)) ∂volume at h
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [map_symm_volume, haarFactor_eq_one, one_smul] at h
  have hp : (E k).symm ⁻¹' A = E k '' A := by
    ext y
    constructor
    · intro hy
      exact ⟨(E k).symm y,hy,(E k).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
  simpa only [hp] using h.symm

def actualDensity (k : ℕ) (a : Fin 4) (x : Space (3+k)) : ℝ :=
  ![x (Fin.castAdd k (0 : Fin 3)),x (Fin.castAdd k (1 : Fin 3)),
    (1+x (Fin.castAdd k (0 : Fin 3)))*x ⟨2+k,by omega⟩,
    x (Fin.castAdd k (1 : Fin 3))*x ⟨2+k,by omega⟩] a

def actualMoments (k : ℕ) (n : ℝ) (A : Set (Space (3+k))) : Fin 4 → ℝ :=
  fun a => n / 2 ^ (3+k) * ∫ x in A, actualDensity k a x ∂volume

theorem actualMoments_eq (k : ℕ) (n : ℝ) (A : Set (Space (3+k))) :
    volumeMoments k n (E k '' A) = actualMoments k n A := by
  funext a
  unfold volumeMoments actualMoments
  rw [setIntegral_image_E]
  simp only [E_apply,density,actualDensity,Nat.add_comm k 3]

def characteristics (k : ℕ) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) :
    Fin ((3+k)-1) → C(CompactConvex (3+k),ℝ) :=
  fun a => pullCharacteristic (E k)
    (CubeAllDimensions.characteristics k n P (Fin.cast (by omega) a))

/-- The first two characteristics are exactly the preselected polynomials
of the actual `n/2^d` normalized moments of `x₁,x₂,(1+x₁)x_d,x₂x_d`. -/
theorem polynomialFormula (k : ℕ) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (a : Fin 2)
    (C : CompactConvex (3+k)) :
    characteristics k n P
      (Fin.cast (by omega) (CubeAllDimensions.polynomialIndex k a)) C =
      RationalMomentApproximation.eval (P a)
        (actualMoments k n (ConvexLimits.points C)) := by
  simp only [characteristics, pullCharacteristic, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Fin.cast_cast, Fin.cast_eq_self,
    CubeAllDimensions.characteristics_polynomial]
  change RationalMomentApproximation.eval (P a)
    (volumeMoments k n (E k '' ConvexLimits.points C)) = _
  rw [actualMoments_eq]

/-- The remaining characteristics are the actual first moments of
`x₃,…,x_{d-1}` in their natural coordinate order. -/
theorem passiveFormula (k : ℕ) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) (j : Fin k)
    (C : CompactConvex (3+k)) :
    characteristics k n P
      (Fin.cast (by omega) (CubeAllDimensions.passiveIndex k j)) C =
      ∫ x in ConvexLimits.points C, x ⟨j.val+2,by omega⟩ ∂volume := by
  simp only [characteristics, pullCharacteristic, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Fin.cast_cast, Fin.cast_eq_self,
    CubeAllDimensions.characteristics_passive]
  change (∫ y in E k '' ConvexLimits.points C, y.2 j ∂volume) = _
  rw [setIntegral_image_E]
  simp only [E_apply]

/-- One pair of rational polynomials works for every Euclidean dimension
`3+k`, every genuine equal-volume convex partition of the cube, and the
full Hausdorff domain of the dimension-minus-one characteristics. -/
theorem exists_characteristics_for_euclidean_dimensions (n : ℕ)
    (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    ∃ P : Fin 2 → MvPolynomial (Fin 4) ℚ,
      ∀ (k : ℕ) (C : Fin n → CompactConvex (3+k)),
        (∀ i, (interior (ConvexLimits.points (C i))).Nonempty) →
        Pairwise (fun i j => Disjoint (interior (ConvexLimits.points (C i)))
          (interior (ConvexLimits.points (C j)))) →
        (⋃ i, ConvexLimits.points (C i)) = cube k →
        (∀ i j, volume.real (ConvexLimits.points (C i)) =
          volume.real (ConvexLimits.points (C j))) →
        ∃ a i j, characteristics k n P a (C i) ≠ characteristics k n P a (C j) := by
  classical
  obtain ⟨P,reject⟩ := CubeAllDimensions.exists_characteristics_for_all_dimensions n hn hpow
  refine ⟨P,?_⟩
  intro k C full disjoint cover equal
  let T : Fin n → ConvexLimits.ConvexCompact (Ambient k) :=
    fun i => convexCompactsHomeomorph (E k) (C i)
  have interior_image (A : Set (Space (3+k))) :
      interior (E k '' A) = E k '' interior A :=
    ((E k).toHomeomorph.image_interior A).symm
  have fullT (i : Fin n) : (interior (ConvexLimits.points (T i))).Nonempty := by
    change (interior (E k '' ConvexLimits.points (C i))).Nonempty
    rw [interior_image]
    exact (full i).image _
  have disjointT : Pairwise (fun i j =>
      Disjoint (interior (ConvexLimits.points (T i)))
        (interior (ConvexLimits.points (T j)))) := by
    intro i j hij
    change Disjoint (interior (E k '' ConvexLimits.points (C i)))
      (interior (E k '' ConvexLimits.points (C j)))
    rw [interior_image, interior_image]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    have hxy : y = x := (E k).injective heq
    subst y
    exact Set.disjoint_left.mp (disjoint hij) hx hy
  have coverT : (⋃ i, ConvexLimits.points (T i)) =
      CubePlaneCoordinates.coordinateCube ×ˢ passiveCube k := by
    change (⋃ i, E k '' ConvexLimits.points (C i)) = _
    rw [← image_iUnion, cover, image_cube]
  have equalT (i j : Fin n) : volume.real (ConvexLimits.points (T i)) =
      volume.real (ConvexLimits.points (T j)) := by
    change volume.real (E k '' ConvexLimits.points (C i)) =
      volume.real (E k '' ConvexLimits.points (C j))
    rw [volume_image, volume_image, equal i j]
  obtain ⟨a,i,j,h⟩ := reject k T fullT disjointT coverT equalT
  refine ⟨Fin.cast (by omega) a,i,j,?_⟩
  simpa [characteristics, pullCharacteristic, T] using h

def dimensionCharacteristics (d : ℕ) (hd : 3 ≤ d) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) :
    Fin (d-1) → C(CompactConvex d,ℝ) := by
  have h : 3+(d-3) = d := by omega
  exact Eq.recOn (motive := fun e _ => Fin (e-1) → C(CompactConvex e,ℝ))
    h (characteristics (d-3) n P)

theorem dimensionCharacteristics_add (k : ℕ) (hd : 3 ≤ 3+k) (n : ℝ)
    (P : Fin 2 → MvPolynomial (Fin 4) ℚ) :
    dimensionCharacteristics (3+k) hd n P = characteristics k n P := by
  apply eq_of_heq
  dsimp only [dimensionCharacteristics]
  refine (eqRec_heq (φ := fun e => Fin (e-1) → C(CompactConvex e,ℝ)) _ _).trans ?_
  have hk : 3+k-3 = k := by omega
  rw [hk]

/-- The requested order of quantification in standard Euclidean space:
the pair depends only on the number of cells, and works for every `d ≥ 3`
and every actual equal-volume convex partition of the standard cube.
The `d-1` characteristics are continuous on all nonempty compact convex sets. -/
theorem exists_same_polynomials_all_dimensions (n : ℕ)
    (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    ∃ P : Fin 2 → MvPolynomial (Fin 4) ℚ,
      ∀ (d : ℕ) (hd : 3 ≤ d) (C : Fin n → CompactConvex d),
        (∀ i, (interior (ConvexLimits.points (C i))).Nonempty) →
        Pairwise (fun i j => Disjoint (interior (ConvexLimits.points (C i)))
          (interior (ConvexLimits.points (C j)))) →
        (⋃ i, ConvexLimits.points (C i)) =
          {x : Space d | ∀ j, x j ∈ Icc (-1 : ℝ) 1} →
        (∀ i j, volume.real (ConvexLimits.points (C i)) =
          volume.real (ConvexLimits.points (C j))) →
        ∃ a i j, dimensionCharacteristics d hd n P a (C i) ≠
          dimensionCharacteristics d hd n P a (C j) := by
  obtain ⟨P,reject⟩ := exists_characteristics_for_euclidean_dimensions n hn hpow
  refine ⟨P,?_⟩
  intro d hd
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
  intro C full disjoint cover equal
  rw [← cube_eq_standardCube] at cover
  obtain ⟨a,i,j,h⟩ := reject k C full disjoint cover equal
  exact ⟨a,i,j,by simpa only [dimensionCharacteristics_add] using h⟩

end NRR.CubeEuclideanDimensions
