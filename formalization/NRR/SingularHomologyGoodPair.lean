import NRR.SingularHomologyMayerVietorisCover

/-! Excision and neighborhood comparison for the actual singular relative
complexes. These lemmas isolate the precise good-pair input needed for
compact open-stratum collapse maps. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology

namespace NRR.SingularHomology
variable (R : Type) [Ring R]

theorem isIso_HrelMap_of_homologyEquivalences {A X B Y : TopCat.{0}}
    (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    (hA : ∀ n, IsIso (HabsMap R n fA)) (hX : ∀ n, IsIso (HabsMap R n f)) (n : ℕ) :
    IsIso (HrelMap R n i j w) := by
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (relShortComplexMap R i j w) (relShortComplex_shortExact R i)
      (relShortComplex_shortExact R j)
  · change Epi (HabsMap R n fA)
    letI := hA n
    infer_instance
  · exact hX n
  · intro k _
    exact hA k
  · intro k _
    change Mono (HabsMap R k f)
    letI := hX k
    infer_instance

section ExcisionComparison
variable {X Y : TopCat.{0}} (U N : Set X) (V M : Set Y)
variable (f : X ⟶ Y) (hU : Set.MapsTo f U V) (hN : Set.MapsTo f N M)

@[reassoc]
theorem mvExcisionHrelMap_naturality (n : ℕ) :
    mvExcisionHrelMap R U N n ≫
        HrelMap R n (subIncl N) (subIncl M)
          (mvRestrictMap_subIncl N M f hN).symm =
      HrelMap R n (mvInclLeft U N) (mvInclLeft V M)
          (mvIntersectionMap_left U N V M f hU hN).symm ≫
        mvExcisionHrelMap R V M n := by
  unfold mvExcisionHrelMap HrelMap
  rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp]
  congr 1
  letI : Epi (relProj R (mvInclLeft U N)) := by unfold relProj; infer_instance
  apply (cancel_epi (relProj R (mvInclLeft U N))).mp
  simp only [relProj_comp_relComplexMap_assoc,relProj_comp_relComplexMap]
  simp only [← Category.assoc,← CsingMap_comp,mvRestrictMap_subIncl]

/-- An excisive comparison which is a homeomorphism on the open part and
on its overlap induces an isomorphism of the actual relative homologies. -/
theorem isIso_HrelMap_of_excisionComparison
    (coverX : interior U ∪ interior N = Set.univ)
    (coverY : interior V ∪ interior M = Set.univ)
    [IsIso (mvRestrictMap U V f hU)]
    [IsIso (mvIntersectionMap U N V M f hU hN)] (n : ℕ) :
    IsIso (HrelMap R n (subIncl N) (subIncl M)
      (mvRestrictMap_subIncl N M f hN).symm) := by
  let eX := mvExcisionHrelMap R U N n
  let eY := mvExcisionHrelMap R V M n
  let g := HrelMap R n (subIncl N) (subIncl M)
    (mvRestrictMap_subIncl N M f hN).symm
  let l := HrelMap R n (mvInclLeft U N) (mvInclLeft V M)
    (mvIntersectionMap_left U N V M f hU hN).symm
  letI : IsIso eX := isIso_mvExcisionHrelMap R U N coverX n
  letI : IsIso eY := isIso_mvExcisionHrelMap R V M coverY n
  letI : IsIso l := isIso_HrelMap_of_isIso R n (mvInclLeft U N) (mvInclLeft V M) _
  have he : eX ≫ g = l ≫ eY := mvExcisionHrelMap_naturality R U N V M f hU hN n
  letI : IsIso (eX ≫ g) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left eX g

end ExcisionComparison

/-- Enlarging the two subspaces along actual homology equivalences does
not affect whether the given canonical relative map is an isomorphism.
The lower square need not be supplied separately: the relative maps are
determined by their common ambient map after the cokernel projection. -/
theorem isIso_HrelMap_of_goodNeighborhoods {A X B Y N M : TopCat.{0}}
    (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    (iN : N ⟶ X) [Mono iN] (jM : M ⟶ Y) [Mono jM]
    (a : A ⟶ N) (b : B ⟶ M) (wa : i = a ≫ iN) (wb : j = b ≫ jM)
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    {fN : N ⟶ M} (wN : iN ≫ f = fN ≫ jM)
    (ha : ∀ n, IsIso (HabsMap R n a)) (hb : ∀ n, IsIso (HabsMap R n b))
    (hN : ∀ n, IsIso (HrelMap R n iN jM wN)) (n : ℕ) :
    IsIso (HrelMap R n i j w) := by
  let ea := HrelMap R n i iN (show i ≫ 𝟙 X = a ≫ iN by simpa using wa)
  let eb := HrelMap R n j jM (show j ≫ 𝟙 Y = b ≫ jM by simpa using wb)
  let g := HrelMap R n i j w
  let gN := HrelMap R n iN jM wN
  letI : IsIso ea := isIso_HrelMap_of_homologyEquivalences R i iN _ ha (by
    intro k
    rw [HabsMap_id]
    infer_instance) n
  letI : IsIso eb := isIso_HrelMap_of_homologyEquivalences R j jM _ hb (by
    intro k
    rw [HabsMap_id]
    infer_instance) n
  letI : IsIso gN := hN n
  have he : ea ≫ gN = g ≫ eb := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp]
    congr 1
    letI : Epi (relProj R i) := by unfold relProj; infer_instance
    apply (cancel_epi (relProj R i)).mp
    simp only [relProj_comp_relComplexMap_assoc,relProj_comp_relComplexMap,
      CsingMap_id,Category.id_comp,Category.comp_id]
  letI : IsIso (g ≫ eb) := by rw [← he]; infer_instance
  exact IsIso.of_isIso_comp_right g eb

end NRR.SingularHomology
