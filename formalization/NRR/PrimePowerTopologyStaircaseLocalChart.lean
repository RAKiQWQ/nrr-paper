import NRR.PrimePowerTopologyStaircaseLocalGeometry

/-! Open charts and the genuine local homology isomorphism of the selected
configuration staircase singular simplex. -/

noncomputable section
open Set Topology CategoryTheory Limits
open scoped OnePoint
open NRR.PrimePower NRR.SingularHomology
open NRR.SingularHomology.SimplexGeometry

namespace NRR.PrimePowerTopology

/-- The inverse of the finite part of the compact cube collapse. -/
def configurationFiniteCubeChart (d n : ℕ) : C(Configuration d n,ConfigurationCube d n) :=
  ⟨fun z => ((configurationCubeInteriorEuclidean d n).symm z.val).val,
    continuous_subtype_val.comp
      ((configurationCubeInteriorEuclidean d n).symm.continuous.comp continuous_subtype_val)⟩

theorem configurationFiniteCubeChart_open (d n : ℕ) :
    IsOpenEmbedding (configurationFiniteCubeChart d n) :=
  (isOpen_configurationCubeInterior d n).isOpenEmbedding_subtypeVal.comp
    ((configurationCubeInteriorEuclidean d n).symm.isOpenEmbedding.comp
      (isOpen_injectiveSites d n).isOpenEmbedding_subtypeVal)

@[simp] theorem configurationCubeCollapse_finiteChart {d n : ℕ}
    (z : Configuration d n) :
    configurationCubeCollapse d n (configurationFiniteCubeChart d n z) =
      (z : OnePoint (Configuration d n)) := by
  let x := (configurationCubeInteriorEuclidean d n).symm z.val
  have hinj : Function.Injective (configurationCubeInteriorEuclidean d n x) := by
    simpa [x] using z.property
  change configurationCubeCollapse d n x.val = _
  rw [configurationCubeCollapse_interior_configuration x hinj]
  apply congrArg OnePoint.some
  apply Subtype.ext
  exact (configurationCubeInteriorEuclidean d n).apply_symm_apply z.val

@[simp] theorem configurationFiniteCubeChart_selected {d n : ℕ} (hd : 0 < d) :
    configurationFiniteCubeChart d n (staircaseSelectedConfiguration (n := n) hd) =
      staircaseSelectedCubePoint (n*d) := by
  simp [configurationFiniteCubeChart, staircaseSelectedConfiguration]

def staircaseStrictChamber (m : ℕ) : Set (Fin m → Set.Icc (0 : ℝ) 1) :=
  {y | StrictAnti (fun a => (y a).val)}

theorem isOpen_staircaseStrictChamber (m : ℕ) : IsOpen (staircaseStrictChamber m) := by
  have he : staircaseStrictChamber m =
      ⋂ a : Fin m, ⋂ b : Fin m,
        {y : Fin m → Set.Icc (0 : ℝ) 1 | a < b → (y b).val < (y a).val} := by
    ext y
    simp only [staircaseStrictChamber, mem_setOf_eq, mem_iInter]
    rfl
  rw [he]
  apply isOpen_iInter_of_finite
  intro a
  apply isOpen_iInter_of_finite
  intro b
  by_cases hab : a < b
  · simp only [hab, true_implies]
    exact isOpen_lt (by fun_prop) (by fun_prop)
  · simp only [hab, false_implies, setOf_true]
    exact isOpen_univ

/-- Configurations whose finite cube inverse lies in the strict identity chamber. -/
def staircaseLocalChartDomain (d n : ℕ) : Set (Configuration d n) :=
  (configurationFiniteCubeChart d n) ⁻¹' staircaseStrictChamber (n*d)

theorem isOpen_staircaseLocalChartDomain (d n : ℕ) :
    IsOpen (staircaseLocalChartDomain d n) :=
  (isOpen_staircaseStrictChamber (n*d)).preimage (configurationFiniteCubeChart d n).continuous

def staircaseLocalChartCube (d n : ℕ) :
    C(staircaseLocalChartDomain d n,staircaseClosedChamber (n*d)) :=
  ⟨fun z => ⟨configurationFiniteCubeChart d n z.val,z.property.antitone⟩,
    ((configurationFiniteCubeChart d n).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem staircaseLocalChartCube_open (d n : ℕ) :
    IsOpenEmbedding (staircaseLocalChartCube d n) := by
  have h := (configurationFiniteCubeChart_open d n).comp
    (isOpen_staircaseLocalChartDomain d n).isOpenEmbedding_subtypeVal
  have he := h.isEmbedding.codRestrict (staircaseClosedChamber (n*d))
    (fun z => z.property.antitone)
  have ho := h.isOpenMap.codRestrict (s := staircaseClosedChamber (n*d))
    (fun z => z.property.antitone)
  exact .of_isEmbedding_isOpenMap he ho

/-- The simplex-side open chart, expressed by actual inverse barycentric coordinates. -/
def staircaseLocalChartSource (d n : ℕ) :
    C(staircaseLocalChartDomain d n,Simplex (n*d)) :=
  (⟨(staircaseChamberHomeomorph (n*d)).symm,
    (staircaseChamberHomeomorph (n*d)).symm.continuous⟩ :
    C(staircaseClosedChamber (n*d),Simplex (n*d))).comp (staircaseLocalChartCube d n)

theorem staircaseLocalChartSource_open (d n : ℕ) :
    IsOpenEmbedding (staircaseLocalChartSource d n) :=
  (staircaseChamberHomeomorph (n*d)).symm.isOpenEmbedding.comp
    (staircaseLocalChartCube_open d n)

def staircaseLocalChartTarget (d n : ℕ) :
    C(staircaseLocalChartDomain d n,OnePoint (Configuration d n)) :=
  ⟨fun z => (z.val : OnePoint (Configuration d n)),
    OnePoint.continuous_coe.comp continuous_subtype_val⟩

theorem staircaseLocalChartTarget_open (d n : ℕ) :
    IsOpenEmbedding (staircaseLocalChartTarget d n) :=
  OnePoint.isOpenEmbedding_coe.comp
    (isOpen_staircaseLocalChartDomain d n).isOpenEmbedding_subtypeVal

theorem configurationStaircaseSimplex_localChart {d n : ℕ}
    (z : staircaseLocalChartDomain d n) :
    configurationStaircaseSimplex (Equiv.refl _) (staircaseLocalChartSource d n z) =
      staircaseLocalChartTarget d n z := by
  change configurationCubeCollapse d n
    (staircaseUnitCubeSimplex (Equiv.refl _)
      (staircaseCubeInverse (staircaseLocalChartCube d n z))) = _
  rw [staircaseUnitCubeSimplex_inverse]
  exact configurationCubeCollapse_finiteChart z.val

def staircaseLocalChartSelected {d n : ℕ} (hd : 0 < d) : staircaseLocalChartDomain d n :=
  ⟨staircaseSelectedConfiguration hd, by
    change StrictAnti (fun a =>
      (configurationFiniteCubeChart d n (staircaseSelectedConfiguration hd) a).val)
    rw [configurationFiniteCubeChart_selected]
    exact staircaseSelectedCubePoint_strictAnti (n*d)⟩

@[simp] theorem staircaseLocalChartSource_selected {d n : ℕ} (hd : 0 < d) :
    staircaseLocalChartSource d n (staircaseLocalChartSelected hd) =
      staircaseBarycenter (n*d) := by
  apply (staircaseChamberHomeomorph (n*d)).injective
  apply Subtype.ext
  change staircaseUnitCubeSimplex (Equiv.refl _)
    (staircaseCubeInverse (staircaseLocalChartCube d n (staircaseLocalChartSelected hd))) = _
  rw [staircaseUnitCubeSimplex_inverse]
  exact configurationFiniteCubeChart_selected hd

@[simp] theorem staircaseLocalChartTarget_selected {d n : ℕ} (hd : 0 < d) :
    staircaseLocalChartTarget d n (staircaseLocalChartSelected hd) =
      (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n)) := rfl

theorem staircaseUnitCubeSimplex_id_injective (m : ℕ) :
    Function.Injective (staircaseUnitCubeSimplex (Equiv.refl (Fin m))) := by
  intro x y h
  exact (staircaseChamberHomeomorph m).injective (Subtype.ext h)

theorem configurationStaircaseSimplex_selected_fiber {d n : ℕ} (hd : 0 < d)
    (x : Simplex (n*d))
    (hx : configurationStaircaseSimplex (Equiv.refl _) x =
      (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n))) :
    x = staircaseBarycenter (n*d) :=
  staircaseUnitCubeSimplex_id_injective (n*d)
    (configurationCubeCollapse_selected_fiber hd _ hx)

def staircaseSelectedSimplexPuncturedMap {d n : ℕ} (hd : 0 < d) :
    TopCat.of ({staircaseBarycenter (n*d)}ᶜ : Set (Simplex (n*d))) ⟶
      TopCat.of ({(staircaseSelectedConfiguration (n := n) hd :
        OnePoint (Configuration d n))}ᶜ : Set (OnePoint (Configuration d n))) :=
  mvRestrictMap _ _ (TopCat.ofHom (configurationStaircaseSimplex (Equiv.refl _)))
    (fun x hx he => hx (configurationStaircaseSimplex_selected_fiber hd x he))

theorem staircaseSelectedSimplexPunctured_square {d n : ℕ} (hd : 0 < d) :
    subIncl (Y := TopCat.of (Simplex (n*d))) {staircaseBarycenter (n*d)}ᶜ ≫
        TopCat.ofHom (configurationStaircaseSimplex (Equiv.refl (Fin (n*d)))) =
      staircaseSelectedSimplexPuncturedMap hd ≫
        subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
          {(staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n))}ᶜ := rfl

private theorem isIso_localHomologyMap_of_open_chart_at
    (R : Type) [Ring R] {X Y T : Type}
    [TopologicalSpace X] [T1Space X] [TopologicalSpace Y] [T1Space Y]
    [TopologicalSpace T] (f : C(X,Y)) (u : C(T,X)) (v : C(T,Y))
    (hu : IsOpenEmbedding u) (hv : IsOpenEmbedding v)
    (hcomm : ∀ t, f (u t) = v t) (t : T) (a : X) (b : Y)
    (ha : u t = a) (hb : v t = b) (hfiber : ∀ x, f x = b → x = a) (q : ℕ) :
    IsIso (HrelMap R q (subIncl (Y := TopCat.of X) {a}ᶜ)
      (subIncl (Y := TopCat.of Y) {b}ᶜ)
      (mvRestrictMap_subIncl (X := TopCat.of X) (Y := TopCat.of Y)
        {a}ᶜ {b}ᶜ (TopCat.ofHom f)
        (fun x hx he => hx (hfiber x he))).symm) := by
  subst a
  subst b
  exact isIso_localHomologyMap_of_open_chart R f u v hu hv hcomm t hfiber q

/-- The selected actual singular simplex induces an isomorphism on genuine
point-relative singular homology, in every degree. -/
theorem isIso_configurationStaircaseSimplex_selected_local (R : Type) [Ring R]
    {d n : ℕ} (hd : 0 < d) (q : ℕ) :
    IsIso (HrelMap R q
      (subIncl (Y := TopCat.of (Simplex (n*d))) {staircaseBarycenter (n*d)}ᶜ)
      (subIncl (Y := TopCat.of (OnePoint (Configuration d n)))
        {(staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n))}ᶜ)
      (staircaseSelectedSimplexPunctured_square hd)) := by
  exact isIso_localHomologyMap_of_open_chart_at R
    (configurationStaircaseSimplex (Equiv.refl (Fin (n*d))))
    (staircaseLocalChartSource d n) (staircaseLocalChartTarget d n)
    (staircaseLocalChartSource_open d n) (staircaseLocalChartTarget_open d n)
    configurationStaircaseSimplex_localChart (staircaseLocalChartSelected hd)
    (staircaseBarycenter (n*d))
    (staircaseSelectedConfiguration (n := n) hd : OnePoint (Configuration d n))
    (staircaseLocalChartSource_selected hd) rfl
    (configurationStaircaseSimplex_selected_fiber hd) q

end NRR.PrimePowerTopology
