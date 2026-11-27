/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from Submission/Model/Sphere.lean and
Submission/Homotopy/ContractionData.lean in akopjan/toptverbert-nandakumar,
revision d98f6f87bb60b9e5b3a57370f393ade1397189bc.
The suspension comparison is omitted; all retained constructions use the
actual metric spheres in the local mathlib 4.24.0 toolchain.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Path
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 800000
namespace NRR.SphereGeometry
open Metric Set Topology

section SnocLp

variable {m : ℕ}

/-- Append a real number as the last coordinate of a Euclidean vector; this is the identification
`ℝ^m × ℝ ≅ ℝ^{m+1}`. -/
noncomputable def snocLp (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp v) a)

@[simp]
theorem snocLp_castSucc (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) (i : Fin m) :
    snocLp v a i.castSucc = v i := by
  simp [snocLp]

@[simp]
theorem snocLp_last (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    snocLp v a (Fin.last m) = a := by
  simp [snocLp]

theorem snocLp_injective :
    Function.Injective (fun p : EuclideanSpace ℝ (Fin m) × ℝ => snocLp p.1 p.2) := by
  rintro ⟨v, a⟩ ⟨w, b⟩ h
  simp only at h
  refine Prod.ext (PiLp.ext fun i => ?_) ?_
  · simpa using congrArg (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y i.castSucc) h
  · simpa using congrArg (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y (Fin.last m)) h

theorem snocLp_eq_iff {v w : EuclideanSpace ℝ (Fin m)} {a b : ℝ} :
    snocLp v a = snocLp w b ↔ v = w ∧ a = b := by
  constructor
  · intro h
    have h' := snocLp_injective (a₁ := (v, a)) (a₂ := (w, b)) h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem continuous_snocLp :
    Continuous fun p : EuclideanSpace ℝ (Fin m) × ℝ => snocLp p.1 p.2 := by
  have hg : Continuous fun p : EuclideanSpace ℝ (Fin m) × ℝ =>
      (Fin.snoc (WithLp.ofLp p.1) p.2 : Fin (m + 1) → ℝ) := by
    refine continuous_pi fun i => ?_
    induction i using Fin.lastCases with
    | last => simpa using continuous_snd
    | cast j =>
      simpa using (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).comp' continuous_fst
  exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)) hg

/-- Every Euclidean vector is the extension of its first coordinates by its last coordinate. -/
theorem eq_snocLp (z : EuclideanSpace ℝ (Fin (m + 1))) :
    z = snocLp (WithLp.toLp 2 fun i : Fin m => z i.castSucc) (z (Fin.last m)) := by
  refine PiLp.ext fun i => ?_
  induction i using Fin.lastCases with
  | last => rw [snocLp_last]
  | cast j => rw [snocLp_castSucc]; rfl

/-- Two nonnegative reals with equal squares are equal. -/
theorem eq_of_sq_eq_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

theorem norm_snocLp_sq (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    ‖snocLp v a‖ ^ 2 = ‖v‖ ^ 2 + a ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp

/-- If the square of a norm is `1`, the norm is `1`. -/
theorem norm_eq_one_of_norm_sq_eq_one {E : Type*} [NormedAddCommGroup E] {y : E}
    (h : ‖y‖ ^ 2 = 1) : ‖y‖ = 1 := by
  have h1 : (‖y‖ - 1) * (‖y‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · linarith [norm_nonneg y]

end SnocLp

/-- The `n`-sphere, in the model used by the benchmark statement: the unit sphere of
`EuclideanSpace ℝ (Fin (n + 1))`. -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Challenge-independent spelling of the exact metric-sphere model. -/
abbrev SphereSpace (n : ℕ) := Sph n

/-- The first coordinate vector, used as the distinguished point of the metric sphere. -/
noncomputable def sphereBasepoint (n : ℕ) : SphereSpace n :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_single, norm_one]⟩

instance instNonemptySph (n : ℕ) : Nonempty (Sph n) :=
  ⟨⟨EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), by simp⟩⟩

instance instCompactSpaceSph (n : ℕ) : CompactSpace (Sph n) :=
  inferInstanceAs (CompactSpace (Metric.sphere _ _))


open unitInterval

universe u v

/-- A continuous contraction of a based space `(T, t₀)`: a continuous family of paths from `t₀` to
every point of `T`, which at `t₀` is the constant path.

For a subspace `D ⊆ X` with base point `b₀ : D` this is `ContractionData ↥D b₀`, i.e. a continuous
family of paths *inside `D`* from `b₀` to each point of `D`. -/
structure ContractionData (T : Type u) [TopologicalSpace T] (t₀ : T) where
  /-- The path from the base point `t₀` to the point `t`. -/
  path : ∀ t : T, Path t₀ t
  /-- The family of paths is jointly continuous. -/
  continuous_uncurry : Continuous fun p : T × I => path p.1 p.2
  /-- At the base point the path is constant. -/
  path_base : path t₀ = Path.refl t₀

namespace ContractionData

variable {T : Type u} [TopologicalSpace T] {t₀ : T}

/-- The contraction bundled as a single continuous map `T × I → T`. -/
def curve (c : ContractionData T t₀) : C(T × I, T) :=
  ⟨fun p => c.path p.1 p.2, c.continuous_uncurry⟩

@[simp] theorem curve_apply (c : ContractionData T t₀) (t : T) (s : I) :
    c.curve (t, s) = c.path t s := rfl

@[simp] theorem curve_zero (c : ContractionData T t₀) (t : T) : c.curve (t, 0) = t₀ :=
  (c.path t).source

@[simp] theorem curve_one (c : ContractionData T t₀) (t : T) : c.curve (t, 1) = t :=
  (c.path t).target

@[simp] theorem curve_base (c : ContractionData T t₀) (s : I) : c.curve (t₀, s) = t₀ := by
  rw [curve_apply, c.path_base]; rfl

/-- A space carrying contraction data is contractible. -/
theorem contractibleSpace (c : ContractionData T t₀) : ContractibleSpace T := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨t₀, ⟨⟨⟨fun p => c.curve (p.2, σ p.1), c.curve.continuous.comp
    (continuous_snd.prodMk (continuous_symm.comp continuous_fst))⟩, fun t => ?_, fun t => ?_⟩⟩⟩
  · simp
  · simp

end ContractionData

/-! ### Products with a contractible factor -/

/-- If `Y` is contractible then `X × Y` is homotopy equivalent to `X`. -/
noncomputable def prodHomotopyEquivOfContractible (X : Type u) (Y : Type v) [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace Y] : ContinuousMap.HomotopyEquiv (X × Y) X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
      (ContractibleSpace.hequiv_unit Y).some).trans (Homeomorph.prodUnique X Unit).toHomotopyEquiv

/-! ### Coordinates on a sphere -/

section Sphere

open Metric

variable {m : ℕ}

/-- The last coordinate ("height") of a point of `S^{m+1}`. -/
def sphHeight (z : Sph (m + 1)) : ℝ := (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))

theorem continuous_sphHeight : Continuous (sphHeight (m := m)) :=
  (PiLp.continuous_apply 2 (fun _ : Fin (m + 2) => ℝ) (Fin.last (m + 1))).comp
    continuous_subtype_val

/-- The equatorial component of a point of `S^{m+1}`: its first `m + 1` coordinates. -/
def sphEquator (z : Sph (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 fun i => (z : EuclideanSpace ℝ (Fin (m + 2))) i.castSucc

theorem continuous_sphEquator : Continuous (sphEquator (m := m)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp (continuous_pi fun i => ?_)
  exact (PiLp.continuous_apply 2 (fun _ : Fin (m + 2) => ℝ) i.castSucc).comp continuous_subtype_val

theorem snocLp_sphEquator_sphHeight (z : Sph (m + 1)) :
    snocLp (sphEquator z) (sphHeight z) = (z : EuclideanSpace ℝ (Fin (m + 2))) :=
  (eq_snocLp _).symm

theorem norm_sphEquator_sq (z : Sph (m + 1)) : ‖sphEquator z‖ ^ 2 = 1 - sphHeight z ^ 2 := by
  have hz : ‖(z : EuclideanSpace ℝ (Fin (m + 2)))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have h := norm_snocLp_sq (sphEquator z) (sphHeight z)
  rw [snocLp_sphEquator_sphHeight, hz, one_pow] at h
  linarith

theorem sphHeight_sq_le_one (z : Sph (m + 1)) : sphHeight z ^ 2 ≤ 1 := by
  nlinarith [norm_sphEquator_sq z, sq_nonneg ‖sphEquator z‖]

/-! ### Spherical caps -/

/-- The closed spherical cap `{z ∈ S^{m+1} | -h ≤ ε * z_last}`. For `ε = 1` this is the region of
height at least `-h`, for `ε = -1` the region of height at most `h`. -/
def sphCap (m : ℕ) (ε h : ℝ) : Set (Sph (m + 1)) := {z | -h ≤ ε * sphHeight z}

theorem mem_sphCap {ε h : ℝ} {z : Sph (m + 1)} : z ∈ sphCap m ε h ↔ -h ≤ ε * sphHeight z := Iff.rfl

theorem zero_lt_one_add_of_mem_sphCap {ε h : ℝ} (hh1 : h < 1) {z : Sph (m + 1)}
    (hz : z ∈ sphCap m ε h) : 0 < 1 + ε * sphHeight z := by
  rw [mem_sphCap] at hz; linarith

/-- The pole `(0, …, 0, ε)` of `S^{m+1}`, for `ε = ±1`. -/
noncomputable def sphPole (m : ℕ) (ε : ℝ) (hε : ε ^ 2 = 1) : Sph (m + 1) :=
  ⟨snocLp 0 ε, mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_norm_sq_eq_one (by
    rw [norm_snocLp_sq, norm_zero, hε]; norm_num))⟩

@[simp] theorem sphHeight_sphPole (ε : ℝ) (hε : ε ^ 2 = 1) :
    sphHeight (sphPole m ε hε) = ε := snocLp_last 0 ε

@[simp] theorem sphEquator_sphPole (ε : ℝ) (hε : ε ^ 2 = 1) :
    sphEquator (sphPole m ε hε) = 0 :=
  PiLp.ext fun i => by simp [sphEquator, sphPole]

/-! ### The meridian contraction of a cap -/

/-- The point at parameter `s` on the meridian from the pole `(0, ε)` to `z`. -/
noncomputable def capPathFun (ε : ℝ) (z : Sph (m + 1)) (s : ℝ) :
    EuclideanSpace ℝ (Fin (m + 2)) :=
  snocLp (Real.sqrt (s * (2 - s * (1 - ε * sphHeight z)) / (1 + ε * sphHeight z)) • sphEquator z)
    (ε * (1 - s * (1 - ε * sphHeight z)))

@[simp] theorem capPathFun_zero (ε : ℝ) (z : Sph (m + 1)) : capPathFun ε z 0 = snocLp 0 ε := by
  simp [capPathFun]

theorem capPathFun_last (ε : ℝ) (z : Sph (m + 1)) (s : ℝ) :
    capPathFun ε z s (Fin.last (m + 1)) = ε * (1 - s * (1 - ε * sphHeight z)) :=
  snocLp_last _ _

/-- On the sphere the quantity `1 - ε * z_last` is nonnegative when `ε = ±1`. -/
theorem one_sub_mul_sphHeight_nonneg {ε : ℝ} (hε : ε ^ 2 = 1) (z : Sph (m + 1)) :
    0 ≤ 1 - ε * sphHeight z := by
  nlinarith [sphHeight_sq_le_one z, sq_nonneg (ε - sphHeight z), sq_nonneg (ε + sphHeight z)]

theorem capPathFun_one {ε : ℝ} (hε : ε ^ 2 = 1) (z : Sph (m + 1))
    (hz : 0 < 1 + ε * sphHeight z) : capPathFun ε z 1 = (z : EuclideanSpace ℝ (Fin (m + 2))) := by
  have h1 : (1 : ℝ) * (2 - 1 * (1 - ε * sphHeight z)) / (1 + ε * sphHeight z) = 1 := by
    rw [show (1 : ℝ) * (2 - 1 * (1 - ε * sphHeight z)) = 1 + ε * sphHeight z by ring]
    exact div_self (ne_of_gt hz)
  have h2 : ε * (1 - 1 * (1 - ε * sphHeight z)) = sphHeight z := by
    linear_combination sphHeight z * hε
  rw [capPathFun, h1, h2, Real.sqrt_one, one_smul, snocLp_sphEquator_sphHeight]

theorem norm_capPathFun {ε : ℝ} (hε : ε ^ 2 = 1) (z : Sph (m + 1))
    (hz : 0 < 1 + ε * sphHeight z) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖capPathFun ε z s‖ = 1 := by
  set a := sphHeight z with ha
  set r := 1 - ε * a with hr
  have hr0 : 0 ≤ r := one_sub_mul_sphHeight_nonneg hε z
  have hsr : s * r ≤ r := by nlinarith
  have harg : 0 ≤ s * (2 - s * r) / (1 + ε * a) := by
    apply div_nonneg _ hz.le
    have h2 : 2 - s * r ≥ 1 + ε * a := by simp only [hr] at hsr ⊢; linarith
    nlinarith
  refine norm_eq_one_of_norm_sq_eq_one ?_
  rw [capPathFun, ← ha, ← hr, norm_snocLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt harg, norm_sphEquator_sq, ← ha]
  have hfac : (1 : ℝ) - a ^ 2 = r * (1 + ε * a) := by
    rw [hr]; linear_combination a ^ 2 * hε
  rw [hfac]
  field_simp
  nlinarith [hε]

theorem capPathFun_mem_sphCap {ε h : ℝ} (hε : ε ^ 2 = 1) {z : Sph (m + 1)}
    (hzc : z ∈ sphCap m ε h) {s : ℝ} (hs1 : s ≤ 1) :
    -h ≤ ε * (capPathFun ε z s (Fin.last (m + 1))) := by
  have hr0 : 0 ≤ 1 - ε * sphHeight z := one_sub_mul_sphHeight_nonneg hε z
  have hsr : s * (1 - ε * sphHeight z) ≤ 1 - ε * sphHeight z := by nlinarith [hr0, hs1]
  have hzc' : -h ≤ ε * sphHeight z := hzc
  have key : ε * (ε * (1 - s * (1 - ε * sphHeight z))) = 1 - s * (1 - ε * sphHeight z) := by
    linear_combination (1 - s * (1 - ε * sphHeight z)) * hε
  rw [capPathFun_last, key]
  linarith

theorem continuous_capPathFun {ε : ℝ} {D : Set (Sph (m + 1))}
    (hD : ∀ z : ↥D, 0 < 1 + ε * sphHeight z.1) :
    Continuous fun p : ↥D × I => capPathFun ε p.1.1 (p.2 : ℝ) := by
  have hgt : Continuous fun p : ↥D × I => sphHeight p.1.1 :=
    continuous_sphHeight.comp (continuous_subtype_val.comp continuous_fst)
  have hs : Continuous fun p : ↥D × I => (p.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  have hy : Continuous fun p : ↥D × I => sphEquator p.1.1 :=
    continuous_sphEquator.comp (continuous_subtype_val.comp continuous_fst)
  have hr : Continuous fun p : ↥D × I => 1 - ε * sphHeight p.1.1 :=
    continuous_const.sub (continuous_const.mul hgt)
  have hnum : Continuous fun p : ↥D × I =>
      (p.2 : ℝ) * (2 - (p.2 : ℝ) * (1 - ε * sphHeight p.1.1)) :=
    hs.mul (continuous_const.sub (hs.mul hr))
  have hden : Continuous fun p : ↥D × I => 1 + ε * sphHeight p.1.1 :=
    continuous_const.add (continuous_const.mul hgt)
  have hsqrt : Continuous fun p : ↥D × I => Real.sqrt
      ((p.2 : ℝ) * (2 - (p.2 : ℝ) * (1 - ε * sphHeight p.1.1)) / (1 + ε * sphHeight p.1.1)) :=
    Real.continuous_sqrt.comp (hnum.div hden fun p => ne_of_gt (hD p.1))
  exact continuous_snocLp.comp ((hsqrt.smul hy).prodMk
    (continuous_const.mul (continuous_const.sub (hs.mul hr))))

variable (m) in
/-- The pole of the cap `sphCap m ε h`, as a point of that cap. -/
noncomputable def capPole (ε h : ℝ) (hε : ε ^ 2 = 1) (hh : -1 ≤ h) : ↥(sphCap m ε h) :=
  ⟨sphPole m ε hε, by rw [mem_sphCap, sphHeight_sphPole, ← pow_two, hε]; linarith⟩

/-- All meridian paths, bundled as a single continuous map on the cap times the interval. -/
private def capMeridian (ε h : ℝ) (hε : ε ^ 2 = 1) (hh1 : h < 1) :
    C(↥(sphCap m ε h) × I, ↥(sphCap m ε h)) where
  toFun p :=
    ⟨⟨capPathFun ε p.1.1 p.2, mem_sphere_zero_iff_norm.mpr (norm_capPathFun hε p.1.1
        (zero_lt_one_add_of_mem_sphCap hh1 p.1.2) p.2.2.1 p.2.2.2)⟩,
      capPathFun_mem_sphCap hε p.1.2 p.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_capPathFun (D := sphCap m ε h) (ε := ε)
      (fun w => zero_lt_one_add_of_mem_sphCap hh1 w.2)

/-- The meridian path inside the cap `sphCap m ε h` from the pole to the point `z`. -/
noncomputable def capPath (ε h : ℝ) (hε : ε ^ 2 = 1) (hh : -1 ≤ h) (hh1 : h < 1)
    (z : ↥(sphCap m ε h)) : Path (capPole m ε h hε hh) z where
  toContinuousMap := (capMeridian ε h hε hh1).comp
    ((ContinuousMap.const I z).prodMk (ContinuousMap.id I))
  source' := Subtype.ext (Subtype.ext (capPathFun_zero ε z.1))
  target' := Subtype.ext (Subtype.ext
    (capPathFun_one hε z.1 (zero_lt_one_add_of_mem_sphCap hh1 z.2)))

/-- **The meridian contraction of a spherical cap onto its pole.** -/
noncomputable def capContraction (ε h : ℝ) (hε : ε ^ 2 = 1) (hh : -1 ≤ h) (hh1 : h < 1) :
    ContractionData ↥(sphCap m ε h) (capPole m ε h hε hh) where
  path z := capPath ε h hε hh hh1 z
  continuous_uncurry := (capMeridian ε h hε hh1).continuous
  path_base := by
    refine Path.ext (funext fun s => Subtype.ext (Subtype.ext ?_))
    show capPathFun ε (sphPole m ε hε) (s : ℝ) = snocLp 0 ε
    rw [capPathFun, sphEquator_sphPole, smul_zero, sphHeight_sphPole, ← pow_two, hε]
    norm_num

/-! ### The two enlarged hemispheres -/

variable (m) in
/-- The enlarged lower hemisphere `{z ∈ S^{m+1} | z_last ≤ 1/3}`. -/
noncomputable def sphLowerCap : Set (Sph (m + 1)) := sphCap m (-1) (1 / 3)

variable (m) in
/-- The enlarged upper hemisphere `{z ∈ S^{m+1} | -1/3 ≤ z_last}`. -/
noncomputable def sphUpperCap : Set (Sph (m + 1)) := sphCap m 1 (1 / 3)

theorem mem_sphLowerCap {z : Sph (m + 1)} : z ∈ sphLowerCap m ↔ sphHeight z ≤ 1 / 3 := by
  rw [sphLowerCap, mem_sphCap]; constructor <;> intro h <;> linarith

theorem mem_sphUpperCap {z : Sph (m + 1)} : z ∈ sphUpperCap m ↔ -(1 / 3) ≤ sphHeight z := by
  rw [sphUpperCap, mem_sphCap]; constructor <;> intro h <;> linarith

variable (m) in
/-- **The contraction of the enlarged lower hemisphere onto the south pole.** -/
noncomputable def sphLowerCapContraction :
    ContractionData ↥(sphLowerCap m) (capPole m (-1) (1 / 3) (by norm_num) (by norm_num)) :=
  capContraction (-1) (1 / 3) (by norm_num) (by norm_num) (by norm_num)

variable (m) in
/-- **The contraction of the enlarged upper hemisphere onto the north pole.** -/
noncomputable def sphUpperCapContraction :
    ContractionData ↥(sphUpperCap m) (capPole m 1 (1 / 3) (by norm_num) (by norm_num)) :=
  capContraction 1 (1 / 3) (by norm_num) (by norm_num) (by norm_num)

/-! ### The two enlarged hemispheres cover the sphere -/

instance instContractibleSpaceSphLowerCap (m : ℕ) : ContractibleSpace (sphLowerCap m) :=
  (sphLowerCapContraction m).contractibleSpace

instance instContractibleSpaceSphUpperCap (m : ℕ) : ContractibleSpace (sphUpperCap m) :=
  (sphUpperCapContraction m).contractibleSpace

variable (m) in
/-- The part of `S^{m+1}` strictly below a given height is open. -/
theorem isOpen_sphHeight_lt (c : ℝ) : IsOpen {z : Sph (m + 1) | sphHeight z < c} :=
  isOpen_lt continuous_sphHeight continuous_const

variable (m) in
/-- The part of `S^{m+1}` strictly above a given height is open. -/
theorem isOpen_lt_sphHeight (c : ℝ) : IsOpen {z : Sph (m + 1) | c < sphHeight z} :=
  isOpen_lt continuous_const continuous_sphHeight

variable (m) in
/-- The interiors of the two enlarged hemispheres cover `S^{m+1}`. -/
theorem sphCap_interior_union :
    interior (sphLowerCap m) ∪ interior (sphUpperCap m) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases hz : sphHeight z < 1 / 3
  · refine Or.inl ((isOpen_sphHeight_lt m (1 / 3)).subset_interior_iff.2 ?_ hz)
    intro w hw
    exact mem_sphLowerCap.2 (le_of_lt hw)
  · refine Or.inr ((isOpen_lt_sphHeight m (-(1 / 3))).subset_interior_iff.2 ?_ ?_)
    · intro w hw
      exact mem_sphUpperCap.2 (le_of_lt hw)
    · rw [not_lt] at hz
      change -(1 / 3 : ℝ) < sphHeight z
      linarith


variable (m) in
/-- The intersection of the two enlarged hemispheres: the belt `{|z_last| ≤ 1/3}`. -/
noncomputable def sphBelt : Set (Sph (m + 1)) := sphLowerCap m ∩ sphUpperCap m

theorem mem_sphBelt {z : Sph (m + 1)} :
    z ∈ sphBelt m ↔ -(1 / 3) ≤ sphHeight z ∧ sphHeight z ≤ 1 / 3 := by
  rw [sphBelt, Set.mem_inter_iff, mem_sphLowerCap, mem_sphUpperCap, and_comm]

/-- The vector attached to a pair `(x, a) ∈ Sph m × [-1/3, 1/3]`, namely `(√(1 - a²) x, a)`. -/
noncomputable def beltVec (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :
    EuclideanSpace ℝ (Fin (m + 2)) :=
  snocLp (Real.sqrt (1 - (p.2 : ℝ) ^ 2) • (p.1 : EuclideanSpace ℝ (Fin (m + 1)))) (p.2 : ℝ)

theorem beltVec_last (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :
    beltVec p (Fin.last (m + 1)) = (p.2 : ℝ) := snocLp_last _ _

theorem norm_beltVec (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) : ‖beltVec p‖ = 1 := by
  have hx : ‖(p.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have h2 : -(1 / 3) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 / 3 := Set.mem_Icc.mp p.2.2
  have hnn : (0 : ℝ) ≤ 1 - (p.2 : ℝ) ^ 2 := by nlinarith [h2.1, h2.2]
  refine norm_eq_one_of_norm_sq_eq_one ?_
  rw [beltVec, norm_snocLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hnn, hx]
  ring

/-- The parametrisation of the belt by `Sph m × [-1/3, 1/3]`. -/
noncomputable def beltOfProd (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) : ↥(sphBelt m) :=
  ⟨⟨beltVec p, mem_sphere_zero_iff_norm.mpr (norm_beltVec p)⟩, by
    have h2 : -(1 / 3) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 / 3 := Set.mem_Icc.mp p.2.2
    rw [mem_sphBelt]
    show -(1 / 3) ≤ beltVec p (Fin.last (m + 1)) ∧ beltVec p (Fin.last (m + 1)) ≤ 1 / 3
    rw [beltVec_last]
    exact h2⟩

theorem continuous_beltOfProd : Continuous (beltOfProd (m := m)) := by
  have hx : Continuous fun p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) =>
      (p.1 : EuclideanSpace ℝ (Fin (m + 1))) := continuous_subtype_val.comp continuous_fst
  have ha : Continuous fun p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hsqrt : Continuous fun p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) =>
      Real.sqrt (1 - (p.2 : ℝ) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (ha.pow 2))
  exact ((continuous_snocLp.comp ((hsqrt.smul hx).prodMk ha)).subtype_mk _).subtype_mk _

theorem beltOfProd_bijective : Function.Bijective (beltOfProd (m := m)) := by
  constructor
  · intro p q hpq
    have hpq' : beltVec p = beltVec q := congrArg (fun w : ↥(sphBelt m) => w.1.1) hpq
    obtain ⟨hv, hc⟩ := snocLp_eq_iff.mp hpq'
    have h2 : -(1 / 3) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 / 3 := Set.mem_Icc.mp p.2.2
    have hpos : (0 : ℝ) < Real.sqrt (1 - (p.2 : ℝ) ^ 2) := by
      apply Real.sqrt_pos.mpr; nlinarith [h2.1, h2.2]
    rw [hc] at hv hpos
    exact Prod.ext (Subtype.ext (smul_right_injective _ (ne_of_gt hpos) hv)) (Subtype.ext hc)
  · rintro ⟨z, hz⟩
    rw [mem_sphBelt] at hz
    have hnorm : ‖sphEquator z‖ ^ 2 = 1 - sphHeight z ^ 2 := norm_sphEquator_sq z
    have hpos : (0 : ℝ) < 1 - sphHeight z ^ 2 := by nlinarith [hz.1, hz.2]
    have hne : ‖sphEquator z‖ ≠ 0 := by
      intro hzero
      rw [hzero] at hnorm
      nlinarith
    have hx : ‖‖sphEquator z‖⁻¹ • sphEquator z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have hsqrt : Real.sqrt (1 - sphHeight z ^ 2) = ‖sphEquator z‖ := by
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨(⟨‖sphEquator z‖⁻¹ • sphEquator z, mem_sphere_zero_iff_norm.mpr hx⟩,
      ⟨sphHeight z, Set.mem_Icc.mpr ⟨hz.1, hz.2⟩⟩), Subtype.ext (Subtype.ext ?_)⟩
    show snocLp (Real.sqrt (1 - sphHeight z ^ 2) • (‖sphEquator z‖⁻¹ • sphEquator z))
      (sphHeight z) = (z : EuclideanSpace ℝ (Fin (m + 2)))
    rw [hsqrt, smul_smul, mul_inv_cancel₀ hne, one_smul, snocLp_sphEquator_sphHeight]

variable (m) in
/-- **The intersection of the two enlarged hemispheres is `Sph m × [-1/3, 1/3]`.** -/
noncomputable def sphBeltHomeo : ↥(sphBelt m) ≃ₜ Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) :=
  haveI : CompactSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ beltOfProd_bijective)
    continuous_beltOfProd).symm

variable (m) in
/-- **The intersection of the two enlarged hemispheres is homotopy equivalent to `Sph m`.** -/
noncomputable def sphBeltHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(sphBelt m) (Sph m) :=
  haveI : ContractibleSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    (convex_Icc _ _).contractibleSpace ⟨0, by rw [Set.mem_Icc]; norm_num⟩
  (sphBeltHomeo m).toHomotopyEquiv.trans
    (prodHomotopyEquivOfContractible (Sph m) (Set.Icc (-(1 / 3) : ℝ) (1 / 3)))

end Sphere


end NRR.SphereGeometry
