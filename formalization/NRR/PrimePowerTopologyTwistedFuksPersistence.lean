import NRR.PrimePowerTopologyGeneralCellHomology
import NRR.PrimePowerTopologyTwoColumnModTwoTwisted
import NRR.PrimePowerTopologyTwistedCycleLifting
import NRR.PrimePowerTopologyRelativeOrbitBasis

/-! Lowest-degree comparison for the genuine twisted relative Fuks groups,
and persistence of the minimal class through the compactified filtration. -/

noncomputable section
open CategoryTheory Limits

namespace NRR.PrimePowerTopology

variable (R : Type) [CommRing R] {d n : ℕ} [NeZero n]
variable (χ : Equiv.Perm (Fin n) →* Rˣ)

private theorem ordinaryFuksRelative_zero_below {k q : ℕ} (hn : 2 ≤ n)
    (h : q < k+1+n) :
    IsZero ((fuksRelativeComplex R (d := d) (n := n) (Nat.le_succ k)).homology q) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  letI : NeZero m := ⟨by omega⟩
  exact isZero_generalFuksRelative_off_dimension R d m k q h.ne

/-- For a fixed lower level, no ordinary class can occur below the first
possible cell dimension, even after all subsequent attachments. -/
theorem isZero_fuksRelative_below_first_dimension {a k q : ℕ} (hn : 2 ≤ n)
    (ha : a ≤ k) (hq : q < a+1+n) :
    IsZero ((fuksRelativeComplex R (d := d) (n := n) ha).homology q) := by
  induction k, ha using Nat.le_induction with
  | base =>
      let i := compactifiedFuksInclusion (d := d) (n := n) (le_refl a)
      have hi : i = 𝟙 _ := rfl
      letI : Epi (NRR.SingularHomology.CsingMap R i) := by
        rw [hi, NRR.SingularHomology.CsingMap_id]
        infer_instance
      exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map_isZero
        (isZero_cokernel_of_epi (NRR.SingularHomology.CsingMap R i))
  | succ k hk ih =>
      let T := fuksTriple R (d := d) (n := n) hk (Nat.le_succ k)
      have ht := fuksTriple_shortExact R (d := d) (n := n) hk (Nat.le_succ k)
      apply (ht.homology_exact₂ q).isZero_X₂
      · exact ih.eq_zero_of_src _
      · exact (ordinaryFuksRelative_zero_below R (d := d) hn (show q < k+1+n by omega)).eq_zero_of_tgt _

/-- At and below the cell dimension every twisted class is represented by
the image of an ordinary class. The proof uses freeness on singular simplex
orbits before taking homology. -/
theorem epi_twistedFuksRelativeProj_through_cell_degree {k q : ℕ}
    (hn : 2 ≤ n) (h : q ≤ k+1+n) :
    Epi (HomologicalComplex.homologyMap
      (twistedFuksRelativeProj R (d := d) χ (Nat.le_succ k)) q) := by
  let hab := Nat.le_succ k
  apply epi_twistedProjection_of_free_orbits χ (fuksRelativeRelabel R (d := d) hab)
    (fuksRelativeRelabel_mul R hab) (fun i => fuksRelativeOrbitBasis R hab i)
    (fun i => fuksRelativeOrbitBasis_relabel R hab i) q
  exact fun i hi => ordinaryFuksRelative_zero_below R hn (lt_of_lt_of_le hi h)

theorem isZero_twistedFuksRelative_below_cell_degree {k q : ℕ}
    (hn : 2 ≤ n) (h : q < k+1+n) :
    IsZero ((twistedFuksRelativeComplex R (d := d) χ (Nat.le_succ k)).homology q) := by
  let π := HomologicalComplex.homologyMap
    (twistedFuksRelativeProj R (d := d) χ (Nat.le_succ k)) q
  letI : Epi π := epi_twistedFuksRelativeProj_through_cell_degree R χ hn h.le
  exact IsZero.of_epi π (ordinaryFuksRelative_zero_below R hn h)

/-- Higher cells preserve the lower-degree twisted groups, including in
characteristic dividing the order of the relabelling group. -/
theorem isIso_twistedFuksRelative_step {a k q : ℕ} (ha : a ≤ k)
    (hn : 2 ≤ n) (h : q+1 < k+1+n) :
    IsIso (HomologicalComplex.homologyMap (twistedFuksRelativeMap R (d := d) χ
      ha (ha.trans (Nat.le_succ k)) (le_refl a) (Nat.le_succ k)) q) := by
  let T := twistedFuksTriple R (d := d) χ ha (Nat.le_succ k)
  have ht := twistedFuksTriple_shortExact R (d := d) χ ha (Nat.le_succ k)
  have hi : ht.δ (q+1) q rfl = 0 :=
    (isZero_twistedFuksRelative_below_cell_degree R (d := d) χ hn h).eq_zero_of_src _
  have hj : HomologicalComplex.homologyMap T.g q = 0 :=
    (isZero_twistedFuksRelative_below_cell_degree R (d := d) χ hn (show q < k+1+n by omega)).eq_zero_of_tgt _
  letI : Mono (HomologicalComplex.homologyMap T.f q) := (ht.homology_exact₁ (q+1) q rfl).mono_g hi
  letI : Epi (HomologicalComplex.homologyMap T.f q) := (ht.homology_exact₂ q).epi_f hj
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap T.f q)

/-- Every twisted source class has zero first boundary at a power of two. -/
theorem twistedFuksDifferential_two_pow {a : ℕ}
    (χ₂ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (hpow : n = 2^a) :
    twistedFuksDifferential (ZMod 2) (d := d+1) χ₂ (Nat.le_succ d)
      (Nat.le_succ (d+1)) (d+n+1) = 0 := by
  let π := HomologicalComplex.homologyMap (twistedFuksRelativeProj (ZMod 2) (d := d+1)
    χ₂ (Nat.le_succ (d+1))) (d+n+2)
  letI : Epi π := epi_twistedFuksRelativeProj_through_cell_degree (ZMod 2)
    (d := d+1) χ₂ hn (show d+n+2 ≤ d+1+1+n by omega)
  apply (cancel_epi π).mp
  exact (projection_comp_twistedFuksDifferential_two_pow χ₂ hn hpow).trans comp_zero.symm

private theorem twistedUpperInclusion_id {a b : ℕ} (h : a ≤ b) :
    twistedFuksRelativeMap R (d := d) χ h h (le_refl a) (le_refl b) = 𝟙 _ := by
  let π := twistedFuksRelativeProj R (d := d) χ h
  have he : Epi π := coequalizer.π_epi
  apply he.left_cancellation
  change twistedFuksRelativeProj R χ h ≫ _ = _ ≫ 𝟙 _
  rw [twistedFuksRelativeProj_map, Category.comp_id]
  have hi : fuksRelativeMap R (d := d) (n := n) h h (le_refl a) (le_refl b) = 𝟙 _ := by
    exact NRR.SingularHomology.relComplexMap_id R (compactifiedFuksInclusion h)
  rw [hi, Category.id_comp]

private theorem twistedUpperInclusion_comp {a b c e : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) :
    twistedFuksRelativeMap R (d := d) χ hab (hab.trans hbc) (le_refl a) hbc ≫
      twistedFuksRelativeMap R χ (hab.trans hbc) ((hab.trans hbc).trans hce) (le_refl a) hce =
    twistedFuksRelativeMap R χ hab ((hab.trans hbc).trans hce) (le_refl a) (hbc.trans hce) := by
  let π := twistedFuksRelativeProj R (d := d) χ hab
  have he : Epi π := coequalizer.π_epi
  apply he.left_cancellation
  change twistedFuksRelativeProj R χ hab ≫ _ = twistedFuksRelativeProj R χ hab ≫ _
  rw [twistedFuksRelativeProj_map_assoc, twistedFuksRelativeProj_map, twistedFuksRelativeProj_map]
  rw [← Category.assoc]
  congr 1
  unfold fuksRelativeMap
  rw [NRR.SingularHomology.relComplexMap_comp]

/-- The first twisted differential is the only possible incoming boundary
for the minimal class. This compares the actual inclusion to any later
compactified level, with arbitrary coefficient character. -/
theorem mono_twistedFuksMinimal_to_level_of_first_zero {k q : ℕ}
    (hn : 2 ≤ n) (hdegree : q = d+n) (hk : d ≤ k)
    (hfirst : twistedFuksDifferential R (d := d) χ (Nat.sub_le d 1)
      (Nat.le_succ d) q = 0) :
    Mono (HomologicalComplex.homologyMap (twistedFuksRelativeMap R (d := d) χ
      (Nat.sub_le d 1) ((Nat.sub_le d 1).trans hk) (le_refl _) hk) q) := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [twistedUpperInclusion_id, HomologicalComplex.homologyMap_id]
      infer_instance
  | succ k hk ih =>
      let hlow := (Nat.sub_le d 1).trans hk
      let f := twistedFuksRelativeMap R (d := d) χ (Nat.sub_le d 1) hlow (le_refl _) hk
      let g := twistedFuksRelativeMap R (d := d) χ hlow (hlow.trans (Nat.le_succ k))
        (le_refl _) (Nat.le_succ k)
      letI : Mono (HomologicalComplex.homologyMap f q) := ih
      letI : Mono (HomologicalComplex.homologyMap g q) := by
        by_cases he : k = d
        · subst k
          exact (mono_twistedFuksRelativeInclusion_iff R χ (Nat.sub_le d 1)
            (Nat.le_succ d) q).mpr hfirst
        · letI : IsIso (HomologicalComplex.homologyMap g q) :=
            isIso_twistedFuksRelative_step R (d := d) χ hlow hn (by omega)
          infer_instance
      rw [← twistedUpperInclusion_comp R χ (Nat.sub_le d 1) hk (Nat.le_succ k),
        HomologicalComplex.homologyMap_comp]
      exact mono_comp (HomologicalComplex.homologyMap f q) (HomologicalComplex.homologyMap g q)

/-- The genuine nonzero minimal class with two-power many labels survives
to the full compactification (the top Fuks level is the entire space). -/
theorem twistedMinimalClass_two_pow_survives {a : ℕ}
    (χ₂ : Equiv.Perm (Fin n) →* (ZMod 2)ˣ) (hn : 2 ≤ n) (hpow : n = 2^a)
    (i₀ : Fin n) :
    HomologicalComplex.homologyMap (twistedFuksRelativeMap (ZMod 2) (d := d+1) χ₂
      (Nat.le_succ d) (show d ≤ (d+1)*n by nlinarith) (le_refl d)
      (show d+1 ≤ (d+1)*n by nlinarith)) ((d+1)+n)
        (coherentTwistedMinimalClass (ZMod 2) χ₂ (show 0 < d+1 by omega) i₀) ≠ 0 := by
  let f := HomologicalComplex.homologyMap (twistedFuksRelativeMap (ZMod 2) (d := d+1) χ₂
    (Nat.le_succ d) (show d ≤ (d+1)*n by nlinarith) (le_refl d)
    (show d+1 ≤ (d+1)*n by nlinarith)) ((d+1)+n)
  have hfirst : twistedFuksDifferential (ZMod 2) (d := d+1) χ₂ (Nat.le_succ d)
      (Nat.le_succ (d+1)) ((d+1)+n) = 0 := by
    rw [show (d+1)+n = d+n+1 by omega]
    exact twistedFuksDifferential_two_pow χ₂ hn hpow
  have hm : Mono f := mono_twistedFuksMinimal_to_level_of_first_zero (ZMod 2)
    (d := d+1) χ₂ hn rfl (show d+1 ≤ (d+1)*n by nlinarith) hfirst
  intro hz
  exact coherentTwistedMinimalClass_ne_zero (ZMod 2) χ₂ (show 0 < d+1 by omega) i₀
    ((ModuleCat.mono_iff_injective f).mp hm (hz.trans (map_zero f.hom).symm))

end NRR.PrimePowerTopology
