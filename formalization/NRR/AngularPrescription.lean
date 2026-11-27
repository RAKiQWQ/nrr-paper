import NRR.AngularProfile
import NRR.AngularRealization
import NRR.EndDegrees

/-! The actual finite prescription associated with the binomial degree profile. -/

open Set Topology Finset
open scoped unitInterval Classical
noncomputable section

namespace NRR.AngularMap

open Surface AngularLoops

theorem center_injective {n : ℕ} (hn : 0 < n) : Function.Injective (center n) := by
  intro i j h
  have hnr : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he : 2*(i:ℝ)/(n:ℝ) = 2*(j:ℝ)/(n:ℝ) := by
    dsimp [center] at h
    linarith
  have hm := (div_left_inj' hnr).mp he
  exact_mod_cast (show (i:ℝ) = (j:ℝ) by linarith)

theorem center_reflect {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j ≤ n) :
    center n (n-j) = -center n j := by
  have hnr : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold center
  rw [Nat.cast_sub hj]
  field_simp
  ring

theorem center_inner {n j : ℕ} (hn : 0 < n) (hj : 0 < j) (hjn : j < n) :
    |center n j| < 1 := by
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hjr : (0:ℝ) < j := Nat.cast_pos.mpr hj
  have hjnr : (j:ℝ) < n := by exact_mod_cast hjn
  unfold center
  rw [abs_lt]
  constructor
  · have h : 2*(j:ℝ)/(n:ℝ) < 2 := (div_lt_iff₀ hnr).mpr (by linarith)
    linarith
  · have h : 0 < 2*(j:ℝ)/(n:ℝ) := div_pos (by positivity) hnr
    linarith

def profilePunctures (n : ℕ) : Finset ℝ := (range (n+1)).image (center n)

theorem profilePunctures_neg {n : ℕ} (hn : 0 < n) :
    ∀ q ∈ profilePunctures n, -q ∈ profilePunctures n := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  exact mem_image.mpr ⟨n-j, mem_range.mpr (by omega), center_reflect hn hjn⟩

/-- Subtracting one changes branch-sum degree into angular index.  The value
away from the finite puncture set is irrelevant, including a possible absent
central puncture. -/
def angularPrescription (n : ℕ) (a : ℕ → ℤ) (q : ℝ) : ℤ :=
  (∑ j ∈ range (n+1), if center n j = q then Binomial.degreeProfile n a j else 0) - 1

theorem angularPrescription_center {n : ℕ} (hn : 0 < n) (a : ℕ → ℤ)
    {j : ℕ} (hj : j ≤ n) :
    angularPrescription n a (center n j) = Binomial.degreeProfile n a j - 1 := by
  unfold angularPrescription
  congr 1
  rw [sum_eq_single j]
  · simp
  · intro i hi hne
    exact if_neg (fun h => hne (center_injective hn h))
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (by omega)))

theorem angularPrescription_neg {n : ℕ} (hn : 0 < n) (a : ℕ → ℤ) (q : ℝ) :
    angularPrescription n a (-q) = angularPrescription n a q := by
  unfold angularPrescription
  congr 1
  calc
    _ = ∑ j ∈ range (n+1),
        if center n (n-j) = -q then Binomial.degreeProfile n a (n-j) else 0 := by
      symm
      simpa using sum_range_reflect
        (fun j => if center n j = -q then Binomial.degreeProfile n a j else 0) (n+1)
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      rw [center_reflect hn hjn, Binomial.degreeProfile_symm n a hjn]
      simp only [neg_inj]

theorem angularPrescription_central {n : ℕ} (hn : 0 < n) (a : ℕ → ℤ) :
    ∃ k : ℤ, angularPrescription n a 0 = 2*k-1 := by
  have each (j : ℕ) (hj : j ∈ range (n+1)) :
      Even (if center n j = 0 then Binomial.degreeProfile n a j else 0) := by
    split_ifs with he
    · have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      have href : n-j = j := center_injective hn (by rw [center_reflect hn hjn, he, neg_zero])
      unfold Binomial.degreeProfile
      rw [href]
      exact ⟨_, rfl⟩
    · exact ⟨0, by norm_num⟩
  have evensum : ∀ S : Finset ℕ, S ⊆ range (n+1) →
      Even (∑ j ∈ S, if center n j = 0 then Binomial.degreeProfile n a j else 0) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | @insert j S hj ih =>
      intro hS
      rw [sum_insert hj]
      exact (each j (hS (mem_insert_self _ _))).add
        (ih (fun i hi => hS (mem_insert_of_mem hi)))
  obtain ⟨k, hk⟩ := evensum (range (n+1)) (Finset.Subset.refl _)
  refine ⟨k, ?_⟩
  unfold angularPrescription
  rw [hk]
  ring

theorem angularPrescription_outside {n : ℕ} (hn : 2 ≤ n) (a : ℕ → ℤ)
    (q : ℝ) (hq : q ∈ profilePunctures n) (hout : 1 ≤ |q|) :
    angularPrescription n a q = 0 := by
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [angularPrescription_center (by omega) a hjn]
  have endpt : j = 0 ∨ j = n := by
    by_contra! h
    exact (not_lt_of_ge hout) (center_inner (by omega) (by omega) (by omega))
  rcases endpt with hj0 | hjn
  · rw [hj0, Binomial.degreeProfile_zero n hn a]; simp
  · have he : Binomial.degreeProfile n a n = Binomial.degreeProfile n a 0 := by
      simpa using Binomial.degreeProfile_symm n a (j := 0) (by omega)
    rw [hjn, he, Binomial.degreeProfile_zero n hn a]
    simp

/-- Every binomial degree profile is realized by a literal doubled half-path
at all its punctures, including the endpoints with angular index zero. -/
theorem exists_binomial_half_profile {n : ℕ} (hn : 2 ≤ n) (a : ℕ → ℤ) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < 1 ∧
      ∃ p : Path (top (profilePunctures n) 0 δ (by norm_num) hδ)
          (reflect (profilePunctures_neg (by omega))
            (top (profilePunctures n) 0 δ (by norm_num) hδ)),
        ∀ j (hj : j ≤ n), increment
          (probe (center n j) (mem_image.mpr ⟨j,mem_range.mpr (by omega),rfl⟩))
          (doubled (profilePunctures_neg (by omega)) p) =
            (Binomial.degreeProfile n a j : ℝ) - 1 := by
  obtain ⟨k, hk⟩ := angularPrescription_central (by omega : 0 < n) a
  obtain ⟨δ,hδ,h1,p,hp⟩ := exists_symmetric_half_profile
    (profilePunctures n) (profilePunctures_neg (by omega)) (angularPrescription n a)
    (fun q _ => angularPrescription_neg (by omega) a q)
    (angularPrescription_outside hn a) k hk
  refine ⟨δ,hδ,h1,p,fun j hj => ?_⟩
  rw [hp, angularPrescription_center (by omega) a hj, Int.cast_sub, Int.cast_one]

end NRR.AngularMap
