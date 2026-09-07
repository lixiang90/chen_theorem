import Submission.ChenTheorem.Lemma6.RealHighHeightRegion
import Submission.ChenTheorem.Lemma6.RealLowHeightRegion

set_option autoImplicit true
namespace Chen

theorem zero_height_log_le_conductor_height_log {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    Real.log ((q : ℝ) * 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  apply Real.log_le_log (by positivity)
  nlinarith [abs_nonneg t]

theorem exists_primitive_real_nonreal_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ, s.im ≠ 0 →
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨r, cL, hr, hcL, hlow⟩ := exists_primitive_real_low_height_zero_im_eq_zero
  obtain ⟨cH, hcH, hhigh⟩ := exists_primitive_real_zero_free_away_axis r hr
  refine ⟨min cL cH, lt_min hcL hcH, ?_⟩
  intro q inst χ hq hχ hsq s him hs hz
  have hL := primitiveZeroFreeHeightLog_pos hq s.im
  by_cases ht : |s.im| ≤ r
  · have hL0 : 0 < Real.log ((q : ℝ) * 2) := by
      have h := conductor_height_log_ge_threeQuarters q hq 0
      simp only [abs_zero, zero_add] at h
      linarith
    have hw : min cL cH / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ cL / Real.log ((q : ℝ) * 2) := by
      calc
        _ ≤ cL / Real.log ((q : ℝ) * (|s.im| + 2)) :=
          div_le_div_of_nonneg_right (min_le_left _ _) hL.le
        _ ≤ _ := div_le_div_of_nonneg_left hcL.le hL0 (zero_height_log_le_conductor_height_log hq s.im)
    exact him (hlow q χ hq hχ hsq s (by linarith) ht hz)
  · have hw := div_le_div_of_nonneg_right (min_le_right cL cH) hL.le
    exact hhigh q χ hq hχ hsq s (le_of_not_ge ht) (by linarith) hz

/-- The full logarithmic region for a primitive real character contains at most
one zero. Any such exceptional zero is real and simple. -/
theorem exists_primitive_real_exceptional_zero_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
      (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re ∧
        DirichletCharacter.LFunction χ s = 0}) ∧
      ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
        DirichletCharacter.LFunction χ s = 0 →
        s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨cR, hcR, hR⟩ := exists_primitive_real_nonreal_zero_free_region
  obtain ⟨cU, hcU, hU⟩ := exists_primitive_real_zero_unique
  obtain ⟨cS, hcS, hS⟩ := exists_primitive_real_zero_deriv_ne_zero
  let c := min cR (min cU cS)
  have hc : 0 < c := lt_min hcR (lt_min hcU hcS)
  have hcR' : c ≤ cR := min_le_left _ _
  have hcU' : c ≤ cU := (min_le_right _ _).trans (min_le_left _ _)
  have hcS' : c ≤ cS := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro q inst χ hq hχ hsq
  have hreal : ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
    intro s hs hz
    by_contra him
    have hw := div_le_div_of_nonneg_right hcR' (primitiveZeroFreeHeightLog_pos hq s.im).le
    exact hR q χ hq hχ hsq s him (by linarith) hz
  have hL0 : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hUdiv := div_le_div_of_nonneg_right hcU' hL0.le
  have hSdiv := div_le_div_of_nonneg_right hcS' hL0.le
  constructor
  · intro s hs t ht
    have hsi := hreal s hs.1 hs.2
    have hti := hreal t ht.1 ht.2
    have heS : (s.re : ℂ) = s := by apply Complex.ext <;> simp [hsi]
    have heT : (t.re : ℂ) = t := by apply Complex.ext <;> simp [hti]
    have hs' := hs.1
    have ht' := ht.1
    simp only [hsi, hti, abs_zero, zero_add] at hs' ht'
    have he := hU q χ hq hχ hsq s.re t.re (by linarith) (by linarith)
      (by rw [heS]; exact hs.2) (by rw [heT]; exact ht.2)
    apply Complex.ext
    · exact he
    · rw [hsi, hti]
  · intro s hs hz
    have him := hreal s hs hz
    refine ⟨him, ?_⟩
    have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [him]
    simp only [him, abs_zero, zero_add] at hs
    have h := hS q χ hq hχ hsq s.re (by linarith) (by rw [he]; exact hz)
    simpa only [he] using h

end Chen
