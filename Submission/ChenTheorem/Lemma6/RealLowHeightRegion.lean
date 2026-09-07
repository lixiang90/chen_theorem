import Submission.ChenTheorem.Lemma6.RealLowHeightTools

set_option autoImplicit true
namespace Chen

/-- For a fixed positive height, independent of the modulus, zeros of primitive
real characters sufficiently close to 1 must be real. -/
theorem exists_primitive_real_low_height_zero_im_eq_zero :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ,
        1 - c / Real.log ((q : ℝ) * 2) < s.re → |s.im| ≤ r →
        DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
  obtain ⟨c₀, hc₀, hbox⟩ := exists_primitive_real_zero_box_im_eq_zero
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  obtain ⟨δp, Cp, hδp, hCp, hprincipal⟩ := exists_principal_complex_logDeriv_pole_bound
  let B : ℝ := 4 * Cz + 2 * Cp + 480002
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min c₀ (min (δz / 4) (min (δp / 4) (min (1 / 8) (1 / (32 * B)))))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₀ : a ≤ c₀ := min_le_left _ _
  have haz : a ≤ δz / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hap : a ≤ δp / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haB : a * B ≤ 1 / 32 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * B)).mp
      (show a ≤ 1 / (32 * B) from (min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith
  let r : ℝ := min (δp / 8) 1
  have hr : 0 < r := lt_min (by positivity) zero_lt_one
  have hrp : r ≤ δp / 8 := min_le_left _ _
  have hr1 : r ≤ 1 := min_le_right _ _
  refine ⟨r, a / 8, hr, by positivity, ?_⟩
  intro q inst χ hq hχ hsq s hs ht hzero
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  have hcdiv : (a / 8) / L ≤ c₀ / L :=
    div_le_div_of_nonneg_right (by linarith) hLp.le
  change 1 - (a / 8) / L < s.re at hs
  by_cases htbox : |s.im| ≤ c₀ / L
  · exact hbox q χ hq hχ hsq s (by linarith) htbox hzero
  · exfalso
    let x : ℝ := a / L
    let σ : ℝ := 1 + x
    let y : ℝ := σ - s.re
    let P : ℝ := (((x : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I)⁻¹).re
    let E : ℝ := 3 * Cz + Cp + 240000 * Real.log ((q : ℝ) * (|s.im| + 2)) + Real.log q
    have hx : 0 < x := div_pos ha hLp
    have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
    have hxt : x ≤ |s.im| := by
      have h := div_le_div_of_nonneg_right ha₀ hLp.le
      dsimp [x]
      linarith
    have hxz : x < δz := by apply (div_lt_iff₀ hLp).mpr; nlinarith
    have hxp : x < δp / 2 := by apply (div_lt_iff₀ hLp).mpr; nlinarith
    have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
    have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
    rw [hquot] at hs
    have hβ : s.re ≤ 1 := by
      by_contra! hh
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
        (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
    have hσ : 1 < σ := by dsimp [σ]; linarith
    have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
    have hσz : σ < 1 + δz := by dsimp [σ]; linarith
    have hσp : ‖(σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I - 1‖ < δp := by
      apply (norm_principal_shifted_point_sub_one_le hσ s.im).trans_lt
      dsimp [σ]
      linarith
    have hπ : P * x ≤ 1 / 5 := principal_shifted_pole_mul_le_one_fifth hx hxt
    have hheight := conductor_height_log_le_twice_zero_height hq s.im (ht.trans hr1)
    have hlogq : Real.log q ≤ L := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
      have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith
    have hE : E ≤ B * L := by dsimp [E, B]; change _ ≤ 2 * L at hheight; nlinarith
    have hEx : E * x ≤ 1 / 32 := by
      calc
        _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hE hx.le
        _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
        _ ≤ _ := by nlinarith [haB]
    have hDx : (P + E) * x ≤ 1 / 4 := by nlinarith
    have hz : DirichletCharacter.LFunction χ ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
      rw [Complex.re_add_im]; exact hzero
    have hi := primitive_real_zero_inequality hq hχ hsq σ s.re s.im Cz Cp
      hσ hσ' (by linarith) hz (hzeta σ hσ hσz)
      (hprincipal q _ (by simpa using hσ) hσp)
    have he : (σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I - 1 =
        (x : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I := by dsimp [σ]; push_cast; ring
    rw [he] at hi
    have hσx : σ - 1 = x := by dsimp [σ]; ring
    rw [hσx] at hi
    have hi' : 4 / y ≤ 3 / x + (P + E) := by dsimp [y, P, E]; linarith
    exact four_div_gap_contradiction hx (by dsimp [y]; linarith)
      (by dsimp [y, σ]; linarith) hDx hi'

/-- The fixed-height strip contains at most one zero, and it is real and simple. -/
theorem exists_primitive_real_low_height_unique_real_simple :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
        (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * 2) < s.re ∧
          |s.im| ≤ r ∧ DirichletCharacter.LFunction χ s = 0}) ∧
        ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * 2) < s.re → |s.im| ≤ r →
          DirichletCharacter.LFunction χ s = 0 →
          s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨r, cR, hr, hcR, hR⟩ := exists_primitive_real_low_height_zero_im_eq_zero
  obtain ⟨cU, hcU, hU⟩ := exists_primitive_real_zero_unique
  obtain ⟨cS, hcS, hS⟩ := exists_primitive_real_zero_deriv_ne_zero
  let c := min cR (min cU cS)
  have hc : 0 < c := lt_min hcR (lt_min hcU hcS)
  refine ⟨r, c, hr, hc, ?_⟩
  intro q inst χ hq hχ hsq
  have hL : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hcR' := div_le_div_of_nonneg_right (show c ≤ cR from min_le_left _ _) hL.le
  have hcU' := div_le_div_of_nonneg_right
    (show c ≤ cU from (min_le_right _ _).trans (min_le_left _ _)) hL.le
  have hcS' := div_le_div_of_nonneg_right
    (show c ≤ cS from (min_le_right _ _).trans (min_le_right _ _)) hL.le
  have hreal : ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * 2) < s.re → |s.im| ≤ r →
      DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
    intro s hs ht hz
    exact hR q χ hq hχ hsq s (by linarith) ht hz
  constructor
  · intro s hs t ht
    have hsi := hreal s hs.1 hs.2.1 hs.2.2
    have hti := hreal t ht.1 ht.2.1 ht.2.2
    have heS : (s.re : ℂ) = s := by apply Complex.ext <;> simp [hsi]
    have heT : (t.re : ℂ) = t := by apply Complex.ext <;> simp [hti]
    have he := hU q χ hq hχ hsq s.re t.re (by linarith [hs.1]) (by linarith [ht.1])
      (by rw [heS]; exact hs.2.2) (by rw [heT]; exact ht.2.2)
    apply Complex.ext
    · exact he
    · rw [hsi, hti]
  · intro s hs ht hz
    have him := hreal s hs ht hz
    refine ⟨him, ?_⟩
    have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [him]
    have h := hS q χ hq hχ hsq s.re (by linarith) (by rw [he]; exact hz)
    simpa only [he] using h

end Chen
