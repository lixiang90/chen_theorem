import ChenTheorem.Lemma6.RealMultipleZeroBound
import ChenTheorem.Lemma6.RealZeroUniqueness

namespace Chen

theorem exists_primitive_real_zero_deriv_ne_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ,
      1 - c / Real.log ((q : ℝ) * 2) < β →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
  obtain ⟨δ, C, hδ, hC, hu⟩ := exists_real_character_logDeriv_real_axis_bound
  let B : ℝ := 2 * C + 60001
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 8) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hsq β hβ hf hdf
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - β
  let D : ℝ := C + Real.log q / 4 + 60000 * L
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < β at hβ
  rw [hquot] at hβ
  have hb : β ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hf
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have hmult := primitive_LFunction_logDeriv_re_ge_multiple_real_zero hq hχ σ β
    hσ hσ' (by linarith) hf hdf
  have hup := hu q χ hsq σ hσ hσδ
  have hlogq : Real.log q ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hy : 0 < y := by dsimp [y, σ]; linarith
  have hyx : y ≤ 9 * x / 8 := by dsimp [y, σ]; linarith
  have hi : 1 / y + 1 / y ≤ 1 / x + D := by
    have he : σ - 1 = x := by dsimp [σ]; ring
    rw [he] at hup
    change 2 / y - 60000 * L ≤ _ at hmult
    dsimp [D]
    rw [show (2 : ℝ) / y = 1 / y + 1 / y by ring] at hmult
    linarith
  exact two_real_zero_gaps_contradiction hx hy hy hyx hyx hDx hi

/-- A primitive real character has at most one zero in a uniform logarithmic
box about 1; any such zero is real and simple. No existence or Siegel bound is asserted. -/
theorem exists_primitive_real_zero_box_unique_real_simple :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
      (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * 2) < s.re ∧
        |s.im| ≤ c / Real.log ((q : ℝ) * 2) ∧ DirichletCharacter.LFunction χ s = 0}) ∧
      ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * 2) < s.re →
        |s.im| ≤ c / Real.log ((q : ℝ) * 2) → DirichletCharacter.LFunction χ s = 0 →
        s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨cU, hcU, hU⟩ := exists_primitive_real_zero_box_subsingleton
  obtain ⟨cR, hcR, hR⟩ := exists_primitive_real_zero_box_im_eq_zero
  obtain ⟨cS, hcS, hS⟩ := exists_primitive_real_zero_deriv_ne_zero
  let c := min cU (min cR cS)
  have hc : 0 < c := lt_min hcU (lt_min hcR hcS)
  refine ⟨c, hc, ?_⟩
  intro q inst χ hq hχ hsq
  have hL : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hcU' := div_le_div_of_nonneg_right (show c ≤ cU from min_le_left _ _) hL.le
  have hcR' := div_le_div_of_nonneg_right
    (show c ≤ cR from (min_le_right _ _).trans (min_le_left _ _)) hL.le
  have hcS' := div_le_div_of_nonneg_right
    (show c ≤ cS from (min_le_right _ _).trans (min_le_right _ _)) hL.le
  constructor
  · intro s hs t ht
    exact hU q χ hq hχ hsq
      ⟨by linarith [hs.1], hs.2.1.trans hcU', hs.2.2⟩
      ⟨by linarith [ht.1], ht.2.1.trans hcU', ht.2.2⟩
  · intro s hs ht hz
    have him := hR q χ hq hχ hsq s (by linarith) (ht.trans hcR') hz
    refine ⟨him, ?_⟩
    have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [him]
    have h := hS q χ hq hχ hsq s.re (by linarith) (by rw [he]; exact hz)
    simpa only [he] using h

end Chen
