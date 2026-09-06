import ChenTheorem.Lemma6.NonrealZeroInequality

namespace Chen

theorem four_div_gap_contradiction {x y D : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : 8 * y ≤ 9 * x) (hDx : D * x ≤ 1 / 4)
    (hineq : 4 / y ≤ 3 / x + D) : False := by
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hy).mp hineq) hx.le
  have he : (3 / x + D) * y * x = 3 * y + (D * x) * y := by
    calc
      _ = (3 / x * x) * y + (D * x) * y := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx.ne']
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_right hDx hy.le
  nlinarith

/-- A uniform classical logarithmic zero-free region for primitive characters
whose square is nonprincipal. Real characters, including exceptional real zeros,
are deliberately not covered by this theorem. -/
theorem exists_primitive_nonreal_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 ≠ 1 → ∀ s : ℂ,
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨δ, C, hδ, hC, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  let B : ℝ := 4 * C + 360002
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 16) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha16 : a ≤ 1 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hχsq s hs hzero
  let L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : 3 / 4 ≤ L := conductor_height_log_ge_threeQuarters q hq s.im
  have hLpos : 0 < L := by linarith
  have hβ : s.re ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - s.re
  let D : ℝ := 3 * C + 360002 * L
  have hx : 0 < x := div_pos ha hLpos
  have hxL : x * L = a := div_mul_cancel₀ _ hLpos.ne'
  have hxδ : x < δ := by
    apply (div_lt_iff₀ hLpos).mpr
    nlinarith
  have hx16 : x ≤ 1 / 12 := by
    apply (div_le_iff₀ hLpos).mpr
    linarith
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < s.re at hs
  rw [hquot] at hs
  have hxy : 8 * y ≤ 9 * x := by dsimp [y, σ]; linarith
  have hβ' : 7 / 8 < s.re := by linarith
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hz : DirichletCharacter.LFunction χ
      ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
    rw [Complex.re_add_im]
    exact hzero
  have hi := primitive_nonreal_zero_inequality hq hχ hχsq σ s.re s.im C
    hσ hσ' hβ' hz (hzeta σ hσ hσδ)
  change 4 / y ≤ 3 / (σ - 1) + 3 * C + 360002 * L at hi
  have hσx : σ - 1 = x := by dsimp [σ]; ring
  rw [hσx] at hi
  exact four_div_gap_contradiction hx hy hxy hDx (by dsimp [D]; linarith [hi])

end Chen
