import Submission.ChenTheorem.Lemma6.RealCharacterZeroInequality

set_option autoImplicit true
namespace Chen

theorem conjugate_pair_gap_contradiction {x y t D : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hyx : y ≤ 9 * x / 8) (ht : |t| ≤ x / 8)
    (hDx : D * x ≤ 1 / 4)
    (hi : 2 * y / (y ^ 2 + t ^ 2) ≤ 1 / x + D) : False := by
  have hy : 0 < y := hx.trans_le hxy
  have hden : 0 < y ^ 2 + t ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hden).mp hi) hx.le
  have he : (1 / x + D) * (y ^ 2 + t ^ 2) * x =
      (y ^ 2 + t ^ 2) + (D * x) * (y ^ 2 + t ^ 2) := by
    calc
      _ = (1 / x * x) * (y ^ 2 + t ^ 2) + (D * x) * (y ^ 2 + t ^ 2) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx.ne', one_mul]
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_right hDx hden.le
  have hy2 : y ^ 2 ≤ 81 * x ^ 2 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (show 0 ≤ 9 * x / 8 + y by positivity)]
  have ht2 : t ^ 2 ≤ x ^ 2 / 64 := by
    have h := abs_le.mp ht
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ x / 8 + t by linarith [h.1])]
  have hxy2 := mul_le_mul_of_nonneg_right hxy hx.le
  nlinarith

/-- Any zero of a primitive real character in a uniform logarithmic box
around 1 is real. This leaves open the existence and distance of an exceptional real zero. -/
theorem exists_primitive_real_zero_box_im_eq_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ,
      1 - c / Real.log ((q : ℝ) * 2) < s.re →
      |s.im| ≤ c / Real.log ((q : ℝ) * 2) →
      DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  obtain ⟨δp, Cp, hδp, hCp, hprincipal⟩ := exists_principal_complex_logDeriv_pole_bound
  let δ := min δz δp
  have hδ : 0 < δ := lt_min hδz hδp
  let B : ℝ := Cz + Cp + 60001
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
  intro q inst χ hq hχ hsq s hs ht hzero
  by_contra htne
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - s.re
  let D : ℝ := (3 * Cz + Cp + Real.log q) / 4
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < s.re at hs
  change |s.im| ≤ (a / 8) / L at ht
  rw [hquot] at hs ht
  have hβ : s.re ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δz := by dsimp [σ]; linarith [min_le_left δz δp]
  have hσδp : ‖(σ : ℂ) - 1‖ < δp := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < σ - 1)]
    dsimp [σ]
    linarith [min_le_right δz δp]
  have hpair := primitive_real_LFunction_logDeriv_re_ge_zero_pair hq hχ hsq σ s.re s.im
    hσ hσ' (by linarith) (by linarith) htne
    (by rw [Complex.re_add_im]; exact hzero)
  have hu := real_character_logDeriv_real_axis_le χ hsq σ Cz Cp hσ
    (hzeta σ hσ hσδ) (hprincipal q (σ : ℂ) (by simpa using hσ) hσδp)
  have hlogq : Real.log q ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hD : D + 60000 * L ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : (D + 60000 * L) * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hxy : x ≤ y := by dsimp [y, σ]; linarith
  have hyx : y ≤ 9 * x / 8 := by dsimp [y, σ]; linarith
  have hi : 2 * y / (y ^ 2 + s.im ^ 2) ≤ 1 / x + (D + 60000 * L) := by
    have he : σ - 1 = x := by dsimp [σ]; ring
    rw [he] at hu
    change 2 * y / (y ^ 2 + s.im ^ 2) - 60000 * L ≤ _ at hpair
    dsimp [D]
    linarith
  exact conjugate_pair_gap_contradiction hx hxy hyx ht hDx hi

end Chen
