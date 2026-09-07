import ChenTheorem.Lemma6.ZetaAwayPoleLogDerivative
import ChenTheorem.Lemma6.NonrealZeroFreeRegion

namespace Chen

theorem primitive_real_zero_inequality_away_pole {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (σ β t Cz Cp : ℝ) (hCp : 0 < Cp) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz)
    (hprincipal : -(Cp * Real.log ((q : ℝ) * (|2 * t| + 2))) ≤
      (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) :
    4 / (σ - β) ≤ 3 / (σ - 1) + 3 * Cz +
      (240000 + 2 * Cp) * Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := primitive_LFunction_logDeriv_re_ge_single_zero hq hχ σ β t hσ hσ' hβ hzero
  have h2 := hprincipal
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ t hσ
  rw [hsq] at h3
  simp only [logDeriv_apply] at h2
  have hd := mul_le_mul_of_nonneg_left (conductor_height_log_double_le hq t) hCp.le
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  norm_num at h1 h2 hd ⊢
  simp only [div_eq_mul_inv] at h1 h2 h3 hzeta ⊢
  nlinarith

theorem exists_primitive_real_zero_free_away_axis (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ, ρ ≤ |s.im| →
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨Cp, hCp, hprincipal⟩ := exists_principal_logDeriv_re_ge_away_pole ρ hρ
  obtain ⟨δ, Cz, hδ, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  let B : ℝ := 4 * Cz + 240000 + 2 * Cp
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
  intro q inst χ hq hχ hsq s ht hs hzero
  let L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : 3 / 4 ≤ L := conductor_height_log_ge_threeQuarters q hq s.im
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - s.re
  let D : ℝ := 3 * Cz + (240000 + 2 * Cp) * L
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < s.re at hs
  rw [hquot] at hs
  have hβ : s.re ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have ht2 : ρ ≤ |2 * s.im| := by rw [abs_mul]; norm_num; linarith
  have hp := hprincipal q hq σ (2 * s.im) hσ hσ' ht2
  have hz : DirichletCharacter.LFunction χ ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
    rw [Complex.re_add_im]; exact hzero
  have hi := primitive_real_zero_inequality_away_pole hq hχ hsq σ s.re s.im Cz Cp
    hCp hσ hσ' (by linarith) hz (hzeta σ hσ hσδ) hp
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hσx : σ - 1 = x := by dsimp [σ]; ring
  rw [hσx] at hi
  have hi' : 4 / y ≤ 3 / x + D := by dsimp [y, D]; linarith
  exact four_div_gap_contradiction hx (by dsimp [y]; linarith)
    (by dsimp [y, σ]; linarith) hDx hi'

end Chen
