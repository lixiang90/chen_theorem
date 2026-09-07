import Submission.ChenTheorem.Lemma6.LFunctionEulerBounds
import Mathlib.Analysis.Complex.JensenFormula

set_option autoImplicit true

open Set Metric

namespace Chen

/-- Jensen's inequality bounds the number of zeros, counted with multiplicity,
in a fixed disk reaching to the left of one. No zero-free-region hypothesis
is used. This supplies the zero count needed for a local factorization. -/
theorem LFunction_zero_count_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ) :
    ((∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (closedBall (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (3 / 8)) u : ℤ) : ℝ) ≤
      Real.log (5 * (6 * Real.sqrt q * Real.log (2 * q) *
        (‖((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ + 1 / 2) + 1)) /
          Real.log (4 / 3) := by
  have hχne : χ ≠ 1 := by
    intro hχone
    have hcond : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  let c : ℂ := ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  let M : ℝ := 2 * B * (‖c‖ + 1 / 2) + 1
  have hc : c.re = 5 / 4 := by simp [c]
  have hlog : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 1 ≤ M := by
    have : 0 ≤ 2 * B * (‖c‖ + 1 / 2) := by positivity
    dsimp [M]
    linarith
  have hMpos : 0 < M := by linarith
  have hanchor : (1 / 5 : ℝ) ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    have h := norm_LFunction_euler_lower χ c (by rw [hc]; norm_num)
    norm_num [hc] at h
    exact h
  have hanchorpos : 0 < ‖DirichletCharacter.LFunction χ c‖ := by linarith
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c |(1 / 2 : ℝ)|) :=
    ((DirichletCharacter.differentiable_LFunction hχne).differentiableOn.analyticOnNhd
      isOpen_univ).mono (subset_univ _)
  have hbound : ∀ z ∈ sphere c |(1 / 2 : ℝ)|, ‖DirichletCharacter.LFunction χ z‖ ≤ M := by
    intro z hz
    have hd : ‖z - c‖ = 1 / 2 := by simpa [mem_sphere, dist_eq_norm] using hz
    have hr := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hc, hd] at hr
    have hrez : 1 / 2 ≤ z.re := by have := (abs_le.mp hr).1; linarith
    have hn : ‖z‖ ≤ ‖c‖ + 1 / 2 := by
      have := norm_le_norm_sub_add z c
      rw [hd] at this
      linarith
    have hg := norm_LFunction_le_of_re_pos hχ hq (show 0 < z.re by linarith)
    change ‖DirichletCharacter.LFunction χ z‖ ≤ B * ‖z‖ / z.re at hg
    apply hg.trans
    apply (div_le_iff₀ (by linarith : 0 < z.re)).mpr
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hn hB.le,
      mul_le_mul_of_nonneg_left hrez (mul_nonneg hB.le (show 0 ≤ ‖c‖ + 1 / 2 by positivity))]
  have hj := hf.sum_divisor_le (r := (3 / 8 : ℝ)) (R := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) hM (norm_pos_iff.mp hanchorpos) hbound
  rw [show |(3 / 8 : ℝ)| = 3 / 8 by norm_num,
    show (1 / 2 : ℝ) / (3 / 8) = 4 / 3 by norm_num] at hj
  have hratio : M / ‖DirichletCharacter.LFunction χ c‖ ≤ 5 * M := by
    apply (div_le_iff₀ hanchorpos).mpr
    nlinarith
  have hlogs := Real.log_le_log (div_pos hMpos hanchorpos) hratio
  have hden : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have ht := hj.trans (div_le_div_of_nonneg_right hlogs hden.le)
  simpa [M, B, c,
    show (2 : ℝ) * (3 * Real.sqrt q * Real.log (2 * q)) =
    6 * Real.sqrt q * Real.log (2 * q) by ring] using ht

end Chen
