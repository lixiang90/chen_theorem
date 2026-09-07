import Submission.ChenTheorem.Lemma6.LFunctionChangeLevelLogDerivative

set_option autoImplicit true
namespace Chen

theorem nonprincipal_LFunction_logDeriv_re_ge {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ t : ℝ)
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    -(60001 * Real.log ((q : ℝ) * (|t| + 2))) ≤
      (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdne : χ.conductor ≠ 1 := by
    intro he
    exact hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)
  have hd : 2 ≤ χ.conductor := by have := χ.conductor_ne_zero; omega
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdq : χ.conductor ≤ q := Nat.le_of_dvd hq χ.conductor_dvd_level
  have hp := primitive_LFunction_logDeriv_re_ge hd χ.primitiveCharacter_isPrimitive σ t hσ hσ'
  have he := norm_logDeriv_LFunction_changeLevel_sub_le χ.conductor_dvd_level
    χ.primitiveCharacter ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  rw [χ.changeLevel_primitiveCharacter] at he
  have her := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  rw [Complex.sub_re] at her
  simp only [logDeriv_apply] at her
  have hdR : (0 : ℝ) < χ.conductor := by exact_mod_cast (by omega : 0 < χ.conductor)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hheight : 0 < |t| + 2 := by positivity
  have hl : Real.log ((χ.conductor : ℝ) * (|t| + 2)) ≤
      Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (mul_pos hdR hheight)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdq) hheight.le
  have hlq : Real.log q ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log hqR
    nlinarith [abs_nonneg t]
  linarith

end Chen
