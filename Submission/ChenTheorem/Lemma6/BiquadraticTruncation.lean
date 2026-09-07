import Submission.ChenTheorem.Lemma6.BiquadraticTaylorLower
import Submission.ChenTheorem.Analysis.GeometricTruncation

set_option autoImplicit true
namespace Chen

noncomputable def siegelTruncationConstant : ℝ := Real.exp (4 * Real.log 7112448 + 2)

theorem siegelTruncationConstant_pos : 0 < siegelTruncationConstant := Real.exp_pos _

/-- A logarithmic truncation length controls the Taylor tail and the retained power,
uniformly for every real argument between 7/8 and one. -/
theorem exists_biquadratic_truncation (q : ℕ) (hq : 2 ≤ q) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ β : ℝ, 7 / 8 < β → β < 1 →
      (12 * (42 * (q : ℝ) ^ 3) ^ 3) * ((2 / 3 : ℝ) * (2 - β)) ^ k /
        (1 - (2 / 3 : ℝ) * (2 - β)) ≤ 1 / 2 ∧
      (2 - β) ^ k ≤ siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqpow : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ q)
  have hbase : (1 : ℝ) ≤ 42 * (q : ℝ) ^ 3 := by linarith
  have hM : (1 : ℝ) ≤ 12 * (42 * (q : ℝ) ^ 3) ^ 3 := by
    have h := one_le_pow₀ hbase (n := 3)
    linarith
  obtain ⟨k, hk, hkbound, htail⟩ := exists_geometric_truncation hM
  have hlog : Real.log (8 * (12 * (42 * (q : ℝ) ^ 3) ^ 3)) =
      Real.log 7112448 + 9 * Real.log q := by
    rw [show 8 * (12 * (42 * (q : ℝ) ^ 3) ^ 3) = 7112448 * (q : ℝ) ^ 9 by ring,
      Real.log_mul (by norm_num) (pow_ne_zero 9 hq0.ne'), Real.log_pow]
    norm_num
  rw [hlog] at hkbound
  have hD : 0 ≤ 4 * Real.log (7112448 : ℝ) + 2 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7112448)
    linarith
  refine ⟨k, hk, ?_⟩
  intro β hβ hβ'
  refine ⟨htail _ (by linarith) (by linarith), ?_⟩
  have hp := one_add_pow_le_exp_of_nat_le (by linarith : 0 ≤ 1 - β) k hkbound
  have he : (4 * (Real.log 7112448 + 9 * Real.log q) + 2) * (1 - β) ≤
      (4 * Real.log 7112448 + 2) + Real.log q * (36 * (1 - β)) := by
    have h := mul_le_mul_of_nonneg_left (show 1 - β ≤ 1 by linarith) hD
    nlinarith
  calc
    (2 - β) ^ k = (1 + (1 - β)) ^ k := by congr 1; ring
    _ ≤ _ := hp
    _ ≤ Real.exp ((4 * Real.log 7112448 + 2) + Real.log q * (36 * (1 - β))) :=
      Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, ← Real.rpow_def_of_pos hq0]; rfl

theorem biquadraticResidue_lower_of_nonpos {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) (β : ℝ) (hβ : 7 / 8 < β) (hβ' : β < 1)
    (hF : (biquadraticLFunction χ ψ (β : ℂ)).re ≤ 0) :
    (1 - β) / (2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β))) ≤
      (biquadraticResidue χ ψ).re := by
  obtain ⟨k, hk, htailpow⟩ := exists_biquadratic_truncation q hq
  obtain ⟨htail, hpow⟩ := htailpow β hβ hβ'
  have hlower := biquadraticLFunction_taylor_lower_bound χ ψ hχ hψ hχψ hχsq hψsq β hβ hβ' k hk
  have hgap : 0 < 1 - β := by linarith
  have hP : 0 < (2 - β) ^ k := pow_pos (by linarith) k
  have hhalf : (1 / 2 : ℝ) ≤ (biquadraticResidue χ ψ).re * (2 - β) ^ k / (1 - β) := by linarith
  have hprod := (le_div_iff₀ hgap).mp hhalf
  have hρ : 0 < (biquadraticResidue χ ψ).re := by
    by_contra h
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hP.le
    linarith
  have hprod' := mul_le_mul_of_nonneg_left hpow hρ.le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc := siegelTruncationConstant_pos
  apply (div_le_iff₀ (by positivity : 0 < 2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β)))).mpr
  nlinarith

theorem biquadraticResidue_lower_of_real_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) (β : ℝ) (hβ : 7 / 8 < β) (hβ' : β < 1)
    (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (1 - β) / (2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β))) ≤
      (biquadraticResidue χ ψ).re := by
  apply biquadraticResidue_lower_of_nonpos hq χ ψ hχ hψ hχψ hχsq hψsq β hβ hβ'
  simp [biquadraticLFunction, hz]

end Chen
