import Submission.ChenTheorem.Lemma6.NonprincipalLogDerivativeBound
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit true

open Set Filter Complex ComplexConjugate
open scoped Topology

namespace Chen

theorem conj_character_apply_of_square_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    conj (χ n) = χ n := by
  have hmul : χ * χ = 1 := by simpa only [pow_two] using hsq
  have hinv : χ⁻¹ = χ := by
    calc
      χ⁻¹ = χ⁻¹ * (χ * χ) := by rw [hmul, mul_one]
      _ = χ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have h := MulChar.star_apply' χ (n : ZMod q)
  rw [hinv] at h
  exact h

theorem conj_LSeries_term_of_real_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (s : ℂ) (n : ℕ) :
    conj (LSeries.term (fun m => χ m) s n) =
      LSeries.term (fun m => χ m) (conj s) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      conj_character_apply_of_square_eq_one χ hsq]
    have harg : (n : ℂ).arg ≠ Real.pi := by rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]; exact Real.pi_pos.ne
    have he := Complex.cpow_conj (n : ℂ) s harg
    simpa using congrArg (fun z => χ n / z) he.symm

theorem conj_LFunction_of_real_character_re_gt_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (s : ℂ) (hs : 1 < s.re) :
    conj (DirichletCharacter.LFunction χ s) = DirichletCharacter.LFunction χ (conj s) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hs)]
  change conj (∑' n, LSeries.term (fun m => χ m) s n) =
    ∑' n, LSeries.term (fun m => χ m) (conj s) n
  rw [Complex.conj_tsum]
  exact tsum_congr (conj_LSeries_term_of_real_character χ hsq s)

theorem conj_LFunction_of_nonprincipal_real_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) (s : ℂ) :
    conj (DirichletCharacter.LFunction χ s) = DirichletCharacter.LFunction χ (conj s) := by
  let f := DirichletCharacter.LFunction χ
  have hf : Differentiable ℂ f := DirichletCharacter.differentiable_LFunction hχ
  have hg : Differentiable ℂ (conj ∘ f ∘ conj) := by
    intro z
    simpa using (hf (conj z)).conj_conj
  have he : f =ᶠ[𝓝 (2 : ℂ)] (conj ∘ f ∘ conj) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h := conj_LFunction_of_real_character_re_gt_one χ hsq (conj z) (by simpa using hz)
    simpa [f, Function.comp_apply] using h.symm
  have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) he
  have h := congrFun hall (conj s)
  simpa [f, Function.comp_apply] using h.symm

theorem real_character_conjugate_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ (conj s) = 0 := by
  rw [← conj_LFunction_of_nonprincipal_real_character χ hχ hsq s, hs, map_zero]

end Chen
