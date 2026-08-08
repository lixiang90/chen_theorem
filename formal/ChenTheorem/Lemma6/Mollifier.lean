/-
The finite Möbius mollifier coefficients used before equation (14) in the
proof of Lemma 6.

The coefficient below is that of `1 - L_H(s,χ) S(H,s,χ)`, where both
Dirichlet polynomials are truncated at `H`.  These elementary support and
divisor bounds are the algebraic input for the dyadic large sieve.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- Chen's coefficient `C_H(n)`: the delta coefficient minus the truncated
convolution of `1` with Möbius. -/
noncomputable def lemma6MollifierCoeff (H n : ℕ) : ℤ :=
  (if n = 1 then 1 else 0) -
    ∑ p ∈ n.divisorsAntidiagonal,
      if p.1 ≤ H ∧ p.2 ≤ H then ArithmeticFunction.moebius p.2 else 0

@[simp]
theorem lemma6MollifierCoeff_one {H : ℕ} (hH : 1 ≤ H) :
    lemma6MollifierCoeff H 1 = 0 := by
  unfold lemma6MollifierCoeff
  simp [hH]

/-- The truncated convolution has no support beyond `H²`. -/
theorem lemma6MollifierCoeff_eq_zero_of_sq_lt
    {H n : ℕ} (hH : 1 ≤ H) (h : H * H < n) :
    lemma6MollifierCoeff H n = 0 := by
  have hn1 : n ≠ 1 := by
    intro hn
    subst n
    have hHH : 1 ≤ H * H := by
      simpa only [one_mul] using Nat.mul_le_mul hH hH
    omega
  unfold lemma6MollifierCoeff
  rw [if_neg hn1, zero_sub]
  have hsum :
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 ≤ H ∧ p.2 ≤ H then
          ArithmeticFunction.moebius p.2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
    rw [if_neg]
    intro hboth
    have hmul : p.1 * p.2 ≤ H * H :=
      Nat.mul_le_mul hboth.1 hboth.2
    omega
  rw [hsum, neg_zero]

/-- For `n ≤ H`, Möbius inversion makes the coefficient vanish. -/
theorem lemma6MollifierCoeff_eq_zero_of_le
    {H n : ℕ} (hH : 1 ≤ H) (hnpos : 1 ≤ n) (hnH : n ≤ H) :
    lemma6MollifierCoeff H n = 0 := by
  by_cases hn1 : n = 1
  · subst n
    exact lemma6MollifierCoeff_one hH
  have hn0 : n ≠ 0 := by omega
  have hbounds : ∀ p ∈ n.divisorsAntidiagonal,
      p.1 ≤ H ∧ p.2 ≤ H := by
    intro p hp
    have hp1dvd := Nat.dvd_of_mem_divisors
      (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have hp2dvd := Nat.dvd_of_mem_divisors
      (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    exact ⟨(Nat.le_of_dvd (by omega) hp1dvd).trans hnH,
      (Nat.le_of_dvd (by omega) hp2dvd).trans hnH⟩
  have hfiltered :
      (∑ p ∈ n.divisorsAntidiagonal,
        if p.1 ≤ H ∧ p.2 ≤ H then
          ArithmeticFunction.moebius p.2 else 0) =
      ∑ p ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [if_pos (hbounds p hp)]
  have hconv :
      (∑ p ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius p.2) = 0 := by
    have hfun := congrArg (fun f : ArithmeticFunction ℤ => f n)
      (ArithmeticFunction.coe_zeta_mul_moebius :
        ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
          ArithmeticFunction.moebius) = 1)
    rw [ArithmeticFunction.mul_apply] at hfun
    have hfun' :
        (∑ p ∈ n.divisorsAntidiagonal,
          if p.1 = 0 then 0 else ArithmeticFunction.moebius p.2) = 0 := by
      simpa [ArithmeticFunction.zeta_apply, hn0, hn1] using hfun
    calc
      (∑ p ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.moebius p.2) =
        ∑ p ∈ n.divisorsAntidiagonal,
          (if p.1 = 0 then 0 else ArithmeticFunction.moebius p.2) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [if_neg (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)]
      _ = 0 := hfun'
  unfold lemma6MollifierCoeff
  rw [if_neg hn1, hfiltered, hconv, sub_zero]

/-- The paper's elementary `|C_H(n)| ≤ τ(n)` bound, stated using the
equivalent cardinality of the divisor antidiagonal. -/
theorem abs_lemma6MollifierCoeff_le_card
    {H n : ℕ} (hn1 : n ≠ 1) :
    |lemma6MollifierCoeff H n| ≤
      (n.divisorsAntidiagonal.card : ℤ) := by
  let f : ℕ × ℕ → ℤ := fun p =>
    if p.1 ≤ H ∧ p.2 ≤ H then ArithmeticFunction.moebius p.2 else 0
  calc
    |lemma6MollifierCoeff H n| =
        |∑ p ∈ n.divisorsAntidiagonal, f p| := by
      unfold lemma6MollifierCoeff
      rw [if_neg hn1, zero_sub, abs_neg]
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, |f p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [f]
      split_ifs
      · exact ArithmeticFunction.abs_moebius_le_one
      · simp
    _ = (n.divisorsAntidiagonal.card : ℤ) := by simp

end Chen
