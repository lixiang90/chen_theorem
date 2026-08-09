import ChenTheorem.Lemma6.Mollifier

/-!
# The square of Chen's truncated Möbius polynomial

These are the coefficients `j(n)` in equation (15), where
`S(H,s,χ)^2 = ∑ j(n)χ(n)n⁻ˢ`.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The coefficient of `a(n)` in the square of the truncated Möbius
polynomial. -/
noncomputable def lemma6MollifierSquareCoeff (H n : ℕ) : ℤ :=
  ∑ p ∈ n.divisorsAntidiagonal,
    if p.1 ≤ H ∧ p.2 ≤ H then
      ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2
    else 0

/-- The square coefficient has support in `n ≤ H²`. -/
theorem lemma6MollifierSquareCoeff_eq_zero_of_sq_lt
    {H n : ℕ} (h : H * H < n) :
    lemma6MollifierSquareCoeff H n = 0 := by
  unfold lemma6MollifierSquareCoeff
  apply Finset.sum_eq_zero
  intro p hp
  rw [if_neg]
  intro hboth
  have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
  have hmul : p.1 * p.2 ≤ H * H :=
    Nat.mul_le_mul hboth.1 hboth.2
  omega

/-- The paper's coefficient estimate `|j(n)| ≤ τ(n)`. -/
theorem abs_lemma6MollifierSquareCoeff_le_card (H n : ℕ) :
    |lemma6MollifierSquareCoeff H n| ≤
      (n.divisorsAntidiagonal.card : ℤ) := by
  let f : ℕ × ℕ → ℤ := fun p =>
    if p.1 ≤ H ∧ p.2 ≤ H then
      ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2
    else 0
  calc
    |lemma6MollifierSquareCoeff H n| =
        |∑ p ∈ n.divisorsAntidiagonal, f p| := by
      rfl
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, |f p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [f]
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul ArithmeticFunction.abs_moebius_le_one
          ArithmeticFunction.abs_moebius_le_one (abs_nonneg _) (by norm_num)
      · simp
    _ = (n.divisorsAntidiagonal.card : ℤ) := by simp

/-- Fibre form of the square coefficient. -/
theorem lemma6MollifierSquareCoeff_eq_fiber (H n : ℕ) :
    lemma6MollifierSquareCoeff H n =
      ∑ p ∈ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
          (fun p => p.1 * p.2 = n),
        ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 := by
  unfold lemma6MollifierSquareCoeff
  rw [← Finset.sum_filter]
  rw [← lemma6MollifierFiber_eq]

/-- Exact finite form of `S(H,a)^2 = ∑_{n≤H²} j_H(n)a(n)`. -/
theorem lemma6_mollifierPolynomial_sq
    {R : Type*} [CommRing R] (H : ℕ) (a : ℕ → R)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → a (m * n) = a m * a n) :
    lemma6MollifierPolynomial H a ^ 2 =
      ∑ n ∈ Finset.Icc 1 (H * H),
        (lemma6MollifierSquareCoeff H n : R) * a n := by
  let S := Finset.Icc 1 H
  let P := S ×ˢ S
  let N := Finset.Icc 1 (H * H)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ N := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P N
    (fun p : ℕ × ℕ => p.1 * p.2)
    (fun p => ((ArithmeticFunction.moebius p.1 : ℤ) : R) *
      (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2))
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  unfold lemma6MollifierPolynomial
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    (∑ p ∈ P,
        ((ArithmeticFunction.moebius p.1 : R) * a p.1) *
          ((ArithmeticFunction.moebius p.2 : R) * a p.2)) =
      ∑ p ∈ P,
        (ArithmeticFunction.moebius p.1 : R) *
          (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := Finset.mem_product.mp hp
      have hp1 := (Finset.mem_Icc.mp hpmem.1).1
      have hp2 := (Finset.mem_Icc.mp hpmem.2).1
      rw [hmul p.1 p.2 hp1 hp2]
      ring
    _ = ∑ n ∈ N,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.1 : R) *
            (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) :=
      hfiber.symm
    _ = ∑ n ∈ N,
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.1 : R) *
            (ArithmeticFunction.moebius p.2 : R)) * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ n ∈ N,
        (lemma6MollifierSquareCoeff H n : R) * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [lemma6MollifierSquareCoeff_eq_fiber]
      push_cast
      rfl

end Chen
