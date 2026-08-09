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

/-- The pairs in the truncated product whose product is `n` are exactly the
bounded divisor-antidivisor pairs of `n`.  This is the finite fibre used to
regroup the two truncated Dirichlet polynomials in the proof of Lemma 6. -/
theorem lemma6MollifierFiber_eq (H n : ℕ) :
    ((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
        (fun p => p.1 * p.2 = n)) =
      n.divisorsAntidiagonal.filter
        (fun p => p.1 ≤ H ∧ p.2 ≤ H) := by
  ext p
  constructor
  · intro hp
    have hpdata := Finset.mem_filter.mp hp
    have hpmem := Finset.mem_product.mp hpdata.1
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hpdata.2, ?_⟩,
      hp1.2, hp2.2⟩
    intro hn0
    rw [hn0] at hpdata
    have hp1pos : 0 < p.1 := by omega
    have hp2pos : 0 < p.2 := by omega
    have := Nat.mul_pos hp1pos hp2pos
    omega
  · intro hp
    have hpdata := Finset.mem_filter.mp hp
    have hanti := Nat.mem_divisorsAntidiagonal.mp hpdata.1
    have hp1ne := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hpdata.1
    have hp2ne := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hpdata.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp1ne, hpdata.2.1⟩,
        Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp2ne, hpdata.2.2⟩⟩,
      hanti.1⟩

/-- The mollifier coefficient as a Kronecker delta minus the fibre of the
truncated product. -/
theorem lemma6MollifierCoeff_eq_delta_sub_fiber (H n : ℕ) :
    lemma6MollifierCoeff H n =
      (if n = 1 then 1 else 0) -
        ∑ p ∈ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
            (fun p => p.1 * p.2 = n),
          ArithmeticFunction.moebius p.2 := by
  unfold lemma6MollifierCoeff
  rw [← Finset.sum_filter]
  rw [← lemma6MollifierFiber_eq]

/-- The finite truncation of the Dirichlet series playing the role of
`L(ω, χ)` in the exact algebraic part of equation (14). -/
noncomputable def lemma6TruncatedLPolynomial
    {R : Type*} [AddCommMonoid R] (H : ℕ) (a : ℕ → R) : R :=
  ∑ n ∈ Finset.Icc 1 H, a n

/-- The truncated Möbius polynomial `S(H, ω, χ)` in equation (14). -/
noncomputable def lemma6MollifierPolynomial
    {R : Type*} [Ring R] (H : ℕ) (a : ℕ → R) : R :=
  ∑ n ∈ Finset.Icc 1 H,
    (ArithmeticFunction.moebius n : R) * a n

/-- The finite `C_H`-polynomial on the right-hand side of equation (14). -/
noncomputable def lemma6MollifierRemainderPolynomial
    {R : Type*} [Ring R] (H : ℕ) (a : ℕ → R) : R :=
  ∑ n ∈ Finset.Icc 1 (H * H),
    (lemma6MollifierCoeff H n : R) * a n

/-- Regroup the product of the two truncated Dirichlet polynomials by the
value `n = m * d`. -/
theorem lemma6_truncated_product_eq_sum_fibers
    {R : Type*} [CommRing R] (H : ℕ) (a : ℕ → R)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → a (m * n) = a m * a n) :
    lemma6TruncatedLPolynomial H a * lemma6MollifierPolynomial H a =
      ∑ n ∈ Finset.Icc 1 (H * H),
        (∑ p ∈ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
            (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R)) * a n := by
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
    (fun p => (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2))
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  change (∑ n ∈ S, a n) *
      (∑ n ∈ S, (ArithmeticFunction.moebius n : R) * a n) = _
  calc
    (∑ n ∈ S, a n) *
        (∑ n ∈ S, (ArithmeticFunction.moebius n : R) * a n) =
      ∑ p ∈ P,
        (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := Finset.mem_product.mp hp
      have hp1 := (Finset.mem_Icc.mp hpmem.1).1
      have hp2 := (Finset.mem_Icc.mp hpmem.2).1
      rw [hmul p.1 p.2 hp1 hp2]
      ring
    _ = ∑ n ∈ N,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) :=
      hfiber.symm
    _ = ∑ n ∈ N,
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R)) * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

/-- Exact finite form of the `C_H` identity used before equation (14):
`1 - L_H(a) S_H(a) = ∑_{n ≤ H²} C_H(n) a(n)` for multiplicative `a`
normalised by `a(1) = 1`. -/
theorem lemma6_one_sub_truncated_product_eq_remainder
    {R : Type*} [CommRing R] {H : ℕ} (hH : 1 ≤ H)
    (a : ℕ → R) (ha1 : a 1 = 1)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → a (m * n) = a m * a n) :
    1 - lemma6TruncatedLPolynomial H a * lemma6MollifierPolynomial H a =
      lemma6MollifierRemainderPolynomial H a := by
  let N := Finset.Icc 1 (H * H)
  let P := Finset.Icc 1 H ×ˢ Finset.Icc 1 H
  have h1mem : 1 ∈ N := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact le_rfl
    · nlinarith
  have hdelta :
      ∑ n ∈ N, (if n = 1 then (1 : R) else 0) * a n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [ha1]
    · intro b hb hbne
      simp [hbne]
    · exact fun h => (h h1mem).elim
  rw [lemma6_truncated_product_eq_sum_fibers H a hmul]
  change 1 - (∑ n ∈ N,
      (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
        (ArithmeticFunction.moebius p.2 : R)) * a n) = _
  rw [← hdelta, ← Finset.sum_sub_distrib]
  unfold lemma6MollifierRemainderPolynomial
  change (∑ n ∈ N,
      ((if n = 1 then (1 : R) else 0) * a n -
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R)) * a n)) =
    ∑ n ∈ N, (lemma6MollifierCoeff H n : R) * a n
  apply Finset.sum_congr rfl
  intro n hn
  rw [lemma6MollifierCoeff_eq_delta_sub_fiber]
  push_cast
  ring

/-- Equation (16), separated from the analytic meaning of its three
factors.  Once `L` is nonzero, the logarithmic derivative splits into the
mollified remainder term and the derivative--mollifier term:
`L'/L = (L'/L) * (1 - L*S) + L'*S`. -/
theorem lemma6_logDeriv_mollifier_identity
    {K : Type*} [Field K] (L L' S : K) (hL : L ≠ 0) :
    L' / L = (L' / L) * (1 - L * S) + L' * S := by
  have hcancel : L⁻¹ * L = 1 := inv_mul_cancel₀ hL
  have hmiddle : (L' * L⁻¹) * (L * S) = L' * S := by
    calc
      (L' * L⁻¹) * (L * S) = L' * (L⁻¹ * L) * S := by ring
      _ = L' * S := by rw [hcancel, mul_one]
  rw [div_eq_mul_inv, mul_sub, mul_one, hmiddle, sub_add_cancel]

end Chen
