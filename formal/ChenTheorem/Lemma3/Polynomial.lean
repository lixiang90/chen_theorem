/-
The finite Dirichlet-polynomial part of Chen's Lemma 3.

Squaring the truncation of `L(s, chi)` and grouping by `n = a*b` gives a
polynomial of length `N^2`.  Its coefficient is bounded by the divisor
function, so the character large sieve and the weighted divisor-square
estimate give the fourth-moment bound used in the printed proof.
-/
import ChenTheorem.LargeSieve.Character
import ChenTheorem.Lemma6.Mollifier
import ChenTheorem.Lemma6.DivisorSquareWeighted

open scoped Classical

namespace Chen

/-- The coefficient `n^{-s}` in the ordinary Dirichlet polynomial.
Kept local to Lemma 3 so that Lemma 6 can depend on the completed result
without creating a circular import. -/
noncomputable def lemma3Phase (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ s)⁻¹

theorem lemma3Phase_norm_sq_le
    {s : ℂ} {n : ℕ} (hn : 1 ≤ n) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖lemma3Phase s n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  have hnpos : 0 < n := by omega
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(s.re * 2) ≤ (-1 : ℝ) := by linarith
  rw [lemma3Phase, norm_inv, Complex.norm_natCast_cpow_of_pos hnpos]
  calc
    ((n : ℝ) ^ s.re)⁻¹ ^ 2 = (((n : ℝ) ^ s.re) ^ 2)⁻¹ :=
      inv_pow _ _
    _ = ((n : ℝ) ^ (s.re * 2))⁻¹ := by
      rw [Real.rpow_mul hnnonneg]
      norm_num
    _ = (n : ℝ) ^ (-(s.re * 2)) := by
      rw [Real.rpow_neg hnnonneg]
    _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnone hexp
    _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _

/-- The ordinary finite Dirichlet polynomial used in Lemma 3. -/
noncomputable def lemma3TruncatedL
    {q : ℕ} (N : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, lemma3Phase s n * χ n

/-- Number of factor pairs `a*b=n` with both factors at most `N`. -/
noncomputable def lemma3SquareCoeff (N n : ℕ) : ℕ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun p => p.1 * p.2 = n)).card

theorem lemma3SquareCoeff_le_divisorsAntidiagonal_card (N n : ℕ) :
    lemma3SquareCoeff N n ≤ n.divisorsAntidiagonal.card := by
  unfold lemma3SquareCoeff
  rw [lemma6MollifierFiber_eq]
  exact Finset.card_filter_le _ _

/-- Exact regrouping of the square of the truncated Dirichlet polynomial. -/
theorem lemma3TruncatedL_sq
    {q : ℕ} (N : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma3TruncatedL N s χ ^ 2 =
      ∑ n ∈ Finset.Icc 1 (N * N),
        ((lemma3SquareCoeff N n : ℂ) * lemma3Phase s n) * χ n := by
  let S := Finset.Icc 1 N
  let P := S ×ˢ S
  let T := Finset.Icc 1 (N * N)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ T := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P T
    (fun p : ℕ × ℕ => p.1 * p.2)
    (fun p => lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2))
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  unfold lemma3TruncatedL
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    (∑ p ∈ P,
        (lemma3Phase s p.1 * χ p.1) *
          (lemma3Phase s p.2 * χ p.2)) =
      ∑ p ∈ P,
        lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := Finset.mem_product.mp hp
      have hp1 := (Finset.mem_Icc.mp hpmem.1).1
      have hp2 := (Finset.mem_Icc.mp hpmem.2).1
      have hphase : lemma3Phase s (p.1 * p.2) =
          lemma3Phase s p.1 * lemma3Phase s p.2 := by
        unfold lemma3Phase
        have hpow : ((p.1 * p.2 : ℕ) : ℂ) ^ s =
            (p.1 : ℂ) ^ s * (p.2 : ℂ) ^ s := by
          simpa only [Nat.cast_mul] using
            Complex.natCast_mul_natCast_cpow p.1 p.2 s
        rw [hpow, mul_inv]
      have hchar : χ (p.1 * p.2) = χ p.1 * χ p.2 := by
        rw [map_mul]
      rw [hphase, hchar]
      ring
    _ = ∑ n ∈ T,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2) :=
      hfiber.symm
    _ = ∑ n ∈ T,
        ((lemma3SquareCoeff N n : ℂ) * lemma3Phase s n) * χ n := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
            lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2) =
          ∑ _p ∈ P.filter (fun p => p.1 * p.2 = n),
            lemma3Phase s n * χ n := by
          apply Finset.sum_congr rfl
          intro p hp
          have heq := (Finset.mem_filter.mp hp).2
          have hchar : χ (p.1 * p.2) = χ n := by
            congr 1
            rw [← Nat.cast_mul, heq]
          rw [heq, hchar]
        _ = ((lemma3SquareCoeff N n : ℂ) *
            lemma3Phase s n) * χ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
          unfold lemma3SquareCoeff
          ring

/-- Pointwise square-coefficient estimate at `Re s >= 1/2`. -/
theorem lemma3SquareCoeff_weighted_norm_sq_le
    {N n : ℕ} {s : ℂ} (hn : 1 ≤ n) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖(lemma3SquareCoeff N n : ℂ) * lemma3Phase s n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  have hcoeff : ‖(lemma3SquareCoeff N n : ℂ)‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 := by
    rw [Complex.norm_natCast]
    exact pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast lemma3SquareCoeff_le_divisorsAntidiagonal_card N n) 2
  rw [norm_mul, mul_pow]
  calc
    ‖(lemma3SquareCoeff N n : ℂ)‖ ^ 2 *
        ‖lemma3Phase s n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul hcoeff (lemma3Phase_norm_sq_le hn hs)
          (sq_nonneg _) (by positivity)
    _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      rw [div_eq_mul_inv]

/-- The raw large-sieve estimate for the fourth moment of the truncation. -/
theorem lemma3_truncated_fourth_moment_raw
    (Q N : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
      ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  let a : ℕ → ℂ := fun n =>
    (lemma3SquareCoeff N n : ℂ) * lemma3Phase s n
  have hinterval : Finset.Ioc 0 (N * N) = Finset.Icc 1 (N * N) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsieve := LargeSieve.large_sieve_character Q 0 (N * N) a
  simp only [zero_add, hinterval] at hsieve
  calc
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) =
      ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, a]
        rw [← lemma3TruncatedL_sq]
        rw [norm_pow]
        ring
      · simp [hp]
    _ ≤ ∑ q ∈ Finset.Icc 2 Q, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq2 := (Finset.mem_Icc.mp hq).1
      have htotpos : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      have hweight : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
        (le_div_iff₀ htotpos).2 (by
          simpa using (show (q.totient : ℝ) ≤ q by
            exact_mod_cast Nat.totient_le q))
      have hsum : 0 ≤ ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0 := by
        positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight hsum
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rcases Finset.mem_Icc.mp hq with ⟨hq2, hqQ⟩
        exact Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ q), hqQ⟩
      · intro q hq hnot
        positivity
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N), ‖a n‖ ^ 2 := hsieve
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      gcongr with n hn
      exact lemma3SquareCoeff_weighted_norm_sq_le
        (Finset.mem_Icc.mp hn).1 hs

/-- Logarithmic form of the truncated fourth moment. -/
theorem lemma3_truncated_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q N : ℕ) (s : ℂ), 2 ≤ N →
      (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q,
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
        C * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
          (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by
  rcases lemma6_divisorSquare_over_n_le_log_four with ⟨C₀, hC₀, hdiv⟩
  refine ⟨(1 + Real.pi) * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro Q N s hN hs
  have hNN : 2 ≤ N * N := by nlinarith
  calc
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
      ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) :=
        lemma3_truncated_fourth_moment_raw Q N s hs
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        (C₀ * (Real.log ((N * N : ℕ) : ℝ)) ^ 4) := by
      gcongr
      exact hdiv (N * N) hNN
    _ ≤ (1 + Real.pi) * C₀ *
        ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
          (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by
      have hQ : 0 ≤ (Q : ℝ) ^ 2 := by positivity
      have hNN0 : 0 ≤ ((N * N : ℕ) : ℝ) := by positivity
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      have hbase : (Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ) ≤
          (1 + Real.pi) * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) := by
        nlinarith [mul_nonneg hpi hQ]
      have hfactor : 0 ≤ C₀ *
          (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by positivity
      calc
        ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
            (C₀ * (Real.log ((N * N : ℕ) : ℝ)) ^ 4) ≤
          ((1 + Real.pi) * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ))) *
            (C₀ * (Real.log ((N * N : ℕ) : ℝ)) ^ 4) :=
              mul_le_mul_of_nonneg_right hbase hfactor
        _ = (1 + Real.pi) * C₀ *
            ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
              (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by ring

end Chen
