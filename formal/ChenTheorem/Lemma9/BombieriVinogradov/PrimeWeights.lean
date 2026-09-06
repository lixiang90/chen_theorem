import ChenTheorem.Lemma9.BombieriVinogradov.Basic
import Mathlib.NumberTheory.Chebyshev

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-- The theta sum over primes in one arithmetic progression. -/
noncomputable def progressionTheta (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n.Prime ∧ n ≡ a [MOD q] then Real.log n else 0

theorem progressionTheta_nonneg (x q a : ℕ) : 0 ≤ progressionTheta x q a := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.1.one_le)
  · exact le_rfl

theorem progressionTheta_le_psi (x q a : ℕ) :
    progressionTheta x q a ≤ progressionPsi x q a := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp, true_and, ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact le_rfl
  · simp only [hp, false_and, if_false]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

/-- The contribution of higher prime powers in a progression is bounded
by their contribution in the whole interval. -/
theorem progressionPsi_sub_theta_le (x q a : ℕ) :
    progressionPsi x q a - progressionTheta x q a ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hglobal : Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 1 x, if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
    congr 1
  rw [hglobal, progressionPsi, progressionTheta, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp only [hp, not_false_eq_true, if_true, false_and, if_false, sub_zero]
    split_ifs
    · exact le_rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg

theorem abs_progressionTheta_sub_psi_le {x : ℕ} (hx : 1 ≤ x) (q a : ℕ) :
    |progressionTheta x q a - progressionPsi x q a| ≤
      2 * Real.sqrt x * Real.log x := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (progressionTheta_le_psi x q a))]
  exact (progressionPsi_sub_theta_le x q a).trans
    (Chebyshev.psi_sub_theta_le (by exact_mod_cast hx))

theorem progressionPsi_mod (x q a : ℕ) :
    progressionPsi x q (a % q) = progressionPsi x q a := by
  simp only [progressionPsi, Nat.ModEq, Nat.mod_mod]
  rfl

/-- The existing maximum controls any reduced residue representative. -/
theorem progressionError_le_max_of_coprime {x q a : ℕ}
    (hq : q ≠ 0) (ha : a.Coprime q) :
    progressionError x q a ≤ maxProgressionError x q := by
  have hm : (a % q).Coprime q := by simpa using ha
  have h := progressionError_le_maxProgressionError (x := x)
    hq (Nat.mod_lt a (Nat.pos_of_ne_zero hq)) hm
  simpa only [progressionError, progressionPsi_mod] using h

/-- Pointwise theta progression error, with a uniform prime-power loss. -/
theorem abs_progressionTheta_sub_main_le {x q a : ℕ}
    (hx : 1 ≤ x) (hq : q ≠ 0) (ha : a.Coprime q) :
    |progressionTheta x q a - (x : ℝ) / Nat.totient q| ≤
      maxProgressionError x q + 2 * Real.sqrt x * Real.log x := by
  calc
    _ ≤ |progressionTheta x q a - progressionPsi x q a| +
        |progressionPsi x q a - (x : ℝ) / Nat.totient q| := abs_sub_le _ _ _
    _ ≤ (2 * Real.sqrt x * Real.log x) + maxProgressionError x q :=
      add_le_add (abs_progressionTheta_sub_psi_le hx q a)
        (progressionError_le_max_of_coprime hq ha)
    _ = _ := add_comm _ _

/-- Uniform finite sum of theta errors for any choice of reduced residues. -/
theorem sum_theta_errors_le {x : ℕ} (hx : 1 ≤ x) (Q : ℕ) (a : ℕ → ℕ)
    (ha : ∀ q ∈ Finset.Icc 1 Q, (a q).Coprime q) :
    (∑ q ∈ Finset.Icc 1 Q,
      |progressionTheta x q (a q) - (x : ℝ) / Nat.totient q|) ≤
      (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) +
        Q * (2 * Real.sqrt x * Real.log x) := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        (maxProgressionError x q + 2 * Real.sqrt x * Real.log x) := by
      apply Finset.sum_le_sum
      intro q hq
      exact abs_progressionTheta_sub_main_le hx
        (by have := (Finset.mem_Icc.mp hq).1; omega) (ha q hq)
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Bombieri--Vinogradov for prime logarithmic weights, uniformly in the
choice of a reduced residue for each modulus. -/
def ThetaStatement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B →
        ∀ a : ℕ → ℕ, (∀ q ∈ Finset.Icc 1 Q, (a q).Coprime q) →
          (∑ q ∈ Finset.Icc 1 Q,
            |progressionTheta x q (a q) - (x : ℝ) / Nat.totient q|) ≤
            C * x / (Real.log x) ^ A

/-- Removing higher prime powers costs only one additional logarithmic
power in the level of distribution. -/
theorem thetaStatement_of_statement (hBV : Statement) : ThetaStatement := by
  intro A hA
  obtain ⟨B₀, C₀, hB₀, hC₀, hBV⟩ := hBV A hA
  refine ⟨B₀ + A + 2, C₀ + 2, by linarith, by linarith, ?_⟩
  filter_upwards [hBV, eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)] with x hBV hx hlog
  intro Q hQ a ha
  change 1 ≤ Real.log (x : ℝ) at hlog
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hQ₀ : (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B₀ :=
    hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) 
      (Real.rpow_pos_of_pos hlogpos _) 
      (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)))
  have hQ₁ : (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ (A + 1) :=
    hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) 
      (Real.rpow_pos_of_pos hlogpos _) 
      (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)))
  have hpow : (Real.log (x : ℝ)) ^ (A + 1) =
      (Real.log x) ^ A * Real.log x := by
    rw [Real.rpow_add hlogpos, Real.rpow_one]
  have hprimepower : (Q : ℝ) * (2 * Real.sqrt x * Real.log x) ≤
      2 * x / (Real.log x) ^ A := by
    calc
      _ ≤ (Real.sqrt x / (Real.log x) ^ (A + 1)) *
          (2 * Real.sqrt x * Real.log x) :=
        mul_le_mul_of_nonneg_right hQ₁
          (by positivity)
      _ = _ := by
        rw [hpow]
        have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity)
        have hpowne := ne_of_gt (Real.rpow_pos_of_pos hlogpos A)
        field_simp
        nlinarith
  calc
    _ ≤ (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) +
        Q * (2 * Real.sqrt x * Real.log x) := sum_theta_errors_le hx Q a ha
    _ ≤ C₀ * x / (Real.log x) ^ A + 2 * x / (Real.log x) ^ A :=
      add_le_add (hBV Q hQ₀) hprimepower
    _ = _ := by ring

/-- Error in a reduced class, and zero for a class to which the prime
distribution theorem does not apply. -/
noncomputable def reducedThetaError (x q a : ℕ) : ℝ :=
  if a.Coprime q then
    |progressionTheta x q a - (x : ℝ) / Nat.totient q| else 0

theorem reducedThetaError_nonneg (x q a : ℕ) : 0 ≤ reducedThetaError x q a := by
  unfold reducedThetaError
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

/-- A convenient form allowing arbitrary representatives: non-reduced
classes are simply omitted. The representatives may depend on `x`. -/
theorem thetaStatement_reduced_errors (hTheta : ThetaStatement)
    (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B →
        ∀ a : ℕ → ℕ,
          (∑ q ∈ Finset.Icc 1 Q, reducedThetaError x q (a q)) ≤
            C * x / (Real.log x) ^ A := by
  obtain ⟨B, C, hB, hC, hTheta⟩ := hTheta A hA
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [hTheta] with x hx
  intro Q hQ a
  let b : ℕ → ℕ := fun q => if (a q).Coprime q then a q else 1
  have hb : ∀ q ∈ Finset.Icc 1 Q, (b q).Coprime q := by
    intro q _
    dsimp [b]
    split_ifs with h
    · exact h
    · exact Nat.coprime_one_left _
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        |progressionTheta x q (b q) - (x : ℝ) / Nat.totient q| := by
      apply Finset.sum_le_sum
      intro q _
      dsimp only [reducedThetaError, b]
      split_ifs <;> first | exact le_rfl | exact abs_nonneg _
    _ ≤ _ := hx Q hQ b hb

end Chen.BombieriVinogradov
