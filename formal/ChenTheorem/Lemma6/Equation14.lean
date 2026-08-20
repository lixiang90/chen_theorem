/-
Assembly of equation (14): combine the exact `L`-series truncation with
the dyadic large-sieve estimate for the finite `C_H` polynomial.
-/
import ChenTheorem.Lemma6.RemainderDyadic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

open scoped Classical

namespace Chen

/-- The analytic truncation-error summand left after the primitive
character count cancels the weight `1 / φ(q)`. -/
noncomputable def lemma6Equation14ErrorTerm
    (C : ℝ) (H : ℕ) (s : ℂ) (q : ℕ) : ℝ :=
  2 * ((C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H) ^ 2 *
    (harmonic H : ℝ) ^ 2)

theorem lemma6Equation14ErrorTerm_nonneg
    (C : ℝ) (H : ℕ) (s : ℂ) (q : ℕ) :
    0 ≤ lemma6Equation14ErrorTerm C H s q := by
  unfold lemma6Equation14ErrorTerm
  positivity

theorem lemma6Equation14ErrorTerm_le_at_Q
    {C : ℝ} (hC : 0 ≤ C) {D Q H q : ℕ} {s : ℂ}
    (hH : 1 ≤ H) (hDQ : D ≤ Q) (hq : q ∈ Finset.Ioc D Q) :
    lemma6Equation14ErrorTerm C H s q ≤
      2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
        (harmonic H : ℝ) ^ 2) := by
  have hqQ : q ≤ Q := (Finset.mem_Ioc.mp hq).2
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hsqrt : Real.sqrt q ≤ Real.sqrt Q := Real.sqrt_le_sqrt (by exact_mod_cast hqQ)
  have hlog : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (Q : ℝ)) := by
    by_cases hqzero : q = 0
    · subst q
      have hqD := (Finset.mem_Ioc.mp hq).1
      omega
    · have hqpos : (0 : ℝ) < 2 * q := by
        exact_mod_cast (show 0 < 2 * q by
          exact Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hqzero))
      have hQposNat : 0 < Q := lt_of_lt_of_le (Nat.pos_of_ne_zero hqzero) hqQ
      have hQpos : (0 : ℝ) < 2 * Q := by
        exact_mod_cast (show 0 < 2 * Q by
          exact Nat.mul_pos (by norm_num) hQposNat)
      exact Real.strictMonoOn_log.monotoneOn hqpos hQpos
        (by exact_mod_cast Nat.mul_le_mul_left 2 hqQ)
  have hnum :
      C * ‖s‖ * Real.sqrt q * Real.log (2 * q) ≤
        C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) := by
    have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) := by
      have hqone : 1 ≤ q := by
        have hqD := (Finset.mem_Ioc.mp hq).1
        omega
      exact Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ 2 * q by nlinarith))
    gcongr
  unfold lemma6Equation14ErrorTerm
  have hleft0 : 0 ≤
      C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg _))
        (Real.sqrt_nonneg _)) (Real.log_nonneg (by
          have hqD := (Finset.mem_Ioc.mp hq).1
          exact_mod_cast (show 1 ≤ 2 * q by omega)))
    · positivity
  have hright0 : 0 ≤
      C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg _))
        (Real.sqrt_nonneg _)) (Real.log_nonneg (by
          have hqD := (Finset.mem_Ioc.mp hq).1
          exact_mod_cast (show 1 ≤ 2 * Q by omega)))
    · positivity
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (sq_le_sq₀ hleft0 hright0 |>.2
        (div_le_div_of_nonneg_right hnum (by positivity)))
      (sq_nonneg (harmonic H : ℝ))) (by norm_num)

theorem sum_lemma6Equation14ErrorTerm_le
    {C : ℝ} (hC : 0 ≤ C) {D Q H : ℕ} {s : ℂ}
    (_hD : 1 ≤ D) (hDQ : D ≤ Q) (hH : 1 ≤ H) :
    ∑ q ∈ Finset.Ioc D Q, lemma6Equation14ErrorTerm C H s q ≤
      (Q : ℝ) *
        (2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2)) := by
  calc
    ∑ q ∈ Finset.Ioc D Q, lemma6Equation14ErrorTerm C H s q ≤
        (Finset.Ioc D Q).card •
          (2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
            (harmonic H : ℝ) ^ 2)) :=
      Finset.sum_le_card_nsmul _ _ _
        (fun q hq => lemma6Equation14ErrorTerm_le_at_Q hC hH hDQ hq)
    _ ≤ Q *
        (2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2)) := by
      simp only [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · have : (Finset.Ioc D Q).card ≤ Q := by simp
        exact_mod_cast this
      · positivity

/-- Total primitive-character left side at a fixed modulus, extended by
zero at the formal modulus `q = 0` where `LFunction` is not defined. -/
noncomputable def lemma6Equation14LeftTerm
    (H q : ℕ) (s : ℂ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
      ‖1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ‖ ^ 2 else 0

theorem lemma6Equation14LeftTerm_eq
    {q : ℕ} (hq : q ≠ 0) (H : ℕ) (s : ℂ) :
    lemma6Equation14LeftTerm H q s =
      letI : NeZero q := ⟨hq⟩
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖1 - DirichletCharacter.LFunction χ s *
          lemma6MollifierAt H s χ‖ ^ 2 else 0 := by
  simp [lemma6Equation14LeftTerm, hq]

/-- At most `φ(q)` characters are primitive, so a constant primitive
character sum is cancelled by the outer `1/φ(q)` weight. -/
theorem inv_totient_mul_primitive_const_sum_le
    {q : ℕ} (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A) :
    (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then A else 0) ≤ A := by
  letI : NeZero q := ⟨by omega⟩
  have hsum :
      (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then A else 0) ≤
        ∑ _χ : DirichletCharacter ℂ q, A := by
    apply Finset.sum_le_sum
    intro χ hχ
    split_ifs
    · exact le_rfl
    · exact hA
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have htot : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  calc
    (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then A else 0) ≤
      (q.totient : ℝ)⁻¹ *
        ∑ _χ : DirichletCharacter ℂ q, A := by
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
    _ = (q.totient : ℝ)⁻¹ *
        (Fintype.card (DirichletCharacter ℂ q) : ℝ) * A := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring
    _ = A := by rw [hcard]; field_simp

/-- Equation (14) before the last scalar simplification.  The first term
is the fully assembled dyadic large-sieve bound; the second is precisely
the Pólya--Vinogradov truncation error summed over moduli. -/
theorem lemma6_equation14_of_truncation
    (htrunc : Lemma6LFunctionTruncation) :
    ∃ Cp Ct : ℝ, 0 < Cp ∧ 0 < Ct ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 < s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            lemma6Equation14LeftTerm H q s ≤
          2 * (Cp * (Nat.log 2 H + 1) *
            (2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
          ∑ q ∈ Finset.Ioc D Q,
            lemma6Equation14ErrorTerm Ct H s q := by
  rcases lemma6_mollifier_remainder_large_sieve with
    ⟨Cp, hCp, hpoly⟩
  rcases norm_one_sub_LFunction_mul_mollifierAt_sq_le_of_truncation
      htrunc with ⟨Ct, hCt, hpoint⟩
  refine ⟨Cp, Ct, hCp, hCt, ?_⟩
  intro D Q H s hD hDQ hH hs
  have hpolyBound := hpoly D Q H s hD hDQ hH hs.le
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        lemma6Equation14LeftTerm H q s ≤
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          (2 * ‖lemma6MollifierRemainderPolynomial H
              (lemma6DirichletPhase χ s)‖ ^ 2 +
            lemma6Equation14ErrorTerm Ct H s q) else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqD := (Finset.mem_Ioc.mp hq).1
        have hq0 : q ≠ 0 := by omega
        letI : NeZero q := ⟨hq0⟩
        rw [lemma6Equation14LeftTerm_eq hq0]
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          split_ifs with hp
          · simpa only [lemma6Equation14ErrorTerm] using
              hpoint (by omega : 2 ≤ q) hH hs χ hp
          · exact le_rfl
        · positivity
    _ ≤ 2 * (∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖lemma6MollifierRemainderPolynomial H
              (lemma6DirichletPhase χ s)‖ ^ 2 else 0)) +
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            lemma6Equation14ErrorTerm Ct H s q else 0) := by
      apply le_of_eq
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      have hqD := (Finset.mem_Ioc.mp hq).1
      letI : NeZero q := ⟨by omega⟩
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      conv_rhs =>
        rhs
        rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro χ hχ
      split_ifs <;> ring
    _ ≤ 2 * (Cp * (Nat.log 2 H + 1) *
          (2 * (Q : ℝ) / H +
            (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
          (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
        ∑ q ∈ Finset.Ioc D Q,
          lemma6Equation14ErrorTerm Ct H s q := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hpolyBound (by norm_num)
      · apply Finset.sum_le_sum
        intro q hq
        have hqD := (Finset.mem_Ioc.mp hq).1
        exact inv_totient_mul_primitive_const_sum_le
          (by omega : 1 ≤ q)
          (lemma6Equation14ErrorTerm_nonneg Ct H s q)

/-- Fully scalar equation (14).  This is the exact formal counterpart of
Chen's displayed estimate before replacing harmonic and dyadic logarithms
by powers of `log x`. -/
theorem lemma6_equation14
    (htrunc : Lemma6LFunctionTruncation) :
    ∃ Cp Ct : ℝ, 0 < Cp ∧ 0 < Ct ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 < s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            lemma6Equation14LeftTerm H q s ≤
          2 * (Cp * (Nat.log 2 H + 1) *
            (2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
          (Q : ℝ) *
            (2 * ((Ct * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
              (harmonic H : ℝ) ^ 2)) := by
  rcases lemma6_equation14_of_truncation htrunc with
    ⟨Cp, Ct, hCp, hCt, hbound⟩
  refine ⟨Cp, Ct, hCp, hCt, ?_⟩
  intro D Q H s hD hDQ hH hs
  apply (hbound D Q H s hD hDQ hH hs).trans
  exact add_le_add_right
    (sum_lemma6Equation14ErrorTerm_le (s := s) hCt.le hD hDQ hH) _

end Chen
