import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLowerStep

set_option autoImplicit true
open Set

namespace Chen.LinearSieve

/-- One positive initial value works for both alternating auxiliary functions. -/
noncomputable def auxiliaryLowerConstant : ℝ :=
  min (upperAuxiliaryError 3) (lowerAuxiliaryError 3)

theorem auxiliaryLowerConstant_pos : 0 < auxiliaryLowerConstant :=
  lt_min (upperAuxiliaryError_pos 3 (by norm_num)) (lowerAuxiliaryError_pos 3 (by norm_num))

theorem auxiliaryLowerConstant_le_initial (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) :
    auxiliaryLowerConstant ≤ upperAuxiliaryError s ∧
      auxiliaryLowerConstant ≤ lowerAuxiliaryError s := by
  constructor
  · exact (min_le_left _ _).trans
      (antitoneOn_upperAuxiliaryError (by change 1 < s; linarith) (by norm_num) hs3)
  · exact (min_le_right _ _).trans
      (antitoneOn_lowerAuxiliaryError (by change 0 < s; linarith) (by norm_num) hs3)

/-- A quantitative induction with a freely chosen step. All parameters up
to `S` use the same factor `ε / S`; no threshold depends implicitly on depth. -/
theorem auxiliaryError_lower_bound_induction (S ε : ℝ) (hS : 3 ≤ S)
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    ∀ s, 2 < s → s ≤ S → s ≤ 3 + (n : ℝ) * (1 - ε) →
      auxiliaryLowerConstant * (ε / S) ^ n ≤ upperAuxiliaryError s ∧
        auxiliaryLowerConstant * (ε / S) ^ n ≤ lowerAuxiliaryError s := by
  have hS0 : 0 < S := by linarith
  have hq0 : 0 ≤ ε / S := (div_pos hε0 hS0).le
  have hq1 : ε / S ≤ 1 := (div_le_one hS0).2 (by linarith)
  induction n with
  | zero =>
    intro s hs hsS hsn
    simpa using auxiliaryLowerConstant_le_initial s hs (by simpa using hsn)
  | succ n ih =>
    intro s hs hsS hsn
    have hpow : (ε / S) ^ (n + 1) ≤ (ε / S) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hq0 n) hq1
    by_cases hs3 : s ≤ 3
    · have hi := ih s hs hsS (by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith)
      have hm := mul_le_mul_of_nonneg_left hpow auxiliaryLowerConstant_pos.le
      exact ⟨hm.trans hi.1, hm.trans hi.2⟩
    · have hs3' : 3 < s := lt_of_not_ge hs3
      have hu2 : 2 < s + ε - 1 := by linarith
      have huS : s + ε - 1 ≤ S := by linarith
      have hun : s + ε - 1 ≤ 3 + (n : ℝ) * (1 - ε) := by
        push_cast at hsn
        nlinarith
      have hi := ih (s + ε - 1) hu2 huS hun
      have hq : ε / S ≤ ε / s :=
        div_le_div_of_nonneg_left hε0.le (by linarith) hsS
      have hscale : ∀ H : ℝ, auxiliaryLowerConstant * (ε / S) ^ n ≤ H →
          auxiliaryLowerConstant * (ε / S) ^ (n + 1) ≤ (ε / s) * H := by
        intro H hH
        calc
          auxiliaryLowerConstant * (ε / S) ^ (n + 1) =
              (ε / S) * (auxiliaryLowerConstant * (ε / S) ^ n) := by rw [pow_succ]; ring
          _ ≤ (ε / S) * H := mul_le_mul_of_nonneg_left hH hq0
          _ ≤ (ε / s) * H := mul_le_mul_of_nonneg_right hq
            ((mul_nonneg auxiliaryLowerConstant_pos.le (pow_nonneg hq0 n)).trans hH)
      exact ⟨(hscale _ hi.2).trans (upperAuxiliaryError_lower_step s ε hs3'.le hε0.le),
        (hscale _ hi.1).trans (lowerAuxiliaryError_lower_step s ε hs hε0.le)⟩

/-- Explicit positive lower bounds at every large parameter, with a
free short-interval length that can later depend on that parameter. -/
theorem auxiliaryError_lower_bound (s ε : ℝ) (hs : 3 ≤ s)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    auxiliaryLowerConstant * (ε / s) ^ ⌈s / (1 - ε)⌉₊ ≤ upperAuxiliaryError s ∧
      auxiliaryLowerConstant * (ε / s) ^ ⌈s / (1 - ε)⌉₊ ≤ lowerAuxiliaryError s := by
  have hh : 0 < 1 - ε := by linarith
  have hn := Nat.le_ceil (s / (1 - ε))
  have hsn : s ≤ 3 + (⌈s / (1 - ε)⌉₊ : ℝ) * (1 - ε) := by
    have hm := (div_le_iff₀ hh).mp hn
    linarith
  exact auxiliaryError_lower_bound_induction s ε hs hε0 hε1 _ s (by linarith) le_rfl hsn

end Chen.LinearSieve
